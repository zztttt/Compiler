#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"
#include "escape.h"
#include "printtree.h"


#define SEMENT_DEBUG 0

#define log(...)\
	if(SEMENT_DEBUG)\
		EM_error(__VA_ARGS__);

struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}


/*environment*/
S_table venv;
S_table tenv;
int recursive;

/*helper functions in lab4*/

Ty_ty actual_ty(Ty_ty t){
	while (t && t->kind == Ty_name) {
		t = t->u.name.ty;
	}
	return t;
}



Ty_fieldList makeFields(S_table tenv, A_fieldList record){
	A_field f = record->head;
	S_symbol name = f->name;
	S_symbol typ = f->typ;

	Ty_ty ty = S_look(tenv, typ);
	Ty_field field;
	if(ty && (ty->kind == Ty_string || ty->kind == Ty_int)){
		field = Ty_Field(name, ty);			
	}
	else if(recursive == 1){
		field = Ty_Field(name, NULL);
	}
	else if(ty && ty->kind == Ty_name){
		field = Ty_Field(name, ty);
	}
	else{
		EM_error(f->pos, "undefined type %s", S_name(f->typ));
		return NULL;
	}

	if(record->tail){	
		return Ty_FieldList(field, makeFields(tenv, record->tail));
	}
	else{
		return Ty_FieldList(field, NULL);
	}				
}

/* core functions */
F_fragList SEM_transProg(A_exp e){
	//TODO LAB5: do not forget to add the main frame
	venv = E_base_venv();
	tenv = E_base_tenv();
	recursive = 0;

	Temp_label prog = Temp_newlabel();
	Tr_level l = Tr_outermost();

	struct expty body = transExp(venv, tenv, e, l, prog);
	
	//Tr_print(body.exp);

	Tr_procEntryExit(l, body.exp, NULL);
	
	return Tr_getResult(); 
}


Ty_ty		 transTy (              S_table tenv, A_ty a){
	switch(a->kind){
		case A_nameTy: {
			log(a->pos, "A_nameTy");
			Ty_ty type = S_look(tenv, a->u.name);
			if (!type) {
				EM_error(a->pos, "undefined type %s", S_name(a->u.name));
				return Ty_Int();
			}
			type = Ty_Name(a->u.name, type);
			return type;
		}
		case A_recordTy:{
			log(a->pos, "A_recordTy");
			A_fieldList record = a->u.record;
			Ty_fieldList fields = makeFieldList(tenv, a->u.record);
			Ty_ty res = Ty_Int();
			if(fields)
				res =  Ty_Record(fields);
			return res;
		}
		case A_arrayTy: {
			log(a->pos, "A_arrayTy");
			Ty_ty type = S_look(tenv, a->u.array);
			if (!type) {
				EM_error(a->pos, "undefined type %s", S_name(a->u.array));
				return Ty_Int();
			}
			return Ty_Array(type);
		}
	}
	assert(0);
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level l, Temp_label label){
	switch(d->kind){
		case A_typeDec:{
			log(d->pos, "A_typeDec");
			S_table name_table = S_empty();
            A_nametyList types = d->u.type;
            while (types) {
                if (S_look(name_table, types->head->name) != NULL) {
                    EM_error(d->pos, "two types with the same name %s in batch declaration\n",
                             S_name(types->head->name));
                }
                S_enter(name_table, types->head->name, (void *) 1);
                types = types->tail;
            }

			types = d->u.type;
			//oops! why put type into new table?
			while (types) {
				//printf("type: %s header\n", S_name(types->head->name));
				
				S_enter(tenv, types->head->name, Ty_Name(types->head->name, NULL));
				types = types->tail;
			}
			//printf("begin resolve reference\n");
			// resolve references
			types = d->u.type;
			while (types) {
				//printf("dealing %s body\n", S_name(types->head->name));
				Ty_ty type;
				if( (type = S_look(tenv, types->head->name)) == NULL){
					EM_error(d->pos, "type not exist");
					return Tr_nilExp();
				}
				//printf("1111\n");
				type->u.name.ty = transTy(tenv, types->head->ty);
				types = types->tail;
			}
			// cycle detection
			//printf("begin cycle detection\n");
			types = d->u.type;
			while (types) {
				Ty_ty init = S_look(tenv, types->head->name);
				Ty_ty type = init;
				while((type = type->u.name.ty)->kind == Ty_name) {
					//printf("checking name type %s\n", S_name(ftype->u.name.sym));
					if (type == init) {
						EM_error(d->pos, "illegal type cycle");
						init->u.name.ty = Ty_Int();
						break;
					}
				}
				types = types->tail;
			}
			return Tr_nilExp();
		}
		case A_varDec:{
			log(d->pos, "A-varDec\n");
			if(!d->u.var.typ){
				log(d->pos, "A_varDec: sym:%s notype", S_name(d->u.var.var));
			}
			else{
				log(d->pos,"A_varDec: sym:%s type:%s", S_name(d->u.var.var), S_name(d->u.var.typ));
			}
			struct expty init = transExp(venv, tenv, d->u.var.init, l, label);
			//printf("finish init\n");
			if (d->u.var.typ) {
				Ty_ty type = S_look(tenv, d->u.var.typ);//found in table
				if (!type) {
					EM_error(d->u.var.init->pos, "type not exist %s", S_name(d->u.var.typ));
				}
				//check whether they are matching
				Ty_ty expected = actual_ty(type);//ecpected
				Ty_ty actual = actual_ty(init.ty);//actual
				if (expected != actual && !(expected->kind == Ty_record && actual->kind == Ty_nil)) {
					EM_error(d->u.var.init->pos, "111type mismatch");
					//oops!!! ty->kind != initty->kind && initty->kind != Ty_nil
					if(expected->kind != actual->kind){
						//printf("%u != %u\n", ty->kind, initty->kind);
						//EM_error(d->u.var.init->pos, "type mismatch");
					}
					else{
						//EM_error(d->u.var.init->pos, "xxx=Ty_nil");
					}
					//printf("%s :%s\n", S_name(type->u.name.sym), S_name(init.ty->u.name.sym));
					
				}
			} else if (actual_ty(init.ty)->kind == Ty_nil) {
				EM_error(d->u.var.init->pos, "init should not be nil without type specified");
			}

			Tr_access access = Tr_allocLocal(l, d->u.var.escape);
			S_enter(venv, d->u.var.var, E_VarEntry(access, init.ty));	
			Tr_exp tr_exp = Tr_simpleVar(access, l);		
			return Tr_assignExp(tr_exp, init.exp);
		}		
		case A_functionDec:{
			log(d->pos, "A_functionDec");
			A_fundecList funcs = d->u.function;
			while(funcs){
				A_fundec func = funcs->head;

				S_symbol name = func->name;
				A_fieldList params = func->params; 
		 		S_symbol result = func->result; 
				A_exp body = func->body;
				
				Temp_label fname = name;
				Tr_level newl = Tr_newLevel(l, fname, makeFormalEscapeList(params));
				Ty_tyList formals = makeFormalTyList(tenv, params);
				
				Ty_ty resultTy;
				if(result){
					resultTy = S_look(tenv, result);
				}
				else{
					resultTy = Ty_Void();
				}
				E_enventry fe = E_FunEntry(newl, fname, formals, resultTy);
				S_enter(venv, name, fe);
				funcs = funcs->tail;
			}

			funcs = d->u.function;
			for(; funcs; funcs=funcs->tail){
				A_fundec func = funcs->head;

				S_symbol name = func->name;
				A_fieldList params = func->params; 
		 		S_symbol result = func->result; 
				A_exp body = func->body;

				//printf("func %s\n",S_name(name));	
				E_enventry f = S_look(venv, name);		
				Temp_label fname = f->u.fun.label;
				Tr_level newl = f->u.fun.level;				
				Ty_tyList formals = makeFormalTyList(tenv, params);

				Ty_ty resultTy;
				if(result){
					resultTy = S_look(tenv, result);
				}
				else{
					resultTy = Ty_Void();
				}
				E_enventry fe = E_FunEntry(newl, fname, formals, resultTy);
				S_enter(venv, name, fe);
				
				S_beginScope(venv);
				Tr_accessList accs = Tr_formals(newl);
				//put formals into env
				accs = accs->tail;
				while(params){
					S_symbol name = params->head->name;
					S_symbol type = params->head->typ;
					E_enventry e = E_VarEntry(accs->head, S_look(tenv, type));
					S_enter(venv, name, e);
					params = params->tail;
					accs = accs->tail;
				}
				struct expty resultty = transExp(venv, tenv, body, newl, fname);
				
				S_endScope(venv);
				Tr_procEntryExit(newl, resultty.exp, Tr_formals(newl));
			}			
			return Tr_typeDec();
		}
		default:{
			EM_error(d->pos, "strange Dec type %d", d->kind);
			return Tr_typeDec();
		}
	}
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level l, Temp_label label){
	switch(v->kind){
		case A_simpleVar:{
			//sample: arr
			log(v->pos, "A_simpleVar: %s", S_name(v->u.simple));
			E_enventry var_entry = S_look(venv, v->u.simple);
			assert(var_entry);
			if (!var_entry || var_entry->kind != E_varEntry) {
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
				return expTy(Tr_nilExp(), Ty_Int());
			}

			Tr_access tr_access = var_entry->u.var.access;
			Tr_exp tr_exp = Tr_simpleVar(tr_access, l);
			
			return expTy(tr_exp, actual_ty(var_entry->u.var.ty));
		}
		case A_fieldVar:{
			log(v->pos, "A_fieldVar: %s", S_name(v->u.field.sym));
			//sample: arr.field
			A_var var = v->u.field.var;
			S_symbol sym = v->u.field.sym;

			struct expty lvalue = transVar(venv, tenv, var, l, label);
			Ty_ty ty = actual_ty(lvalue.ty);

			//check lvalue (sample: arr)
			if (lvalue.ty->kind != Ty_record) {
				EM_error(v->pos, "not a record type");
				return expTy(Tr_nilExp(), Ty_Int());
			}
			//check field and declare the order
			int order = 0;
			Ty_fieldList fields = lvalue.ty->u.record;

			while (fields && fields->head->name != sym) {
				fields = fields->tail;
				order++;
			}
			//don't find the match sym
			if (fields == NULL) {
				EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
				return expTy(Tr_nilExp(), Ty_Int());
			}
			//differ!
			Tr_exp tr_exp = Tr_fieldVar(lvalue.exp, order);
			return expTy(tr_exp, actual_ty(fields->head->ty));
		}
		case A_subscriptVar:{
			//sample: var[exp]
			log(v->pos, "A_subscriptVar");
			A_var typ = v->u.subscript.var;
			A_exp exp = v->u.subscript.exp;
			struct expty lvalue = transVar(venv, tenv, typ, l, label);
			struct expty index = transExp(venv, tenv, exp, l, label);

			//check lvalue
			if (lvalue.ty->kind != Ty_array) {
				EM_error(v->pos, "array type required");
				return expTy(Tr_nilExp(), Ty_Int());
			}

			//check index
			if (index.ty->kind != Ty_int) {
				EM_error(v->pos, "index type is not int");
				return expTy(Tr_nilExp(), Ty_Int());
			}
			Tr_exp tr_exp = Tr_subscriptVar(lvalue.exp, index.exp);
			Ty_ty ty_array = lvalue.ty->u.array;
			return expTy(tr_exp, actual_ty(ty_array));

		}
		default:{
			EM_error(v->pos, "strange variable type %d", v->kind);
			return expTy(Tr_err(), Ty_Int());
		}
	}
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level l, Temp_label label){
	assert(venv && tenv && a);
	switch(a->kind){
		case A_varExp: {
			log(a->pos, "A_varExp");
			return transVar(venv, tenv, a->u.var, l, label);
		}
		case A_nilExp: {
			log(a->pos, "A_nilExp");
			return expTy(Tr_nilExp(), Ty_Nil());
		}
		case A_intExp: {
			log(a->pos, "A_intExp: intt:%d", a->u.intt);
			return expTy(Tr_intExp(a->u.intt), Ty_Int());
		}
		case A_stringExp: {
			log(a->pos, "A_stringExp: stringg: %s", a->u.stringg);
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());
		}
		case A_callExp:{
			log(a->pos, "A_callExp: %s", S_name(a->u.call.func));
			S_symbol func = a->u.call.func;
			E_enventry func_entry = S_look(venv, func);
			if (!func_entry || func_entry->kind != E_funEntry) {
				EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
				return expTy(Tr_nilExp(), Ty_Int());
			}

			Ty_tyList expected = func_entry->u.fun.formals;
			A_expList actual = a->u.call.args;
			Tr_expList ls = NULL;

			while(actual && expected){
				struct expty arg_ty = transExp(venv, tenv, actual->head, l, label);
				if (actual_ty(arg_ty.ty)->kind != actual_ty(expected->head)->kind) {
					EM_error(actual->head->pos, "para type mismatch");
				}
				actual = actual->tail;
				expected = expected->tail;
				//append to para list
				ls = Tr_ExpList(arg_ty.exp, ls);
			}
			if (expected != NULL || actual != NULL) {
				EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
			}
			
			//Tr_exp Tr_callExp(Temp_label fname, Tr_expList params, Tr_level fl, Tr_level envl, string func)
			Tr_level func_level = func_entry->u.fun.level;
			Temp_label func_label = func_entry->u.fun.label;
			Ty_ty func_result = func_entry->u.fun.result;

			Tr_exp tr_exp = Tr_callExp(func_label, ls, func_level, l, S_name(func));
			
			return expTy(tr_exp, actual_ty(func_result));
		}
	    case A_opExp:{
			log(a->pos, "A_opExp: %d", a->u.op.oper);
			A_oper oper = a->u.op.oper;
			struct expty left = transExp(venv, tenv, a->u.op.left, l, label);
			struct expty right = transExp(venv, tenv, a->u.op.right, l, label);

			Tr_exp tr_exp;
			if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp ){
				if(actual_ty(left.ty)->kind != Ty_int ){
					EM_error(a->u.op.left->pos, "integer required");
					return expTy(Tr_nilExp(), Ty_Int());
				}
				if(actual_ty(right.ty)->kind != Ty_int ){
					EM_error(a->u.op.right->pos, "integer required");
					return expTy(Tr_nilExp(), Ty_Int());
				}

				tr_exp = Tr_arithExp(oper,left.exp,right.exp);
			}
			else{
				Ty_ty left_ty = actual_ty(left.ty);
                Ty_ty right_ty = actual_ty(right.ty);

				//need the same type
				if (left_ty != right_ty && 
					!(left_ty->kind == Ty_record && right_ty->kind == Ty_nil)) {
					EM_error(a->u.op.left->pos, "same type required");
				}
				
				if(actual_ty(left.ty)->kind == Ty_record){
					tr_exp = Tr_ptrCompExp(oper,left.exp,right.exp);
				}
				else if(actual_ty(left.ty)->kind == Ty_string){
					tr_exp = Tr_strCompExp(oper,left.exp,right.exp);
				}
				else if(actual_ty(left.ty)->kind == Ty_int){
					tr_exp = Tr_intCompExp(oper,left.exp,right.exp);
				}
				else{
					tr_exp = Tr_nilExp();
				}
			}
			return expTy(tr_exp, Ty_Int());
		}
		case A_recordExp: {
			//sample: type{field, field : name=exp}
			log(a->pos, "A_recordExp: sym:%s", S_name(a->u.record.typ));
			Ty_ty type = S_look(tenv, a->u.record.typ);
			type = actual_ty(type);
			if(!type){
				EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
				return expTy(Tr_nilExp(), Ty_Int());
			}
			if(type->kind != Ty_record){
				EM_error(a->pos, "kind mismatch");
				return expTy(Tr_nilExp(), type);
			}

			Ty_fieldList expected = type->u.record;
			A_efieldList actual = a->u.record.fields;

			Tr_expList ls = NULL;
			int numOfField = 0;

			//compare fields anr record(type and name)
			while(actual && expected){
				// check name and type
				if (expected->head->name != actual->head->name) {
					EM_error(a->pos, "expected %s but get %s", S_name(expected->head->name), S_name(actual->head->name));
				}

				//field type
				struct expty exp = transExp(venv, tenv, actual->head->exp, l, label);
				Ty_ty actual_expected = actual_ty(expected->head->ty);
				Ty_ty actual_type = actual_ty(exp.ty);
				//oops!!!
				if (actual_type->kind != Ty_nil && actual_expected->kind != actual_type->kind ) {
					//printf("%d != %d\n",actual_expected->kind, actual_type->kind);
					EM_error(a->pos, "type not match");
				}
				actual = actual->tail;
				expected = expected->tail;

				ls = Tr_ExpList(exp.exp, ls);
				numOfField++;
			}
			//check number match
			if (expected != NULL || actual != NULL) {
				EM_error(a->pos, "field number of %s does not match", S_name(a->u.record.typ));
			}

            Tr_exp tr_exp = Tr_recordExp(ls, numOfField);

			return expTy(tr_exp, type);
		}
		case A_seqExp:{
			log(a->pos, "A_seqExp");
			A_expList seq = a->u.seq;
			struct expty exp_res;
			Tr_expList ls = NULL;

			while (seq) {
				assert(seq->head);
				exp_res = transExp(venv, tenv, seq->head, l, label);
				ls = Tr_ExpList(exp_res.exp, ls);
				seq = seq->tail;
			}
			Ty_ty result_ty = exp_res.ty;
			Tr_exp tr_exp = Tr_SeqExp(ls);
			return expTy(tr_exp, result_ty);
		}
		case A_assignExp:{
			A_var var = a->u.assign.var;
			A_exp exp = a->u.assign.exp;
			if(var->kind == A_simpleVar){
				log(a->pos, "A_assignExp: %s", S_name(var->u.simple));
			}
			else{
				log(a->pos, "A_assignExp: field type");
			}
			struct expty lvalue = transVar(venv, tenv, var, l, label);
			struct expty exp_ty = transExp(venv, tenv, exp, l, label);

			// not allow to assign to loop variable
			if(hasLoopVar(venv, var)){
				return expTy(Tr_err(), Ty_Int());
			}

			if (actual_ty(lvalue.ty) != actual_ty(exp_ty.ty)) {
				//printf("%d != %d\n", actual_ty(lvalue.ty)->kind, actual_ty(exp.ty)->kind);
				EM_error(a->pos, "unmatched assign exp");
			}

			Tr_exp tr_exp = Tr_assignExp(lvalue.exp, exp_ty.exp);
			return expTy(tr_exp, Ty_Void());
		} 
		case A_ifExp:{
			log(a->pos, "A_ifExp"); 
			struct expty test = transExp(venv, tenv, a->u.iff.test, l, label);
			struct expty then = transExp(venv, tenv, a->u.iff.then, l, label);
			struct expty elsee;// = transExp(venv, tenv, a->u.iff.elsee, l, label);
			Tr_exp tr_exp;
			Ty_ty res_ty;

			if(actual_ty(test.ty)->kind != Ty_int){
				EM_error(a->u.iff.test->pos, "test should be int");
			}
			
			//if-then-else
			if(a->u.iff.elsee->kind != A_nilExp){
				log(a->u.iff.test->pos, "if-then-else\n");
				elsee = transExp(venv, tenv, a->u.iff.elsee, l, label);
				if(actual_ty(then.ty)->kind != actual_ty(elsee.ty)->kind){
					EM_error(a->u.iff.then->pos, "then exp and else exp type mismatch");
				}
				tr_exp = Tr_ifExp(test.exp,then.exp,elsee.exp, elsee.ty);
				res_ty = elsee.ty;
			}
			//just if-then
			else{
				log(a->u.iff.test->pos, "just then");
				elsee = expTy(Tr_nilExp(), Ty_Void());
				if((actual_ty(then.ty) != Ty_Void() && actual_ty(then.ty)->kind != Ty_record)|| actual_ty(elsee.ty) != Ty_Void())
					EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
				tr_exp = Tr_ifExp(test.exp,then.exp,elsee.exp, then.ty);
				res_ty = then.ty;
			}
			return expTy(tr_exp, res_ty);
		}
	    case A_whileExp:{
			// while test do body
			log(a->pos, "A_whileExp");
			Temp_label done = Temp_newlabel();
			struct expty test = transExp(venv, tenv, a->u.whilee.test, l, label);
			struct expty body = transExp(venv, tenv, a->u.whilee.body, l, done);
			
			if (actual_ty(test.ty)->kind != Ty_int) {
				EM_error(a->u.whilee.test->pos, "type of test expression shoulf be int");
			}

			if (actual_ty(body.ty)->kind != Ty_void) {
				EM_error(a->u.whilee.body->pos, "while body must produce no value");
			}

			Tr_exp tr_exp = Tr_whileExp(test.exp, body.exp, done);
			return expTy(tr_exp, Ty_Void());
		}
		case A_forExp:{
			//sample: for var := lo to hi do body
			log(a->pos, "A_forExp");
			Temp_label done = Temp_newlabel();
			S_symbol var = a->u.forr.var;
			struct expty lo = transExp(venv, tenv, a->u.forr.lo, l, label);
			struct expty hi = transExp(venv, tenv, a->u.forr.hi, l, label);
			
			if (actual_ty(lo.ty)->kind != Ty_int) {
				EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
			}
			if (actual_ty(hi.ty)->kind != Ty_int) {
				EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
			}

			S_beginScope(venv);
			bool escape = a->u.forr.escape;
			Tr_access access = Tr_allocLocal(l, escape);

			S_enter(venv, var, E_ROVarEntry(access, lo.ty));
			struct expty body = transExp(venv, tenv, a->u.forr.body, l, done);
			S_endScope(venv);

			Tr_exp forv = Tr_simpleVar(access, l);
			Tr_exp tr_exp = Tr_forExp(forv, lo.exp, hi.exp, body.exp, done);
			return expTy(tr_exp, body.ty);
		}
		case A_breakExp: {
			log(a->pos, "A_breakExp");
			struct expty exp_ty;
			if(label){
				exp_ty = expTy(Tr_breakExp(label), Ty_Void());
			}else{
				exp_ty = expTy(Tr_nilExp(), Ty_Void());
			}
			return exp_ty;
		}
		case A_letExp:{
			log(a->pos, "A_letExp");
			Tr_exp tr_exp = Tr_nilExp();
			Tr_expList ls = NULL;

			S_beginScope(venv);
			S_beginScope(tenv);
			for(A_decList d = a->u.let.decs; d; d = d->tail){
				tr_exp = transDec(venv, tenv, d->head, l, label);
				ls = Tr_ExpList(tr_exp, ls);
			}
			struct expty body = transExp(venv, tenv, a->u.let.body, l, label);
			S_endScope(tenv);
			S_endScope(venv);

			tr_exp = Tr_letExp(ls, body.exp);
			return expTy(tr_exp, body.ty);
		}
		case A_arrayExp:{
			//sample: typ array[size] of init
			log(a->pos, "A_arrayExp: %s", S_name(a->u.array.typ));
			struct expty size = transExp(venv, tenv, a->u.array.size, l, label);
			struct expty init = transExp(venv, tenv, a->u.array.init, l, label);
			Ty_ty type = S_look(tenv, a->u.array.typ);
			type = actual_ty(type);

			if (!type) {
				EM_error(a->pos, "undefined type %s", S_name(a->u.array.typ));
				return expTy(Tr_nilExp(), Ty_Nil());
			}
			if (type->kind != Ty_array) {
				EM_error(a->pos, "not array type %s", S_name(a->u.record.typ));
				return expTy(Tr_nilExp(), type);
			}

			if (actual_ty(size.ty)->kind != Ty_int) {
				EM_error(a->u.array.size->pos, "type of size expression should be int");
			}
			if (actual_ty(init.ty) != actual_ty(type->u.array)&&
					!(actual_ty(type->u.array)->kind != Ty_record && actual_ty(init.ty)->kind == Ty_nil)) {
				EM_error(a->u.array.init->pos, "222type mismatch");
			}
			Tr_exp tr_exp = Tr_arrayExp(size.exp, init.exp);
			return expTy(tr_exp, type);
		}
		default:{
			EM_error(a->pos, "strange exp type %d", a->kind);
			return expTy(Tr_err(), Ty_Int());
		}
	}
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params){
	if (params == NULL) {
		return NULL;
	}
	Ty_ty type = S_look(tenv, params->head->typ);
	return Ty_TyList(type, makeFormalTyList(tenv, params->tail));

}

U_boolList makeFormalEscapeList(A_fieldList params) {
    if (params == NULL) {
        return NULL;
    }

    return U_BoolList(params->head->escape, makeFormalEscapeList(params->tail));
}

Ty_fieldList makeFieldList(S_table tenv, A_fieldList fields) {
	Ty_ty type = S_look(tenv, fields->head->typ);
	Ty_field field = Ty_Field(fields->head->name, type);
	
	if (fields->tail) {
		return Ty_FieldList(field, makeFieldList(tenv, fields->tail));
	} else {
		return Ty_FieldList(field, NULL);
	}
}
int hasLoopVar(S_table venv, A_var v) {
	switch(v->kind) {
		case A_simpleVar: {
			E_enventry x = S_look(venv, v->u.simple);
			if (x->readonly) {
				EM_error(v->pos, "loop variable can't be assigned");
				return 1;
			}
			return 0;
		} 
	   	case A_fieldVar:
			return hasLoopVar(venv, v->u.field.var);
		case A_subscriptVar:
			return hasLoopVar(venv, v->u.subscript.var);
	}
	assert(0); /* should have returned from some clause of the switch */
}