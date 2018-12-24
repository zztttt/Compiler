#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"
#include "table.h"
#include "printtree.c"

#define SEMENT_DEBUG 1

#define log(...)\
	if(SEMENT_DEBUG)\
		EM_error(__VA_ARGS__);

/*Lab4: Your implementation of lab4*/


struct expty 
{
	Tr_exp exp; //empty pointer void*
	Ty_ty ty;
};

//In Lab4, the first argument exp should always e **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

//helper functions
Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params){
	if (params == NULL) {
		return NULL;
	}
	Ty_ty type = S_look(tenv, params->head->typ);
	return Ty_TyList(type, makeFormalTyList(tenv, params->tail));

}

U_boolList makeFormalEscapeList(A_fieldList fields)
{
	if (fields) {
		return U_BoolList(fields->head->escape, makeFormalEscapeList(fields->tail));
	} else {
		return NULL;
	}
}

U_boolList makeFormalEscList(A_fieldList params) {
    if (params == NULL) {
        return NULL;
    }

    return U_BoolList(params->head->escape, makeFormalEscList(params->tail));
}

Ty_ty actual_ty(Ty_ty t) {
	while (t && t->kind == Ty_name) {
		t = t->u.name.ty;
	}
	return t;
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


F_fragList SEM_transProg(A_exp exp){
	Temp_label func_label = Temp_newlabel();
	Tr_level mainFrame = Tr_outermost();
	Tr_level main_level = Tr_newLevel(mainFrame, Temp_newlabel(), NULL);

	struct expty body_exp = transExp(E_base_venv(), E_base_tenv(), exp, main_level, NULL);

    // end main fragment
	Tr_functionDec(body_exp.exp, mainFrame);
    //Tr_procEntryExit(fun_entry->u.fun.level, body_exp.exp, NULL);

    return Tr_getFragList();
}


struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level level, Temp_label tl){
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
			Tr_exp tr_exp = Tr_simpleVar(tr_access, level);
			
			return expTy(tr_exp, actual_ty(var_entry->u.var.ty));
		}
		case A_fieldVar: {
			log(v->pos, "A_fieldVar: %s", S_name(v->u.field.sym));
			//sample: arr.field
			A_var var = v->u.field.var;
			S_symbol sym = v->u.field.sym;

			struct expty lvalue = transVar(venv, tenv, var, level, tl);
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
		case A_subscriptVar: {
			//sample: var[exp]
			log(v->pos, "A_subscriptVar");
			A_var typ = v->u.subscript.var;
			A_exp exp = v->u.subscript.exp;
			struct expty lvalue = transVar(venv, tenv, typ, level, tl);
			struct expty index = transExp(venv, tenv, exp, level, tl);

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
			//differ!
			Tr_exp tr_exp = Tr_subscriptVar(lvalue.exp, index.exp);
			Ty_ty ty_array = lvalue.ty->u.array;
			return expTy(tr_exp, actual_ty(ty_array));
		}
	}
	assert(0);
}
struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level, Temp_label tl){
	assert(venv);
	assert(tenv);
	assert(a);
	switch(a->kind){
		case A_varExp:{
			log(a->pos, "A_varExp");
			return transVar(venv, tenv, a->u.var, level, tl);
		}
		case A_intExp:{
			log(a->pos, "A_intExp: intt:%d", a->u.intt);
			return expTy(Tr_intExp(a->u.intt), Ty_Int());
		}
		case A_stringExp:{
			log(a->pos, "A_stringExp: stringg: %s", a->u.stringg);
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());
		}
		case A_nilExp:{
			log(a->pos, "A_nilExp");
			return expTy(Tr_nilExp(), Ty_Nil());
		}
		case A_breakExp:{
			log(a->pos, "A_breakExp");
			struct expty exp_ty;
			if(tl){
				exp_ty = expTy(Tr_breakExp(tl), Ty_Void());
			}else{
				exp_ty = expTy(Tr_nilExp(), Ty_Void());
			}
			return exp_ty;
		}
		case A_callExp:{
			log(a->pos, "A_callExp: %s", S_name(a->u.call.func));
			S_symbol func = a->u.call.func;
			E_enventry func_entry = S_look(venv, func);
			if (!func_entry || func_entry->kind != E_funEntry) {
				EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
				return expTy(Tr_nilExp(), Ty_Int());
			}

			// check parameter types and number
			Ty_tyList expected = func_entry->u.fun.formals;
			A_expList actual = a->u.call.args;

			Tr_expList list = Tr_ExpList(NULL, NULL);
			Tr_expList tail = list;

			//compare args types and expected types
			while(actual && expected){
				struct expty arg_ty = transExp(venv, tenv, actual->head, level, tl);
				if (actual_ty(arg_ty.ty)->kind != actual_ty(expected->head)->kind) {
					EM_error(actual->head->pos, "para type mismatch");
				}
				actual = actual->tail;
				expected = expected->tail;

				//append to para list
				tail->tail = Tr_ExpList(arg_ty.exp, NULL);
				tail = tail->tail;
			}
			if (expected != NULL || actual != NULL) {
				EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
			}
			//printf("end call\n");
			//skip the head node
			list = list->tail;
			
			//Tr_callExp(Temp_label func, Tr_expList args, Tr_level caller, Tr_level callee)
			Tr_level callee = func_entry->u.fun.level;
			Temp_label func_label = func_entry->u.fun.label;
			Tr_exp tr_exp = Tr_callExp(callee, func_label, list, level);
			Ty_ty func_result = func_entry->u.fun.result;
			return expTy(tr_exp, actual_ty(func_result));
		}
		case A_recordExp:{
			//sample: type{field, field : name=exp}
			log(a->pos, "A_recordExp: sym:%s", S_name(a->u.record.typ));
			Ty_ty type = S_look(tenv, a->u.record.typ);
			
			type = actual_ty(type);
			//Ty_print(type);
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

			Tr_expList list = Tr_ExpList(NULL, NULL);  // dummy head node
            Tr_expList tail = list;
			int numOfField = 0;

			//compare fields anr record(type and name)
			while(actual && expected){
				// check name and type
				if (expected->head->name != actual->head->name) {
					EM_error(a->pos, "expected %s but get %s", S_name(expected->head->name), S_name(actual->head->name));
				}

				//field type
				struct expty exp = transExp(venv, tenv, actual->head->exp, level, tl);
				Ty_ty actual_expected = actual_ty(expected->head->ty);
				Ty_ty actual_type = actual_ty(exp.ty);
				//oops!!!
				if (actual_type->kind != Ty_nil && actual_expected->kind != actual_type->kind ) {
					//printf("%d != %d\n",actual_expected->kind, actual_type->kind);
					EM_error(a->pos, "type not match");
				}
				actual = actual->tail;
				expected = expected->tail;

				tail->tail = Tr_ExpList(exp.exp, NULL);
				numOfField++;
				tail = tail->tail;
			}
			//check number suit?
			if (expected != NULL || actual != NULL) {
				EM_error(a->pos, "field number of %s does not match", S_name(a->u.record.typ));
			}
			list = list->tail;

            Tr_exp tr_exp = Tr_recordExp(list, numOfField);

			return expTy(tr_exp, type);
		}
		case A_seqExp:{
			log(a->pos, "A_seqExp");
			A_expList seq = a->u.seq;

			struct expty exp_res;
			Ty_ty result_ty = Ty_Void();
			Tr_exp tr_exp = Tr_nilExp();
			while (seq) {
				assert(seq->head);
				exp_res = transExp(venv, tenv, seq->head, level, tl);

				tr_exp = Tr_seqExp(tr_exp, exp_res.exp);
				result_ty = exp_res.ty;
				seq = seq->tail;
			}
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
			

			struct expty lvalue = transVar(venv, tenv, var, level, tl);
			struct expty exp_ty = transExp(venv, tenv, exp, level, tl);

			// not allow to assign to loop variable
			hasLoopVar(venv, var);

			if (actual_ty(lvalue.ty) != actual_ty(exp_ty.ty)) {
				//printf("%d != %d\n", actual_ty(lvalue.ty)->kind, actual_ty(exp.ty)->kind);
				EM_error(a->pos, "unmatched assign exp");
			}

			Tr_exp tr_exp = Tr_assignExp(lvalue.exp, exp_ty.exp);
			return expTy(tr_exp, Ty_Void());
		}
		case A_ifExp:{
			//if then else
			log(a->pos, "A_ifExp"); 
			struct expty test = transExp(venv, tenv, a->u.iff.test, level, tl);
			struct expty then = transExp(venv, tenv, a->u.iff.then, level, tl);
			struct expty elsee;
			Tr_exp tr_exp;

			if(actual_ty(test.ty)->kind != Ty_int){
				EM_error(a->u.iff.test->pos, "test should be int");
			}
						
			if(a->u.iff.elsee->kind != A_nilExp){
				//else exist
				//printf("else exist\n");
				//printf("else: %d\n", a->u.iff.elsee->kind);
				elsee = transExp(venv, tenv, a->u.iff.elsee, level, tl);
				if(actual_ty(then.ty)->kind != actual_ty(elsee.ty)->kind){
					EM_error(a->u.iff.then->pos, "then exp and else exp type mismatch");
				}
				//printf("end else\n");
				tr_exp = Tr_ifelseExp(test.exp, then.exp, elsee.exp);
			}
			else{//just if-then
				//printf("just then:%d\n", a->u.iff.test->pos);
				log(a->u.iff.test->pos, "just then");
				//printf("test:%d\n", a->u.iff.test->kind);
				elsee = expTy(NULL, Ty_Void());
				//printf("then.kind:%d\n", actual_ty(then.ty)->kind);
				//if(actual_ty(then.ty)->kind != Ty_record)
				//	printf("===============\n");
				if((actual_ty(then.ty) != Ty_Void() && actual_ty(then.ty)->kind != Ty_record)|| actual_ty(elsee.ty) != Ty_Void())
					EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
				//printf("1121111\n");
				tr_exp = Tr_ifExp(test.exp, then.exp);
			}
			//differ!
			return expTy(tr_exp, then.ty);
		}
		case A_whileExp:{
			// while test do body
			log(a->pos, "A_whileExp");
			Temp_label done = Temp_newlabel();
			struct expty test = transExp(venv, tenv, a->u.whilee.test, level, tl);
			struct expty body = transExp(venv, tenv, a->u.whilee.body, level, tl);
			
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
			struct expty lo = transExp(venv, tenv, a->u.forr.lo, level, tl);
			struct expty hi = transExp(venv, tenv, a->u.forr.hi, level, tl);
			

			if (actual_ty(lo.ty)->kind != Ty_int) {
				EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
			}
			if (actual_ty(hi.ty)->kind != Ty_int) {
				EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
			}
			
			//oops!!!
			S_beginScope(venv);
			S_beginScope(tenv);
			bool escape = a->u.forr.escape;
			Tr_access access = Tr_allocLocal(level, escape);
			S_enter(venv, var, E_ROVarEntry(access, Ty_Int()));

			struct expty body = transExp(venv, tenv, a->u.forr.body, level, tl);
			
			if (actual_ty(body.ty)->kind != Ty_void) {
				EM_error(a->u.forr.body->pos, "type of body expression should be void");
			}
			S_endScope(tenv);
			S_endScope(venv);

			Tr_exp tr_exp = Tr_forExp(lo.exp, hi.exp, body.exp, access, level, done);

			return expTy(tr_exp, Ty_Void());
		}
		case A_opExp:{
			log(a->pos, "A_opExp: %d", a->u.op.oper);
			A_oper oper = a->u.op.oper;
			struct expty left = transExp(venv, tenv, a->u.op.left, level, tl);
			struct expty right = transExp(venv, tenv, a->u.op.right, level, tl);
			if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp ){
				if(actual_ty(left.ty)->kind != Ty_int ){
					EM_error(a->u.op.left->pos, "integer required");
					return expTy(Tr_nilExp(), Ty_Int());
				}
				if(actual_ty(right.ty)->kind != Ty_int ){
					EM_error(a->u.op.right->pos, "integer required");
					return expTy(Tr_nilExp(), Ty_Int());
				}

				Tr_exp tr_exp = Tr_opaluExp(oper, left.exp, right.exp);
				return expTy(tr_exp, Ty_Int());
			}
			else{
				Ty_ty left_ty = actual_ty(left.ty);
                Ty_ty right_ty = actual_ty(right.ty);

				//need the same type
				if (left_ty != right_ty && 
					!(left_ty->kind == Ty_record && right_ty->kind == Ty_nil)) {
					EM_error(a->u.op.left->pos, "same type required");
				}
				bool isStrCmp = (left.ty->kind == Ty_string);
				Tr_exp tr_exp = Tr_opcmpExp(oper, left.exp, right.exp, isStrCmp);
				return expTy(tr_exp, Ty_Int());
			}
			//return expTy(NULL, Ty_Int());
		}
		//update for lab5
		case A_letExp:{
			log(a->pos, "A_letExp");
			struct expty exp_ty;
			Tr_exp tr_exp = Tr_nilExp();
			A_decList d;

			S_beginScope(venv);
			S_beginScope(tenv);
			//printf("after beginscope\n");
			for(d = a->u.let.decs; d; d = d->tail){
				tr_exp = transDec(venv, tenv, d->head, level, tl);
			}
			//printf("begin body\n");
			exp_ty = transExp(venv, tenv, a->u.let.body, level, tl);
			exp_ty.exp = Tr_seqExp(tr_exp, exp_ty.exp);
			//printf("before endscope\n");
			S_endScope(tenv);
			S_endScope(venv);
			return exp_ty;
		}
		//update for lab5
		case A_arrayExp: {
			//sample: typ array[size] of init
			log(a->pos, "A_arrayExp: %s", S_name(a->u.array.typ));
			struct expty size = transExp(venv, tenv, a->u.array.size, level, tl);
			struct expty init = transExp(venv, tenv, a->u.array.init, level, tl);
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
		
		
	}
	EM_error(a->pos, "switch case not exist");
	assert(0);
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level level, Temp_label tl){
	assert(venv && tenv && d);
	switch(d->kind){
		//update for lab5
		case A_varDec:{
			//printf("111\n");
			if(!d->u.var.typ){
				log(d->pos, "A_varDec: sym:%s notype", S_name(d->u.var.var));
			}
			else{
				log(d->pos,"A_varDec: sym:%s type:%s", S_name(d->u.var.var), S_name(d->u.var.typ));
			}
			struct expty init = transExp(venv, tenv, d->u.var.init, level, tl);
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

			Tr_access access = Tr_allocLocal(level, d->u.var.escape);
			S_enter(venv, d->u.var.var, E_VarEntry(access, init.ty));	
			Tr_exp tr_exp = Tr_simpleVar(access, level);		
			return Tr_assignExp(tr_exp, init.exp);
		}
		//update for lab5, TAB_empty???
		case A_typeDec:{
			log(d->pos, "A_typeDec");
			TAB_table name_table = TAB_empty();
            A_nametyList types = d->u.type;
            while (types) {
                if (TAB_look(name_table, types->head->name) != NULL) {
                    EM_error(d->pos, "two types with the same name %s in batch declaration\n",
                             S_name(types->head->name));
                }
                TAB_enter(name_table, types->head->name, (void *) 1);
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
		//update for lab5
		case A_functionDec:{
			log(d->pos, "A_functionDec");
			TAB_table name_table = TAB_empty();
			A_fundecList func = d->u.function;
			while (func) {
                if (TAB_look(name_table, func->head->name) != NULL) {
                    EM_error(d->pos, "two functions with the same name %s in batch declaration\n",
                             S_name(func->head->name));
                }
                TAB_enter(name_table, func->head->name, (void *) 1);
                func = func->tail;
            }

			func = d->u.function;
			//put func into envirnment
			while(func){
				//printf("function %s header\n", S_name(func->head->name));
				S_symbol funcname = func->head->name;
				//don't need below
				/*if(S_look(venv, funcname) != NULL){
					EM_error(d->pos, "two functions have the same name");
				}*/
				S_symbol result = func->head->result;
				Ty_ty resultTy = Ty_Void();
				if(result){
					resultTy = S_look(tenv,func->head->result);
					if(!resultTy){
						EM_error(func->head->pos, "undefined result type:%s", S_name(result));
					}
				}
				else{
					resultTy = Ty_Void();
				}
				//create new level
				Temp_label func_label = Temp_newlabel();
                U_boolList formal_escapes = makeFormalEscList(func->head->params);
                Tr_level new_level = Tr_newLevel(level, func_label, formal_escapes);

				Ty_tyList formal = makeFormalTyList(tenv, func->head->params);
				//TyList_print(formal);
				E_enventry entry = E_FunEntry(new_level, func_label, formal, resultTy);
				entry->kind = E_funEntry;
				S_enter(venv, func->head->name, entry);
				func = func->tail;
			}
			
			//restore functionlist
			//printf("begin restore\n");
			func = d->u.function;
			while(func){
				//printf("func %s body\n", S_name(func->head->name));
				E_enventry fun_entry = S_look(venv, func->head->name);
                Tr_accessList formal_accesses = Tr_formals(fun_entry->u.fun.level);
				//Ty_tyList formal = makeFormalTyList(tenv, func->head->params);
				A_fieldList params = func->head->params;
				//printf("begin scope\n");
				S_beginScope(venv);
				while(params){
					Ty_ty type = S_look(tenv, params->head->typ);
					E_enventry var_entry = E_VarEntry(formal_accesses->head, type);
					S_enter(venv, params->head->name, var_entry);
					params = params->tail;
		
					formal_accesses = formal_accesses->tail;
				}
				struct expty exp = transExp(venv, tenv, func->head->body, fun_entry->u.fun.level, tl);
				S_endScope(venv);


				E_enventry x = S_look(venv, func->head->name);

				Ty_ty expected_result = actual_ty(x->u.fun.result);
				Ty_ty actual_result = actual_ty(exp.ty);
				if(expected_result->kind == Ty_void){
					if(actual_result->kind != Ty_void){
						EM_error(func->head->pos, "procedure returns value");
					}
				}else if(expected_result->kind != actual_result->kind){
					EM_error(func->head->pos, "procedure returns different type");
				}
				Tr_functionDec(exp.exp, fun_entry->u.fun.level);
				//S_endScope(venv);
				func = func->tail;
			}
			return Tr_nilExp();
			break;
		}
	}
	assert(0);
}

Ty_fieldList makeFieldList(S_table tenv, A_fieldList fields) {
	Ty_ty type = S_look(tenv, fields->head->typ);
	if (!type) {
		EM_error(fields->head->pos, "undefined type %s", S_name(fields->head->typ));
		type = Ty_Int();
	}
	Ty_field field = Ty_Field(fields->head->name, type);

	if (fields->tail == NULL) {
		return Ty_FieldList(field, NULL);
	} else {
		return Ty_FieldList(field, makeFieldList(tenv, fields->tail));
	}
}

Ty_ty transTy(S_table tenv, A_ty a){
	switch(a->kind){
		//update for lab5
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
		//update for lab5
		case A_recordTy:{
			log(a->pos, "A_recordTy");
			return Ty_Record(makeFieldList(tenv, a->u.record));
		}
		//update for lab5
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
	EM_error(a->pos, "switch noe exist");
	assert(0);
	return NULL;
}