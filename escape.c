/* escape.c */

#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "escape.h"

static void traverseExp(S_table, int depth, A_exp);
static void traverseDec(S_table, int depth, A_dec);
static void traverseVar(S_table, int depth, A_var);

static void traverseExp(S_table table, int depth, A_exp a){
	switch(a->kind){
		case A_varExp: {
			A_var var = a->u.var;
			traverseVar(table, depth, var);
			break;
		}
		case A_callExp:{
			A_expList args = a->u.call.args;

			for(A_expList exps=args;exps;exps=exps->tail){
					A_exp param = exps->head;
					traverseExp(table, depth, param);
			}
			break;		
		}
		case A_opExp:{ 
			A_exp left = a->u.op.left; 
			A_exp right = a->u.op.right;
			traverseExp(table, depth, left);
			traverseExp(table, depth, right);
			break;
		}
		case A_recordExp: {
			S_symbol typ = a->u.record.typ; 
			A_efieldList fields = a->u.record.fields;
			for(A_efieldList fs=fields; fs; fs=fs->tail){
					A_efield f = fs->head;
					S_symbol fname = f->name; A_exp fexp = f->exp;
					traverseExp(table, depth, fexp);
				}
			break;
		}
		case A_seqExp:{
			for(A_expList seq=a->u.seq; seq; seq=seq->tail){
				A_exp ex = seq->head;
				traverseExp(table, depth, ex);
			}
			break;
		}
		case A_assignExp:{
			A_var var = a->u.assign.var; 
			A_exp ex = a->u.assign.exp;
			traverseVar(table, depth, var);
			traverseExp(table, depth, ex);
			break;
		} 
		case A_ifExp:{
			A_exp test = a->u.iff.test; 
			A_exp then = a->u.iff.then;
			traverseExp(table, depth, test);
			traverseExp(table, depth, then);
			if(a->u.iff.elsee != NULL)
				traverseExp(table, depth, a->u.iff.elsee);
			break;
		}
		case A_whileExp:{
			A_exp test = get_whileexp_test(a);
			A_exp body = get_whileexp_body(a);
			traverseExp(table, depth, test);
			traverseExp(table, depth, body);
			break;
		}
		case A_forExp:{
			S_symbol var = a->u.forr.var; 
			A_exp lo = a->u.forr.lo;
			A_exp hi = a->u.forr.hi;
			A_exp body = a->u.forr.body;

			a->u.forr.escape = FALSE;
			S_enter(table, var, E_EscEntry(depth,&(a->u.forr.escape)));
			traverseExp(table, depth, lo);
			traverseExp(table, depth, hi);
			traverseExp(table, depth, body);
			break;
		}
		case A_letExp:{
			A_exp body = a->u.let.body;
			for(A_decList decs=a->u.let.decs; decs; decs=decs->tail){
				A_dec dec = decs->head;
				traverseDec(table, depth, dec);
			}
			traverseExp(table, depth, body);
			break;
		}
		case A_arrayExp:{
			A_exp size = a->u.array.size;
			A_exp init = a->u.array.init;
			traverseExp(table, depth, size);
			traverseExp(table, depth, init);
			break;
		}
		case A_nilExp: case A_intExp: case A_stringExp: case A_breakExp:
			break;
		default:{
			EM_error(a->pos, "strange exp type %d", a->kind);
			assert(0);
		}
	}
}

static void traverseDec(S_table table, int depth, A_dec d){
	switch(d->kind){
		case A_functionDec:{		
			for(A_fundecList funcs=d->u.function; funcs; funcs=funcs->tail){
				A_fundec func = funcs->head;				
				A_fieldList params = func->params; 
		 		for(A_fieldList ls=params;ls;ls=ls->tail){
					A_field param = ls->head;
					S_enter(table, param->name, E_EscEntry(depth+1, &param->escape));
					param->escape = FALSE;
				 }
				A_exp body = func->body;
				traverseExp(table, depth+1, body);
			}
			break;
		}	
		case A_varDec:{
			S_symbol var = d->u.var.var;
			A_exp init = d->u.var.init;
			d->u.var.escape = FALSE;
			S_enter(table, var, E_EscEntry(depth, &d->u.var.escape));			
			traverseExp(table, depth, init);
			break;
		}	
		case A_typeDec:
			break;
		default:{
			EM_error(d->pos, "strange Dec type %d", d->kind);
			assert(0);
		}
	}
}

static void traverseVar(S_table table, int depth, A_var v){
	switch(v->kind){
		case A_simpleVar:{
			S_symbol simple = v->u.simple;
			E_enventry esc = S_look(table, simple);
			if(esc && depth > esc->u.esc.depth){
				*esc->u.esc.escape = TRUE;
			}
			break;
		}
		case A_fieldVar:{
			A_var var = v->u.field.var; 
			traverseVar(table, depth, var);			
			break;
		}
		case A_subscriptVar:{
			A_var var = v->u.subscript.var;
			A_exp ex = v->u.subscript.exp;
			traverseVar(table, depth, var);
			traverseExp(table, depth, ex);
			break;
		}
		default:{
			EM_error(v->pos, "strange variable type %d", v->kind);
			assert(0);
		}
	}
}

void Esc_findEscape(A_exp exp){
	S_table table = S_empty();
	traverseExp(table, 1, exp);
}
