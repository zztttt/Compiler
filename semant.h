#ifndef __SEMANT_H_
#define __SEMANT_H_

#include "absyn.h"
#include "symbol.h"
#include "temp.h"
#include "frame.h"
#include "translate.h"
#include "tree.h"
#include "printtree.h"
struct expty;

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level curr_level, Temp_label);
struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level curr_level, Temp_label);
Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level l, Temp_label);
Ty_ty transTy (S_table tenv, A_ty a);

F_fragList SEM_transProg(A_exp exp);

//helper functions
Ty_ty actual_ty(Ty_ty t);
int hasLoopVar(S_table venv, A_var v);
U_boolList makeFormalEscapeList(A_fieldList params);
Ty_fieldList makeFieldList(S_table tenv, A_fieldList fields);
Ty_tyList makeFormalTyList(S_table tenv, A_fieldList list);
#endif