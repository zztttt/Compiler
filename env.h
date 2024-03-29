/*Lab4: Your implementation of lab4*/

#ifndef ENV_H_
#define ENV_H_

#include "types.h"
#include "translate.h"
#include "temp.h"

typedef struct E_enventry_ *E_enventry;

struct E_enventry_ {
	enum {E_varEntry, E_funEntry, E_escEntry} kind;
	int readonly; //for loop var
	union 
	{
		struct {Tr_access access; Ty_ty ty;} var;
		struct {Tr_level level; Temp_label label; Ty_tyList formals; Ty_ty result;} fun;
		struct {int depth; bool *escape;} esc;
	} u;
};

E_enventry E_VarEntry(Tr_access access, Ty_ty ty);
E_enventry E_ROVarEntry(Tr_access access, Ty_ty ty);
E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result);
E_enventry E_EscEntry(int depth, bool *escape);

S_table E_base_tenv(void);
S_table E_base_venv(void);

#endif
