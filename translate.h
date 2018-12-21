#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct patchList_ *patchList;
struct patchList_
{
        Temp_label *head;
        patchList tail;
};

struct Cx {
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

/* 一种模拟三种表达式的exp类型 */
typedef struct Tr_exp_ *Tr_exp;
struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

/* new data struct, exp链：recordexp和seqexp的时候用一用 */
typedef struct Tr_expList_ *Tr_expList;
struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;
};

typedef struct Tr_access_ *Tr_access;
typedef struct Tr_accessList_ *Tr_accessList;
typedef struct Tr_level_ *Tr_level;

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
	Tr_accessList formals; //add parameter
};

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);
Tr_access Tr_Access(Tr_level level, F_access access);
Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

/* 当为程序的主函数创建层次时，应当传递一个特殊的层次值，此值由调用Tr_outermost()得到，它每次返回的都是相同的层次 */
Tr_level Tr_outermost(void);

/* tranDec通过调用tr_newlevel为每一个函数创建一个新的“嵌套层”，tr_newlevel调用f_newframe建立一个新的栈帧 */
Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

/* 返回在当前level中的所有变量序列 */
Tr_accessList Tr_formals(Tr_level level);

/* 返回一个相对帧指针位移地址的inframe访问 */
/* 当semant处理一个位于level层的局部变量声明时，调用tr_alloclocal在lev指定的这一层创建变量，参数esc指出是否逃逸*/
Tr_access Tr_allocLocal(Tr_level level, bool escape);

F_fragList Tr_getFragList(void);

/****************************************************************/

/* translation: 返回Ex, Nx或者Cx: lab4中transExp的值 */

/* translate var */
Tr_exp Tr_simpleVar(Tr_access access, Tr_level level); //EX, 栈上的变量，当前level

Tr_exp Tr_fieldVar(Tr_exp addr, int nth); //EX, 首地址，field数

Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp index); //EX, 首地址，取值数

/* translate exp */
Tr_exp Tr_nilExp(); //EX, const 0

Tr_exp Tr_intExp(int n); //EX, int值

Tr_exp Tr_stringExp(string s); //EX, string值

Tr_exp Tr_callExp(Tr_level callee, Temp_label func, Tr_expList params, Tr_level caller); //NX/EX, 函数名，变量序列

Tr_exp Tr_opaluExp(A_oper oper, Tr_exp left, Tr_exp right); //EX, 操作符，左操作数，右操作数

Tr_exp Tr_opcmpExp(A_oper oper, Tr_exp left, Tr_exp right, bool isStrCmp); //CX

Tr_exp Tr_recordExp(Tr_expList fields, int n); //EX

Tr_exp Tr_seqExp(Tr_exp e1, Tr_exp e2); //NX, 序列

Tr_exp Tr_assignExp(Tr_exp var, Tr_exp exp); //NX, 左值，右值

Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then); //Cx, 条件判断，then

Tr_exp Tr_ifelseExp(Tr_exp test, Tr_exp then, Tr_exp elsee);

Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done); //NX, 条件判断，body

Tr_exp Tr_forExp(Tr_exp lo, Tr_exp hi, Tr_exp body, Tr_access access, Tr_level level, Temp_label done); //NX, 循环变量i，low值，high值，body

Tr_exp Tr_breakExp(Temp_label done); //NX

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init); //EX, 数组大小，数组初值

/****************************************************************/

T_stm Tr_procEntryExit(Tr_exp body, Tr_level level, Tr_accessList formals);

void Tr_functionDec(Tr_exp exp, Tr_level level);

#endif
