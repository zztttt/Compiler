#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"
#include <assert.h>

//LAB5: you can modify anything you want.
//工具函数就写成static类型，不用在h文件中声明

/****************************************************************/

//new variable

/* fraglist */
static F_fragList frags; 

static const int F_wordSize = 8;

/* main frame level */
static Tr_level outermost = NULL;

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
	Tr_expList explist = (Tr_expList)checked_malloc(sizeof(*explist));
	explist->head = head;
	explist->tail = tail;
	return explist;
}

Tr_access Tr_Access(Tr_level level, F_access access)
{
	Tr_access traccess = (Tr_access)checked_malloc(sizeof(*traccess));
	traccess->level = level;
	traccess->access = access;
	return traccess;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
	Tr_accessList accesses = (Tr_accessList)checked_malloc(sizeof(*accesses));
	accesses->head = head;
	accesses->tail = tail;
	return accesses;
}

// use in Tr_level 
// create parameter: level->formals (Tr_accessList)
static Tr_accessList Tr_makeFormals(Tr_level level, F_accessList accesses)
{
	if (accesses) {
		return Tr_AccessList(Tr_Access(level, accesses->head), Tr_makeFormals(level, accesses->tail));
	} else {
		return NULL;
	}
}

// 赋值Tr_level
// F_frame F_newFrame(Temp_label name, U_boolList formals)
Tr_level Tr_outermost(void)
{
	//if already exist
	if (outermost) {
		return outermost;
	} else {
		//create new level 
		outermost = (Tr_level)checked_malloc(sizeof(*outermost));
		outermost->frame = F_newFrame(Temp_newlabel(), NULL);
		outermost->parent = NULL;
		outermost->formals = NULL;
		return outermost;
	}
}

// 赋值Tr_level
//static F_accessList F_makeFormals(U_boolList formals, int offset)
Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
	Tr_level level = (Tr_level)checked_malloc(sizeof(*level));
	level->frame = F_newFrame(name, U_BoolList(TRUE, formals));
	level->parent = parent;
	level->formals = Tr_makeFormals(level, (F_formals(level->frame))->tail);
	return level;
}

//struct Tr_level_ {
//	F_frame frame;
//	Tr_level parent;
//	Tr_accessList formals; //add parameter
//};
Tr_accessList Tr_formals(Tr_level level)
{
	return level->formals;
}

//F_access F_allocLocal(F_frame frame, bool escape)
Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
	return Tr_Access(level, F_allocLocal(level->frame, escape));
}

//static link: 当前层level和目标层level
//T_exp F_Exp(F_access access, T_exp fp)
//F_accessList F_getFormals(F_frame frame)
static T_exp staticlink(Tr_level level, Tr_level dest)
{
	T_exp ex = T_Temp(F_FP()); //获取本level的栈帧
	Tr_level curlevel = level;
	while (curlevel && curlevel != dest) 
	{
		if (curlevel == outermost)
		{
			ex = T_Mem(ex);
			break;
		}
		ex = F_Exp(F_formals(curlevel->frame)->head, ex); //获取上一层frame的fp
		curlevel = curlevel->parent;
	}

	return ex; //返回目标frame的fp
}

// return parameter
// same as Tr_getResult() in PPT
F_fragList Tr_getFragList(void)  { return frags; }

/****************************************************************/

/* 原本就写好的 */

//typedef struct patchList_ *patchList;
/*struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};*/

/* 表示“需要填充标号的地点”组成的表 */
static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

/* 通过调用doPatch(e->u.cx.trues.t)利用标号t来填充真值标号回填表 */
void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

/****************************************************************/

/* Ex代表“表达式”，表示为Tr_exp */
static Tr_exp Tr_Ex(T_exp ex)
{
	Tr_exp tr_ex = (Tr_exp)checked_malloc(sizeof(*tr_ex));
	tr_ex->kind = Tr_ex;
	tr_ex->u.ex = ex;
	return tr_ex;
}

/* Nx代表“无结果语句”，表示为Tree语句 */
static Tr_exp Tr_Nx(T_stm nx)
{
	Tr_exp tr_nx = (Tr_exp)checked_malloc(sizeof(*tr_nx));
	tr_nx->kind = Tr_nx;
	tr_nx->u.nx = nx;
	return tr_nx;
}

/* Cx代表“条件语句”，表示为一个可能转移到两个标号之一的语句 */
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)
{
	Tr_exp tr_cx = (Tr_exp)checked_malloc(sizeof(*tr_cx));
	tr_cx->kind = Tr_cx;
	tr_cx->u.cx.trues = trues;
	tr_cx->u.cx.falses = falses;
	tr_cx->u.cx.stm = stm;
	return tr_cx;
}

/* 强制类型转换函数 */
/* 主要用于Tr_exp的加法 */
static T_exp unEx(Tr_exp e)
{
	switch (e->kind) 
	{
		case Tr_ex:
		{
			return e->u.ex;
		}
		case Tr_nx:
		{
			return T_Eseq(e->u.nx, T_Const(0)); //副作用
		}
		case Tr_cx:
		{
			Temp_temp r = Temp_newtemp(); //构造寄存器
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);

			//返回寄存器r的值作为ex
			T_exp ex = T_Eseq(T_Move(T_Temp(r), T_Const(1)),
					T_Eseq(e->u.cx.stm,
					T_Eseq(T_Label(f),
					T_Eseq(T_Move(T_Temp(r), T_Const(0)),
					T_Eseq(T_Label(t),
					T_Temp(r))))));
			return ex;
		}
	}
	assert(0);
}

/* 主要用于SEQ */
static T_stm unNx(Tr_exp e)
{
	switch (e->kind)
	{
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_nx:
			return e->u.nx;
		case Tr_cx:
		{
			//忽略跳转分支
			Temp_label empty = Temp_newlabel();
			doPatch(e->u.cx.trues, empty);
			doPatch(e->u.cx.falses, empty);
			return T_Seq(e->u.cx.stm, T_Label(empty));
		}
	}
	assert(0);
}

/* 主要用于if，while，for的判断语句 */
/* static patchList PatchList(Temp_label *head, patchList tail) */
static struct Cx unCx(Tr_exp e)
{
	switch (e->kind)
	{
		case Tr_ex:
		{
			//cx: if(ex), label的patch在translate过程中写入
			struct Cx cx;
			cx.stm = T_Cjump(T_ne, unEx(e), T_Const(0), NULL, NULL);
			cx.trues = PatchList(&(cx.stm->u.CJUMP.true), NULL);
			cx.falses = PatchList(&(cx.stm->u.CJUMP.false), NULL);
			return cx;
		}
		case Tr_nx:
			//unCx应该拒绝kind标志为Tr_nx的exp
			//这种情况正常情况下不会发生
			assert(0);
			break;
		case Tr_cx:
			return e->u.cx;
	}
	assert(0);
}

/****************************************************************/
/* translation: 返回Ex, Nx或者Cx: lab4中transExp的值 */
/*static Tr_exp Tr_Ex(T_exp ex)
static Tr_exp Tr_Nx(T_stm nx)
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)*/
/*static T_exp unEx(Tr_exp e)
static T_stm unNx(Tr_exp e)
static T_Cx unCx(Tr_exp e)*/
/****************************************************************/

/* translate var */

//EX, 栈上的变量，当前level
//T_exp F_Exp(F_access access, T_exp fp)
Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{
	//要考虑静态链
	T_exp fp = staticlink(level, access->level); //返回fp
	T_exp ex = F_Exp(access->access, fp);
	return Tr_Ex(ex);
}

//EX, 首地址，field数, address of record
Tr_exp Tr_fieldVar(Tr_exp addr, int nth)
{
	T_exp ex = T_Mem(T_Binop(T_plus, unEx(addr), T_Const(nth * F_wordSize)));
	return Tr_Ex(ex);
}

//EX, 首地址，取值数,address of array
//address (i-l)*s + a
Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp index)
{
	//address = addr + index * wordsize
	//默认底限low为0
	T_exp ex = T_Mem(
			T_Binop(T_plus, unEx(addr),
				T_Binop(T_mul, 
					T_Binop(T_minus, unEx(index), T_Const(0)), 
					T_Const(F_wordSize))));
	return Tr_Ex(ex);
}

/****************************************************************/

/* translate exp */

//EX, const 0
Tr_exp Tr_nilExp(void)
{
	return Tr_Ex(T_Const(0));
}

//EX, int值
Tr_exp Tr_intExp(int n)
{
	return Tr_Ex(T_Const(n));
}

//EX, string值
Tr_exp Tr_stringExp(string s)
{
	//添加全局静态变量frags
	//看看什么时候会用到procFrag
	Temp_label label = Temp_newlabel(); //变量label
	F_frag head = F_StringFrag(label, s); 
	frags = F_FragList(head, frags); //更新frags
	return Tr_Ex(T_Name(label));
} 

static T_expList makeCallArgs(Tr_expList params)
{
/*	if (params) {
		return T_ExpList(unEx(params->head), makeCallArgs(params->tail));
	} else {
		return NULL; //终止符
	}*/
	T_expList exps = NULL;
	Tr_expList trexps = params;
	while (trexps) {
		exps = T_ExpList(unEx(trexps->head), exps);
		trexps = trexps->tail;
	}
	return exps;
}

//NX/EX, 函数名，变量序列
//T_exp T_Call(T_exp, T_expList);
//static T_exp staticlink(Tr_level level, Tr_level dest)
//传递静态链作为隐藏参数
//CALL(NAME lf, [sl, e1, e2, …,en])
//Both the level of f and the level of the function calling f are required to calculate s1
Tr_exp Tr_callExp(Tr_level callee, Temp_label func, Tr_expList params, Tr_level caller)
{
	T_exp ex = T_Call(T_Name(func), 
		T_ExpList(staticlink(caller, callee->parent), makeCallArgs(params)));
	return Tr_Ex(ex);
}

//EX, 算术运算，操作符，左操作数，右操作数
Tr_exp Tr_opaluExp(A_oper oper, Tr_exp left, Tr_exp right)
{
	T_exp ex;
	T_exp l = unEx(left), r = unEx(right);

	//type check后，两个操作数都是int
	switch (oper)
	{
		case A_plusOp:
			ex = T_Binop(T_plus, l, r);
			break;
		case A_minusOp:
			ex = T_Binop(T_minus, l, r);
			break;
		case A_timesOp:
			ex = T_Binop(T_mul, l, r);
			break;
		case A_divideOp:
			ex = T_Binop(T_div, l, r);
			break;
	}

	return Tr_Ex(ex); 
}

//CX, 比较运算，操作符，左操作数，右操作数
Tr_exp Tr_opcmpExp(A_oper oper, Tr_exp left, Tr_exp right, bool isStrCmp)
{
	struct Cx cx; //stm, trues, false
	T_exp l, f;

	if (isStrCmp == TRUE){
		
		l = F_externalCall("stringEqual", 
			T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
		f = T_Const(0);

	} else {
		l = unEx(left);
		f = unEx(right);
	}

	//type check后，判等操作可以是int、string、record、array
	//非判等操作可以是int、string
	//建议：删去关于record和array的操作（写不来）
	switch (oper)
	{
		case A_eqOp:
			cx.stm = T_Cjump(T_eq, l, f, NULL, NULL); //==
			break;
		case A_neqOp:
			cx.stm = T_Cjump(T_ne, l, f, NULL, NULL); //!=
			break;
		case A_ltOp:
			cx.stm = T_Cjump(T_lt, l, f, NULL, NULL); //<
			break; 
		case A_leOp:
			cx.stm = T_Cjump(T_le, l, f, NULL, NULL); //<=
			break;
		case A_gtOp:
			cx.stm = T_Cjump(T_gt, l, f, NULL, NULL); //>
			break;
		case A_geOp:
			cx.stm = T_Cjump(T_ge, l, f, NULL, NULL); //>=
			break;
	}

	cx.trues = PatchList(&(cx.stm->u.CJUMP.true), NULL);
	cx.falses = PatchList(&(cx.stm->u.CJUMP.false), NULL);	

	return Tr_Cx(cx.trues, cx.falses, cx.stm);
}

//	A series of MOVE trees can initialize offsets 0, 1w, 2w, …,(n-1)w from r with the translations of expression ei
static T_stm makeRecordFields(Tr_expList fields, Temp_temp r, int n)
{
	//递归分配field空间
	if (fields) {
		return T_Seq(T_Move(T_Binop(T_plus, T_Temp(r), T_Const(n * F_wordSize)), 
					unEx(fields->head)),
				makeRecordFields(fields->tail, r, n-1));
	} else {
		return T_Exp(T_Const(0)); //fields全都分配完
	}
}

//EX, n是field的个数
//	It must be allocated on the heap
//	Call an external memory-allocation function 
//	creates an n-word area 
//	returns the pointer into a new temporary r
Tr_exp Tr_recordExp(Tr_expList fields, int n)
{
	Temp_temp r; //return value
	
	//temp r 的值是 old ptr，即块的起始位置
	T_exp ex = T_Eseq(T_Move(T_Temp(r),
				F_externalCall("malloc",
					T_ExpList(T_Const(n * F_wordSize), NULL))),
			T_Eseq(makeRecordFields(fields, r, n),
			T_Temp(r)));

	return Tr_Ex(ex);
}

//EX, 序列, 返回最后一个表达式产生的结果
Tr_exp Tr_seqExp(Tr_exp e1, Tr_exp e2)
{
	T_exp ex = T_Eseq(unNx(e1), unEx(e2));
	return Tr_Ex(ex);
}

//NX, 条件判断，then
Tr_exp Tr_assignExp(Tr_exp var, Tr_exp exp)
{
	T_stm nx = T_Move(unEx(var), unEx(exp));
	return Tr_Nx(nx);
}

//NX, 条件判断，then
Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then)
{
	struct Cx cx = unCx(test);
	//label: true, false
	Temp_label t = Temp_newlabel(), f = Temp_newlabel();
	doPatch(cx.trues, t);
	doPatch(cx.falses, f);

	T_stm nx = T_Seq(cx.stm,
			T_Seq(T_Label(t),
			T_Seq(unNx(then),
			T_Label(f))));

	return Tr_Nx(nx);
} 

/* if-then-else的数据类型是then和elsee的type */
Tr_exp Tr_ifelseExp(Tr_exp test, Tr_exp then, Tr_exp elsee)
{
	struct Cx cx = unCx(test);
	Temp_temp r = Temp_newtemp();
	//label: true, false
	Temp_label t = Temp_newlabel(), f = Temp_newlabel();
	doPatch(cx.trues, t);
	doPatch(cx.falses, f);

	T_exp ex = T_Eseq(T_Move(T_Temp(r), unEx(then)),
			T_Eseq(cx.stm,
			T_Eseq(T_Label(f),
			T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
			T_Eseq(T_Label(t),
			T_Temp(r))))));

	return Tr_Ex(ex);
}

//NX, 条件判断，body
//T_stm T_Jump(T_exp exp, Temp_labelList labels);
//done label是在参数中提供的
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done)
{
	struct Cx cx = unCx(test);
	//label: loop/body, test, done
	Temp_label l = Temp_newlabel(), t = Temp_newlabel();
	doPatch(cx.trues, l);
	doPatch(cx.falses, done);

	T_stm nx = T_Seq(T_Label(t),
			T_Seq(cx.stm,
			T_Seq(T_Label(l),
			T_Seq(unNx(body),
			T_Seq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)),
			T_Label(done))))));

	return Tr_Nx(nx);
}

//NX, 循环变量i，low值，high值，body
//semant接口需要传i的access
/* if i > limit goto done
  body
  if i == limit goto done
Loop:	i := i + 1
	if i <= limit goto Loop
 done:
*/
Tr_exp Tr_forExp(Tr_exp lo, Tr_exp hi, Tr_exp body, Tr_access access, Tr_level level, Temp_label done)
{
	//DECLARE loop variable, init
	//T_exp ex = F_Exp(access->access, fp);
	Tr_exp i = Tr_simpleVar(access, level);
	Temp_temp limit = Temp_newtemp();
	//label: loop/body
	Temp_label l = Temp_newlabel(), b = Temp_newlabel();

	T_stm nx = T_Seq(T_Move(unEx(i), unEx(lo)),
			T_Seq(T_Move(T_Temp(limit), unEx(hi)),
			T_Seq(T_Cjump(T_gt, unEx(i), T_Temp(limit), done, b),
			T_Seq(T_Label(b),
			T_Seq(unNx(body),
			T_Seq(T_Cjump(T_eq, unEx(i), T_Temp(limit), done, l),
			T_Seq(T_Label(l),
			T_Seq(T_Move(unEx(i), T_Binop(T_plus, unEx(i), T_Const(1))),  
			T_Seq( T_Cjump(T_lt, unEx(i), T_Temp(limit), l, done), 
			T_Label(done))))))))));

	return Tr_Nx(nx);

	/*struct Cx cx = unCx(test);
	Temp_temp r = Temp_newtemp(); //循环变量i
	//label: loop/body, test, done
	Temp_label l = Temp_newlabel(), t = Temp_newlabel(), done = Temp_newlabel();
	doPatch(cx.trues, l);
	doPatch(cx.falses, done);

	T_stm nx = T_Seq(T_Move(T_Temp(r), unEx(lo)),
			T_Seq(T_Label(t),
			T_Seq(cx.stm,
			T_Seq(T_Cjump(T_le, T_Temp(r), unEx(hi), l, done),
			T_Seq(T_Label(l),
			T_Seq(unNx(body),
			T_Seq(T_exp(T_Binop(T_plus, T_Temp(r), T_Const(1))),
			T_Seq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)),
			T_Seq(T_Label(done))))))))));

	return Tr_Nx(nx);*/
}

//NX 跳出循环
//TODO: 这在semant中要怎么对接呢？
Tr_exp Tr_breakExp(Temp_label done)
{
	T_stm nx = T_Jump(T_Name(done), Temp_LabelList(done, NULL));
	return Tr_Nx(nx);
}

//EX, 数组大小，数组初值
//T_exp F_externalCall(string s, T_expList args)
//	详细介绍在ppt里面
//	returns the pointer into a new temporary r
//	initArray(n, b), n:array length b:init value
//	CALL(NAME(Temp_namedlabel(“initArray”)),
//		T_ExpList(n, T_ExpList(b, NULL)))
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init)
{
	Temp_temp r; //return value 
	Temp_temp s = Temp_newtemp(), i = Temp_newtemp();

	T_exp ex = T_Eseq(T_Move(T_Temp(s), unEx(size)),
			T_Eseq(T_Move(T_Temp(i), unEx(init)),
			T_Eseq(T_Move(T_Temp(r), 
				F_externalCall("initArray",
					T_ExpList(T_Temp(s), T_ExpList(T_Temp(i), NULL)))),
			T_Temp(r))));
	
	return Tr_Ex(ex);
}

/****************************************************************/

T_stm Tr_procEntryExit(Tr_exp body, Tr_level level, Tr_accessList formals) {
	/*Temp_temp t = F_RV();*/
	//Temp_temp t = Temp_newtemp();
	return T_Move(T_Temp(F_RV()), unEx(body));
}

/* struct Tr_level_ { F_frame frame; Tr_level parent;}; */
void Tr_functionDec(Tr_exp exp, Tr_level level)
{
	//return T_Move(T_Temp(F_FP()), unEx(stm));
	
	T_stm stm = Tr_procEntryExit(exp, level, level->formals);
	F_frag head = F_ProcFrag(stm, level->frame);
	frags = F_FragList(head, frags);
}

