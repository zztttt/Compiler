#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/
static int F_wordSize = 8;

//help functions
static F_access InFrame(int offset)
{
	F_access access = (F_access)checked_malloc(sizeof(*access));
	access->kind = inFrame;
	access->u.offset = offset;
	return access;
}

static F_access InReg(Temp_temp reg)
{
	F_access access = (F_access)checked_malloc(sizeof(*access));
	access->kind = inReg;
	access->u.reg = reg;
	return access;
}

static F_accessList F_makeFormals(U_boolList formals, int offset) {
        if (formals) {
                return F_AccessList(InFrame(offset), 
                    F_makeFormals(formals->tail, offset + F_wordSize));
        } else {
                return NULL;
        }
}

//get functions
Temp_label F_name(F_frame frame) {
    return frame->name;
}

F_accessList F_formals(F_frame frame) {
    return frame->formals;
}

T_exp F_Exp(F_access access, T_exp frame_ptr) {
    switch (access->kind) {
        case inFrame://for variable in stack, calculate with static list
            return T_Mem(T_Binop(T_plus, frame_ptr, T_Const(access->u.offset)));
        case inReg://for variable in reg just return T_Temp(...)
             return T_Temp(access->u.reg);
        default:
            assert(0);
    }
}

T_exp F_externalCall(string s, T_expList args) {
    return T_Call(T_Name(Temp_namedlabel(s)), args);
}



//provided functions
F_frame F_newFrame(Temp_label name, U_boolList formals) {
    F_frame frame = checked_malloc(sizeof(*frame));

    frame->name = name;
    frame->formals = F_makeFormals(formals, F_wordSize);
    frame->size = 0;

    return frame;
}

//if is escaped, store it in FRAME; otherwise in REG
F_access F_allocLocal(F_frame frame, bool escape) {
    F_access access;
    if (escape) {
        //???
		frame->size++;
		int offset = -(frame->size * F_wordSize);
		access = InFrame(offset);
	} else {
		access = InReg(Temp_newtemp());
	}
    return access;
}
//constructor
F_accessList F_AccessList(F_access head, F_accessList tail) {
    F_accessList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;
    return list;
}

F_fragList F_FragList(F_frag head, F_fragList tail) {
    F_fragList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;
    return list;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
    F_frag frag = checked_malloc(sizeof(*frag));
    frag->kind = F_procFrag;
    frag->u.proc.body = body;
    frag->u.proc.frame = frame;
    return frag;
}

F_frag F_StringFrag(Temp_label label, string str) {
    F_frag frag = checked_malloc(sizeof(*frag));
    frag->kind = F_stringFrag;
    frag->u.stringg.label = label;
    frag->u.stringg.str = str;
    return frag;
}

Temp_temp F_FP() {
    return Temp_newtemp();
}

// TODO: identify all the RVs
Temp_temp F_RV() {
    return Temp_newtemp();
}

Temp_temp F_SP(void){ 
    return Temp_newtemp(); 
}

Temp_temp F_Zero(void){ 
    return Temp_newtemp(); 
}