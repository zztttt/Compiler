/*
 * main.c
 */

#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "absyn.h"
#include "errormsg.h"
#include "temp.h" /* needed by translate.h */
#include "tree.h" /* needed by frame.h */
#include "assem.h"
#include "frame.h" /* needed by translate.h and printfrags prototype */
#include "translate.h"
#include "env.h"
#include "semant.h" /* function prototype for transProg */
#include "canon.h"
#include "prabsyn.h"
#include "printtree.h"
#include "escape.h" 
#include "parse.h"
#include "codegen.h"
#include "regalloc.h"
#include "flowgraph.h"
#include "liveness.h"
#include "graph.h"
#include <string.h>

extern bool anyErrors;
//extern Temp_map F_tempMap;

/*Lab6: complete the function doProc
 * 1. initialize the F_tempMap
 * 2. initialize the register lists (for register allocation)
 * 3. do register allocation
 * 4. output (print) the assembly code of each function
 
 * Uncommenting the following printf can help you debugging.*/
void printStmList (FILE *out, T_stmList stmList) ;

/* print the assembly language instructions to filename.s */
static void doProc(FILE *out, F_frame frame, T_stm body)
{
 AS_proc proc;
 struct RA_result allocation;
 T_stmList stmList;
 AS_instrList iList;
 struct C_block blo;

 //F_tempMap = Temp_empty();

 printf("doProc for function %s:\n", S_name(F_name(frame)));
 printStmList(stdout, T_StmList(body, NULL));
 printf("-------====IR tree=====-----\n");

 stmList = C_linearize(body);
 printStmList(stdout, stmList);
 printf("-------====Linearlized=====-----\n");

 blo = C_basicBlocks(stmList);
 C_stmListList stmLists = blo.stmLists;
 /*for (; stmLists; stmLists = stmLists->tail) {
 	printStmList(stdout, stmLists->head);
	printf("------====Basic block=====-------\n");
 }*/

 stmList = C_traceSchedule(blo);
 //printStmList(stdout, stmList);
 //printf("-------====trace=====-----\n");

 iList  = F_codegen(frame, stmList); /* 9 */
 //AS_printInstrList(stdout, iList, Temp_layerMap(F_tempMap, Temp_name()));
 //printf("----======before RA=======-----\n");

 
/* 11 */
 struct RA_result ra = RA_regAlloc(frame, iList);  

  //Part of TA's implementation. Just for reference.
 
 //AS_rewrite(ra.il, Temp_layerMap(F_tempMap, ra.coloring));
 proc =	F_procEntryExit3(frame, ra.il);

 string procName = S_name(F_name(frame));
 fprintf(out, ".text\n");
 fprintf(out, ".globl %s\n", procName);
 fprintf(out, ".type %s, @function\n", procName);
 fprintf(out, "%s:\n", procName);

 
 //fprintf(stdout, "%s:\n", Temp_labelstring(F_name(frame)));
 //prologue
 fprintf(out, "%s", proc->prolog);
 AS_printInstrList (out, proc->body,
                       Temp_layerMap(F_tempMap, ra.coloring));
 fprintf(out, "%s", proc->epilog);
 //fprintf(out, "END %s\n\n", Temp_labelstring(F_name(frame)));
 
}


void doStr(FILE *out, Temp_label label, string str) {
	fprintf(out, ".section .rodata\n");
	fprintf(out, "%s:\n", S_name(label));

	int length = strlen(str);
  fprintf(out, ".int %d\n", length);

	//it may contains zeros in the middle of string. To keep this work, we need to print all the charactors instead of using fprintf(str)
	fprintf(out, ".string \"");
	
  char ch = *str;
  while(ch){
    if (ch == '\n') fprintf(out, "\\n");
    else if(ch == '\t') fprintf(out, "\\t");
    else fprintf(out, "%c", ch);
    str++;
    ch = *str;
  }
	
	fprintf(out, "\"\n");

	//fprintf(out, ".string \"%s\"\n", str);
}

int main(int argc, string *argv)
{
 A_exp absyn_root;
 S_table base_env, base_tenv;
 F_fragList frags;
 char outfile[100];
 FILE *out = stdout;

 if (argc==2) {
   absyn_root = parse(argv[1]);
   if (!absyn_root)
     return 1;
     
#if 0
   pr_exp(out, absyn_root, 0); /* print absyn data structure */
   fprintf(out, "\n");
#endif

   //Lab 6: escape analysis
   //If you have implemented escape analysis, uncomment this
   Esc_findEscape(absyn_root); /* set varDec's escape field */
   F_tempMap = Temp_empty();
   frags = SEM_transProg(absyn_root);
   if (anyErrors) return 1; /* don't continue */

   /* convert the filename */
   sprintf(outfile, "%s.s", argv[1]);
   out = fopen(outfile, "w");
   /* Chapter 8, 9, 10, 11 & 12 */
   int cnt = 0;
   for (;frags;frags=frags->tail){   
     if (frags->head->kind == F_procFrag) {
       doProc(out, frags->head->u.proc.frame, frags->head->u.proc.body);
	    }
     else if (frags->head->kind == F_stringFrag) {
	    doStr(out, frags->head->u.stringg.label, frags->head->u.stringg.str);
     }
   }
   fclose(out);
   return 0;
 }
 EM_error(0,"usage: tiger file.tig");
 return 1;
}


#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"

/* local function prototype */
static void pr_tree_exp(FILE *out, T_exp exp, int d);

static void indent(FILE *out, int d) {
 int i;
 for (i = 0; i <= d; i++) fprintf(out, " ");
}

static char bin_oper[][12] = {
   "PLUS", "MINUS", "TIMES", "DIVIDE", 
   "AND", "OR", "LSHIFT", "RSHIFT", "ARSHIFT", "XOR"};

static char rel_oper[][12] = {
  "EQ", "NE", "LT", "GT", "LE", "GE", "ULT", "ULE", "UGT", "UGE"};
 
static void pr_stm(FILE *out, T_stm stm, int d)
{
  switch (stm->kind) {
  case T_SEQ:
    indent(out,d);
    fprintf(out, "SEQ(\n"); pr_stm(out, stm->u.SEQ.left,d+1);  fprintf(out, ",\n"); 
    pr_stm(out, stm->u.SEQ.right,d+1); fprintf(out, ")");
    break;
  case T_LABEL:
    indent(out,d); fprintf(out, "LABEL %s", S_name(stm->u.LABEL));
    break;
  case T_JUMP:
    indent(out,d); fprintf(out, "JUMP(\n"); pr_tree_exp(out, stm->u.JUMP.exp,d+1); 
    fprintf(out, ")");
    break;
  case T_CJUMP:
    indent(out,d); fprintf(out, "CJUMP(%s,\n", rel_oper[stm->u.CJUMP.op]);
    pr_tree_exp(out, stm->u.CJUMP.left,d+1); fprintf(out, ",\n"); 
    pr_tree_exp(out, stm->u.CJUMP.right,d+1); fprintf(out, ",\n");
    indent(out,d+1); fprintf(out, "%s,", S_name(stm->u.CJUMP.true));
    fprintf(out, "%s", S_name(stm->u.CJUMP.false)); fprintf(out, ")");
    break;
  case T_MOVE:
    indent(out,d); fprintf(out, "MOVE(\n"); pr_tree_exp(out, stm->u.MOVE.dst,d+1); 
    fprintf(out, ",\n");
    pr_tree_exp(out, stm->u.MOVE.src,d+1); fprintf(out, ")");
    break;
  case T_EXP:
    indent(out,d); fprintf(out, "EXP(\n"); pr_tree_exp(out, stm->u.EXP,d+1); 
    fprintf(out, ")");
    break;
  }
}

static void pr_tree_exp(FILE *out, T_exp exp, int d)
{
  switch (exp->kind) {
  case T_BINOP:
    indent(out,d); fprintf(out, "BINOP(%s,\n", bin_oper[exp->u.BINOP.op]); 
    pr_tree_exp(out, exp->u.BINOP.left,d+1); fprintf(out, ",\n"); 
    pr_tree_exp(out, exp->u.BINOP.right,d+1); fprintf(out, ")");
    break;
  case T_MEM:
    indent(out,d); fprintf(out, "MEM");
    fprintf(out, "(\n"); pr_tree_exp(out, exp->u.MEM,d+1); fprintf(out, ")");
    break;
  case T_TEMP:
    indent(out,d); fprintf(out, "TEMP t%s", 
			   Temp_look(Temp_name(), exp->u.TEMP));
    break;
  case T_ESEQ:
    indent(out,d); fprintf(out, "ESEQ(\n"); pr_stm(out, exp->u.ESEQ.stm,d+1); 
    fprintf(out, ",\n");
    pr_tree_exp(out, exp->u.ESEQ.exp,d+1); fprintf(out, ")");
    break;
  case T_NAME:
    indent(out,d); fprintf(out, "NAME %s", S_name(exp->u.NAME));
    break;
  case T_CONST:
    indent(out,d); fprintf(out, "CONST %d", exp->u.CONST);
    break;
  case T_CALL:
    {T_expList args = exp->u.CALL.args;
     indent(out,d); fprintf(out, "CALL(\n"); pr_tree_exp(out, exp->u.CALL.fun,d+1);
     for (;args; args=args->tail) {
       fprintf(out, ",\n"); pr_tree_exp(out, args->head,d+2);
     }
     fprintf(out, ")");
     break;
   }
  } /* end of switch */
}

void printStmList (FILE *out, T_stmList stmList) 
{
  for (; stmList; stmList=stmList->tail) {
    pr_stm(out, stmList->head,0); fprintf(out, "\n");
  }
}
