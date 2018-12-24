#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

#define CODEGEN_DEBUG 1
#define log(...)\
    if(CODEGEN_DEBUG)\
        fprintf(stdout, __VA_ARGS__);

//Lab 6: put your code here
AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    log("F_codegen\n");
}
