%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "errormsg.h"
#include "absyn.h"
#include "y.tab.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/
static int comment_level = 0;
/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences
 * translated into their meaning.
 */
 #include <ctype.h>
 #include <stdio.h>
 #include <fcntl.h>

char *getstr(const char *str)
{
    //printf("strlen:%d\n",(int)strlen(str));
    char *result = (char *)malloc(yyleng + 1);
    size_t cur = 1, len = 0;
    char d[3];
    int digit;
    while(str[cur] != '"') {
        if (str[cur] == '\\' ) {
            cur++;//predict!!!!!!!!!!!
            if(isdigit(str[cur])){
                d[0] = str[cur];
                d[1] = str[cur+1];
                d[2] = str[cur+2];
                digit = atoi(d);
                //printf("d[]:%s\n", d);
                //printf("digit:%d\n", digit);
                char tmp = (char)digit;
                result[len++] = tmp;
                cur += 3;
            }
            else if(str[cur] == '^'){
                //printf("^\n");
                //printf("%d\n", str[cur+1]);
                char tmp = str[cur+1];//ABC......
                //printf("%d\n", tmp);
                tmp = tmp - 64;//transfer A->^A
                result[len++] = tmp;
                cur += 2;
            }
            else if(str[cur] == '\n'){
                cur++;
                while(str[cur] == ' ' || str[cur] == '\t'){
                    cur++;
                }
                //deal with '\?' which appears at the second line
                if(str[cur] == '\\'){
                    result[len++] = str[cur+1];
                    cur +=2 ;
                }
            }
            else{
                switch(str[cur]) {
                case 'n': result[len++] = '\n';break;
                case 't': result[len++] = '\t'; break;
                case '\\': result[len++] = '\\'; break;
                case '\"': result[len++] = '\"'; break;
                default:break;
                }
                cur++;
            }
        }
        else {
            result[len++] = str[cur++];
        }
    }
    if (len == 0) {
        free(result);
        return "";
    }
    result[len] = '\0';
    return result;
}

%}
/* You can add lex definitions here. */
%Start COMMENT


%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 
"/*" { adjust(), ++comment_level; BEGIN COMMENT; }
<COMMENT>\n { adjust(); EM_newline(); }
<COMMENT>[^\*\/]* { adjust(); }
<COMMENT>"*" { adjust(); }
<COMMENT>"/" { adjust(); }
<COMMENT>"*/" {
    adjust();
    --comment_level;
    if (comment_level == 0) BEGIN 0;
    else if (comment_level < 0) {
        comment_level = 0;
        REJECT;
    }
}

[\ \t]* { adjust(); }
"\n" {adjust(); EM_newline(); continue;}
let { adjust(); return LET; }
in { adjust(); return IN; }
var { adjust(); return VAR; }
if { adjust(); return IF; }
then { adjust(); return THEN; }
else { adjust(); return ELSE; }
do { adjust(); return DO; }
while { adjust(); return WHILE; }
end { adjust(); return END; }
type { adjust(); return TYPE; }
nil { adjust(); return NIL; }
break { adjust(); return BREAK; }
function { adjust(); return FUNCTION; }
of { adjust(); return OF; }
array { adjust(); return ARRAY; }
to { adjust(); return TO; }
for { adjust(); return FOR;}
\"([^\"]|\\\")*\" { adjust(); yylval.sval = getstr(yytext); return STRING; }
[0-9]* { adjust(); yylval.ival = atoi(yytext); return INT; }
[_a-zA-Z][_0-9a-zA-Z]* { adjust(); yylval.sval = String(yytext); return ID; }
"<=" { adjust(); return LE; }
"<" { adjust(); return LT; }
">=" { adjust(); return GE; }
">" { adjust(); return GT; }
"=" { adjust(); return EQ; }
"<>" { adjust(); return NEQ; }
":=" { adjust(); return ASSIGN; }

"," { adjust(); return COMMA; }
";" { adjust(); return SEMICOLON; }
":" { adjust(); return COLON; }
"." { adjust(); return DOT; }
"*" { adjust(); return TIMES; }
"/" { adjust(); return DIVIDE; }
"+" { adjust(); return PLUS; }
"-" { adjust(); return MINUS; }

"{" { adjust(); return LBRACE; }
"}" { adjust(); return RBRACE; }
"(" { adjust(); return LPAREN; }
")" { adjust(); return RPAREN; }
"&" { adjust(); return AND; }
"|" { adjust(); return OR; }
"[" { adjust(); return LBRACK; }
"]" { adjust(); return RBRACK; }
<<EOF>> { adjust(); yyterminate(); }
. { adjust(); }
