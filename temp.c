/*
 * temp.c - functions to create and manipulate temporary variables which are
 *          used in the IR tree representation before it has been determined
 *          which variables are to go into registers.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"

struct Temp_temp_ {int num;};

int Temp_int(Temp_temp t)
{
	return t->num;
}

string Temp_labelstring(Temp_label s)
{return S_name(s);
}

static int labels = 0;

Temp_label Temp_newlabel(void)
{char buf[100];
 sprintf(buf,".L%d",labels++);
 return Temp_namedlabel(String(buf));
}

/* The label will be created only if it is not found. */
Temp_label Temp_namedlabel(string s)
{return S_Symbol(s);
}

static int temps = 100;

Temp_temp Temp_newtemp(void)
{Temp_temp p = (Temp_temp) checked_malloc(sizeof (*p));
 p->num=temps++;
 {char r[16];
  sprintf(r, "%d", p->num);
  Temp_enter(Temp_name(), p, String(r));
 }
 return p;
}



struct Temp_map_ {TAB_table tab; Temp_map under;};


Temp_map Temp_name(void) {
 static Temp_map m = NULL;
 if (!m) m=Temp_empty();
 return m;
}

Temp_map newMap(TAB_table tab, Temp_map under) {
  Temp_map m = checked_malloc(sizeof(*m));
  m->tab=tab;
  m->under=under;
  return m;
}

Temp_map Temp_empty(void) {
  return newMap(TAB_empty(), NULL);
}

Temp_map Temp_layerMap(Temp_map over, Temp_map under) {
  if (over==NULL)
      return under;
  else return newMap(over->tab, Temp_layerMap(over->under, under));
}

void Temp_enter(Temp_map m, Temp_temp t, string s) {
  assert(m && m->tab);
  TAB_enter(m->tab,t,s);
}

string Temp_look(Temp_map m, Temp_temp t) {
  string s;
  assert(m && m->tab);
  s = TAB_look(m->tab, t);
  if (s) return s;
  else if (m->under) return Temp_look(m->under, t);
  else return NULL;
}

Temp_tempList Temp_TempList(Temp_temp h, Temp_tempList t) 
{Temp_tempList p = (Temp_tempList) checked_malloc(sizeof (*p));
 p->head=h; p->tail=t;
 return p;
}

Temp_labelList Temp_LabelList(Temp_label h, Temp_labelList t)
{Temp_labelList p = (Temp_labelList) checked_malloc(sizeof (*p));
 p->head=h; p->tail=t;
 return p;
}

static FILE *outfile;
void showit(Temp_temp t, string r) {
  fprintf(outfile, "t%d -> %s\n", t->num, r);
}

void Temp_dumpMap(FILE *out, Temp_map m) {
  outfile=out;
  TAB_dump(m->tab,(void (*)(void *, void*))showit);
  if (m->under) {
     fprintf(out,"---------\n");
     Temp_dumpMap(out,m->under);
  }
}

//my helper funcs

Temp_tempList Temp_catList(Temp_tempList a, Temp_tempList b){
    Temp_tempList li = NULL;
    for(Temp_tempList p=a;p;p=p->tail){
        li = Temp_TempList(p->head,li);
    }
    for(Temp_tempList p=b;p;p=p->tail){
        li = Temp_TempList(p->head,li);
    }
    return li;
}

bool Temp_inList(Temp_tempList list, Temp_temp t){
	for(;list;list=list->tail){
		Temp_temp tt = list->head;
		if(Temp_int(tt) == Temp_int(t)){
			return TRUE;
		}
	}
	return FALSE;
}


Temp_tempList Temp_Union(Temp_tempList A, Temp_tempList B){
	Temp_tempList list = NULL;
	for(;A;A=A->tail){
		Temp_temp tt = A->head;
		list = Temp_TempList(tt, list);
	}
	//Temp_tempList list = A;
	for(;B;B=B->tail){
		Temp_temp tt = B->head;
		if(!Temp_inList(A, tt)){
			list = Temp_TempList(tt, list);
		}
	}
	return list;
}
Temp_tempList Temp_UnionCombine(Temp_tempList A, Temp_tempList B){
  Temp_tempList list = A;
	for(;B;B=B->tail){
		Temp_temp tt = B->head;
		if(!Temp_inList(A, tt)){
			list = Temp_TempList(tt, list);
		}
	}
	return list;
}
Temp_tempList Temp_Minus(Temp_tempList A, Temp_tempList B){
	Temp_tempList list = NULL;
	for(;A;A=A->tail){
		Temp_temp tt = A->head;
		if(!Temp_inList(B, tt)){
			list = Temp_TempList(tt, list);
		}
	}
	return list;
}
bool Temp_Equal(Temp_tempList A, Temp_tempList B){
	if(Temp_Minus(A,B)==NULL && Temp_Minus(B,A)==NULL){
		return TRUE;
	}
	return FALSE;
}

void Temp_replace(Temp_temp old, Temp_temp fresh, Temp_tempList li){
  for(Temp_tempList p=li;p;p=p->tail){
    if(p->head == old) 
      p->head=fresh;
  }
}