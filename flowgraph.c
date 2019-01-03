#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
	AS_instr ins = G_nodeInfo(n);
	switch(ins->kind){
		case I_OPER:
			return ins->u.OPER.dst;
		case I_MOVE:
			return ins->u.MOVE.dst;
		default:
			//should not arrive here
			assert(0);
	}
}

Temp_tempList FG_use(G_node n) {
	AS_instr ins = G_nodeInfo(n);
	switch(ins->kind){
		case I_OPER:
			return ins->u.OPER.src;
		case I_MOVE:
			return ins->u.MOVE.src;
		default:
			//should not arrive here
			assert(0);
	}
}

bool FG_isMove(G_node n) {
	AS_instr ins = G_nodeInfo(n);
	return ins->kind == I_MOVE && strstr(ins->u.MOVE.assem,"movq `s0, `d0");
}

void FG_showInfo(void *p){
	AS_instr ins = p;
	AS_print(stdout, ins, Temp_layerMap(F_tempMap, Temp_name()));
}

/* GlowGraph -- [node -> As_inst]*/
G_graph FG_AssemFlowGraph(AS_instrList il) {
	G_graph g = G_Graph();
	Temp_labelList labels = NULL;
	G_nodeList nodes = NULL;

	AS_targetsList waits = NULL;
	G_nodeList nodes_as = NULL;
	
	bool prevLab = FALSE;
	Temp_labelList lab = NULL;
	G_node prevNode = NULL;
	//generate flow graph
	for(AS_instrList ls=il; ls; ls=ls->tail){
		AS_instr ins = ls->head;
		switch(ins->kind){
			case I_LABEL:{
				prevLab = TRUE;
				lab = Temp_LabelList(ins->u.LABEL.label, lab); 
				printf("END I_LABEL==================\n");
				break;
			}
			case I_MOVE:{
				Temp_tempList dst = ins->u.MOVE.dst;
				Temp_tempList src = ins->u.MOVE.src;
				string ass = ins->u.MOVE.assem;		
				printf("%s\n", ass);
				printf("END I_MOVE===================\n");		
				if(strstr(ass,"movq `s0, `d0")){
					if(Temp_int(dst->head) == Temp_int(src->head))
						break;
				} 
			}
			case I_OPER:{
				G_node node = G_Node(g, ins);
				if(prevNode){
					G_addEdge(prevNode, node);
				}
				if(prevLab){
					for(;lab;lab=lab->tail){
						labels = Temp_LabelList(lab->head, labels);
						nodes = G_NodeList(node, nodes);
					}
					prevLab = FALSE;
				}

				prevNode = node;
				if(ins->u.OPER.jumps){
					if(strstr(ins->u.OPER.assem, "jmp"))
						prevNode = NULL;
					waits = AS_TargetsList(ins->u.OPER.jumps, waits);
					nodes_as = G_NodeList(node, nodes_as);
				}
				printf("END I_OPER==================\n");
				break;
			}
			default:assert(0);
		}
	}
	//fill jump->label
	AS_targetsList p = waits;
	G_nodeList as_node = nodes_as;
	for(; p && as_node; p = p->tail, as_node = as_node->tail){
		for(Temp_labelList t = p->head->labels; t; t=t->tail){
			Temp_label label = t->head;
			//find label
			G_node succ = NULL;
			Temp_labelList t = labels;
			G_nodeList n = nodes;
			for(; t && n; t = t->tail, n = n->tail){
				Temp_label lab = t->head;
				if(lab == label){
					succ = n->head;
				}
			}
			if(!succ){
				EM_impossible("vanishing jump label %s", Temp_labelstring(label));
				assert(0);
			}
			G_addEdge(as_node->head, succ);
		}
	}
	FG_showInfo(il);
	return g;
}
