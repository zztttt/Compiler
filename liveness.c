#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"


//data structure
typedef struct liveInfo_ *liveInfo;
struct liveInfo_{
	Temp_tempList in;
	Temp_tempList out;
};

liveInfo LiveInfo(Temp_tempList in, Temp_tempList out){
	liveInfo i = checked_malloc(sizeof(*i));
	i->in = in;
	i->out = out;
	return i;
}

nodeInfo NodeInfo(Temp_temp t, int d){
	nodeInfo i = checked_malloc(sizeof(*i));
	i->degree = d;
	i->reg = t;
	i->alias = NULL;
	return i;
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

//helper
static int pool[100];
static int cnt;
static bool inPool(Temp_temp t){	
	int mark = Temp_int(t);
	for(int i=0;i<cnt;i++){
		if(pool[i] == mark){
			return TRUE;
		}
	}
	pool[cnt] = mark;
	cnt += 1;
	return FALSE;
}

//procedure
Temp_temp Live_gtemp(G_node n) {
	//your code here.
	nodeInfo p = G_nodeInfo(n);
	Temp_temp t = p->reg;
	return t;
}

void Live_showInfo(void *p){
	nodeInfo t = p;
	Temp_map map = Temp_layerMap(F_tempMap, Temp_name());
	printf("%s\t",Temp_look(map, t->reg));
}

void Live_prMovs(Live_moveList ml){
	Temp_map map = Temp_layerMap(F_tempMap, Temp_name());
	for(;ml;ml=ml->tail){
		printf("%s -> %s\n", Temp_look(map, Live_gtemp( ml->src)), Temp_look(map, Live_gtemp( ml->dst)));
	}
}
static void makeLivenessGraph(TAB_table tn, G_table liveT, G_graph flow, G_graph* cfGraph, G_nodeList* Points){
	//create empty graph without in/out and edge
	cnt = 0;
	for(G_nodeList nodes = G_nodes(flow);nodes;nodes=nodes->tail){
		G_node fnode = nodes->head;
		for(Temp_tempList defs = FG_def(fnode); defs; defs = defs->tail){
			Temp_temp t = defs->head;
			if(!inPool(t)){
				G_node cfnode = G_Node(*cfGraph, NodeInfo(t,0));
				TAB_enter(tn, t, cfnode);
			}
		}
		for(Temp_tempList uses = FG_use(fnode); uses; uses = uses->tail){
			Temp_temp t = uses->head;
			if(!inPool(t)){
				G_node cfnode = G_Node(*cfGraph, NodeInfo(t,0));
				TAB_enter(tn, t, cfnode);
			}
		}
		G_enter(liveT, fnode, LiveInfo(NULL, NULL));
		*Points = G_NodeList(fnode, *Points);
	}
	//add in/out
	bool stable = FALSE;
	while(!stable){
		stable = TRUE;
		for(G_nodeList nl = *Points; nl; nl = nl->tail){
			G_node fnode = nl->head;

			liveInfo old = G_look(liveT, fnode);
			Temp_tempList out = old->out;
			for(G_nodeList succs = G_succ(fnode); succs; succs = succs->tail){
				G_node succ = succs->head;
				liveInfo tmp = G_look(liveT, succ);
				out = Temp_UnionCombine(out, tmp->in);
			}
			Temp_tempList in = Temp_Union(FG_use(fnode), Temp_Minus(out, FG_def(fnode)));
			if(!Temp_Equal(in, old->in) || !Temp_Equal(out, old->out)){
				stable = FALSE;
			}
			G_enter(liveT, fnode, LiveInfo(in, out));
		}
	}
}

/*
 * 目标：make conflict graph 
 * 将所有结点加入tempTab中
 * 对于任何对变量a定值的非传送指令，以及在该指令处是出口活跃的变量b1...bn，添加冲突边(a,b1)...(a,bn)
 * 对于传送指令a<-c，如果变量b1...bn在该指令出口处是活跃的，则对每一个不同于c的bi添加冲突边(a,b1)...(a,bn)
 * templist的差操作t1-t2, Temp_tempList subTempList(Temp_tempList t1, Temp_tempList t2) 
 */
static void makeConflictGraph(TAB_table tn, G_table liveT, Live_moveList* movs, G_nodeList* Points){
	for(G_nodeList np = *Points;np;np=np->tail){
		G_node fnode = np->head;

		liveInfo info = G_look(liveT, fnode);
		Temp_tempList live = info->out;

		//judge is move
		if(FG_isMove(fnode)){
			live = Temp_Minus(live, FG_use(fnode));

			Temp_temp dst = FG_def(fnode)->head;
			G_node d = TAB_look(tn, dst);
			Temp_temp src = FG_use(fnode)->head;
			G_node s = TAB_look(tn, src);

			*movs = Live_MoveList(s, d, *movs);
		}

		//add conflicts 
		Temp_tempList defs = FG_def(fnode);
		//out and defs
		live = Temp_Union(live, defs);
		for(Temp_tempList p1 = defs; p1 ; p1 = p1->tail){
			G_node cf1 = TAB_look(tn, p1->head);
			for(Temp_tempList p2 = live; p2 ; p2 = p2->tail){
				G_node cf2 = TAB_look(tn, p2->head);
				/* Tell if there is an edge from "from" to "to" */
				if(G_goesTo(cf2, cf1) || cf1 == cf2)
					continue;
				G_addEdge(cf1, cf2);
			}
		}

	}
}

/* Conflict graph -- [node -> temp]*/
struct Live_graph Live_liveness(G_graph flow) {
	struct Live_graph lg;

	//tables to store datas
	G_graph cfGraph = G_Graph();
	TAB_table tn = TAB_empty();
	G_table liveT = G_empty();
	
	G_nodeList Points = NULL;
	Live_moveList movs = NULL;	

	//make liveness graph with no edge
	makeLivenessGraph(tn, liveT, flow, &cfGraph, &Points);
	
	//add conflict edges according to [in]
	makeConflictGraph(tn, liveT, &movs, &Points);
	
	lg.graph = cfGraph;
	lg.moves = movs;

	return lg;
}


