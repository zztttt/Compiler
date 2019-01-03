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

nodeInfo NodeInfo(Temp_temp t, int d, enum State s){
	nodeInfo i = checked_malloc(sizeof(*i));
	i->degree = d;
	i->reg = t;
	i->stat = s;
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
static void genGraph(G_table tn, G_table liveT, G_graph flow, G_graph* cfGraph, G_nodeList* revFlow){
	//cfnode -> temp
	cnt = 0;
	for(G_nodeList nodes=G_nodes(flow);nodes;nodes=nodes->tail){
		G_node fnode = nodes->head;
		for(Temp_tempList tp = FG_def(fnode);tp;tp=tp->tail){
			Temp_temp t = tp->head;
			if(!inPool(t)){
				G_node cfnode = G_Node(*cfGraph, NodeInfo(t,0,0));
				G_enter(tn, t, cfnode);
			}
		}
		for(Temp_tempList tp = FG_use(fnode);tp;tp=tp->tail){
			Temp_temp t = tp->head;
			if(!inPool(t)){
				G_node cfnode = G_Node(*cfGraph,NodeInfo(t,0,0));
				G_enter(tn, t, cfnode);
			}
		}
		G_enter(liveT, fnode, LiveInfo(NULL, NULL));
		*revFlow = G_NodeList(fnode, *revFlow);
	}
}
static void loopAnalyse(G_table liveT, G_nodeList* revFlow){
	bool stable = FALSE;
	while(!stable){
		stable = TRUE;
		for(G_nodeList np = *revFlow;np;np=np->tail){
			G_node fnode = np->head;

			liveInfo old = G_look(liveT, fnode);
			assert(old);

			Temp_tempList out = old->out;
			for(G_nodeList sp=G_succ(fnode);sp;sp=sp->tail){
				G_node succ = sp->head;
				liveInfo tmp = G_look(liveT, succ);
				assert(tmp);
				out = Temp_UnionCombine(out, tmp->in);
			}
			Temp_tempList in = Temp_Union(FG_use(fnode), Temp_Minus(out, FG_def(fnode)));
			//Temp_tempList in = Minus(Union(out, FG_use(fnode)), FG_def(fnode));

			if(!Temp_Equal(in, old->in) || !Temp_Equal(out, old->out)){
				stable = FALSE;
			}

			G_enter(liveT, fnode, LiveInfo(in, out));
		}
	}
}
static void addConf(G_table tn, G_table liveT, G_table movs, G_nodeList* revFlow){
	for(G_nodeList np = *revFlow;np;np=np->tail){
		G_node fnode = np->head;

		liveInfo info = G_look(liveT, fnode);
		Temp_tempList live = info->out;

		//move
		if(FG_isMove(fnode)){
			live = Temp_Minus(live, FG_use(fnode));

			Temp_temp dst = FG_def(fnode)->head;
			G_node d = G_look(tn, dst);
			Temp_temp src = FG_use(fnode)->head;
			G_node s = G_look(tn, src);

			movs = Live_MoveList(s, d, movs);
		}

		//add conflicts 
		Temp_tempList def = FG_def(fnode);
		live = Temp_Union(live, def);
		for(Temp_tempList p1=def;p1;p1=p1->tail){
			G_node cf1 = G_look(tn, p1->head);
			for(Temp_tempList p2=live;p2;p2=p2->tail){
				G_node cf2 = G_look(tn, p2->head);
				if(G_goesTo(cf2, cf1) || cf1 == cf2)continue;
				G_addEdge(cf1, cf2);
			}
		}

	}
}

/* Conflict graph -- [node -> temp]*/
struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;

	G_graph cfGraph = G_Graph();
	G_nodeList revFlow = NULL;
	G_table liveT = G_empty();
	//[temp:cfnode]
	G_table tn = G_empty();
	Live_moveList movs = NULL;	

	//generate a empty conflict graph with no edge in it 
	genGraph(tn, liveT, flow, &cfGraph, &revFlow);
	
	//loop find in/out
	loopAnalyse(liveT, &revFlow);
	
	//add conflict edges according to [in]
	addConf(tn, liveT, movs, &revFlow);
	
	lg.graph = cfGraph;
	lg.moves = movs;

	return lg;
}


