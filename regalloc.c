#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"

#define REGALLOC_DEBUG 0

#define log(...)\
	if(REGALLOC_DEBUG)\
		fprintf(stdout, __VA_ARGS__);

const int REG_NUM = 16;

//机器寄存器集合，每个寄存器都预先指派了一种颜色
static G_nodeList precolored = NULL;
//已成功着色的结点集合
static G_nodeList coloredNode = NULL;
//在本轮中要被溢出的结点集合
static G_nodeList spilledNode = NULL;
//已合并的寄存器集合
static G_nodeList coalescedNode = NULL;

//高度数的结点表
static G_nodeList spillWorkList = NULL;
//低度数的与传送结点有关的表
static G_nodeList freezeWorkList = NULL;
//低度数的与传送无关的结点表
static G_nodeList simplifyWorkList = NULL;

//有可能合并的传送指令集合
static Live_moveList worklistMoves = NULL;
//已经合并的传送指令集合
static Live_moveList coalescedMoves = NULL;
//不再考虑合并的传送指令集合
static Live_moveList frozenMoves = NULL;
//源操作数和目标操作数冲突的传送指令集合
static Live_moveList constrainedMoves = NULL;
//还未做好合并准备的传送指令集合
static Live_moveList activeMoves = NULL;


//stack
static G_nodeList SelectStack;

//helper
bool inMoveList(G_node node, Live_moveList list){
    for(;list;list = list->tail){
        if(node == list->dst || node == list->src){
            return TRUE;
        }
    }
    return FALSE;
}

Live_moveList RMrelatedMovs(G_node node, Live_moveList list){
    Live_moveList li = NULL;
    Live_moveList last = NULL;
    for(;list;list = list->tail){
        if(node == list->src || node == list->dst){
            //save live_movelist
            li = Live_MoveList(list->src, list->dst, li);
            if(last){
                last->tail = list->tail;
                list = last;
            }
        }
        last = list;
    }
    return li;
}

void RA_showInfo(void *p){
	nodeInfo t = p;
	Temp_map map = Temp_layerMap(COL_map(),Temp_layerMap(F_tempMap, Temp_name()));
	if(t->alias){
		//printf("%s\t stat:%d\tdegree:%d\talias:%s\t",Temp_look(map, t->reg), t->stat, t->degree,Temp_look(map, Live_gtemp(t->alias)));
	}
	else
		printf("%s\tdegree:%d\t",Temp_look(map, t->reg), t->degree);
}
static void clear(){
	log("clear\n");
	//node set
	precolored = NULL;
	coloredNode = NULL;
	spilledNode = NULL;
	coalescedNode = NULL;

	//nodeWorklist
	spillWorkList = NULL;
	freezeWorkList = NULL;
	simplifyWorkList = NULL;

	//moveList
	worklistMoves = NULL;
	coalescedMoves = NULL;
	frozenMoves = NULL;
	constrainedMoves = NULL;
	activeMoves = NULL;

	SelectStack = NULL;
}

//function  MoveRelated(n)
static bool MoveRelated(G_node node){
	//moveList[n] ^ (activeMoves + worklistMoves) != {}
	Live_moveList list1 = worklistMoves;
	Live_moveList list2 = activeMoves;
	bool res = FALSE;
	for(;list1;list1 = list1->tail){
        if(node == list1->dst || node == list1->src){
            res = TRUE;
        }
    }
	for(;list2;list2 = list2->tail){
        if(node == list2->dst || node == list2->src){
            res = TRUE;
        }
    }
    return res;
}

//function Adjacent(n)
static G_nodeList Adjacent(G_node node){
	log("Adjacent\n");
	//adjList[n]\(selectStack + coaleseedNodes)
	G_nodeList adj = G_adj(node);
	G_nodeList locked = G_UnionList(SelectStack, coalescedNode);
	return G_MinusList(adj, locked);
}

//procedure EnableMoves
static void EnableMoves(G_nodeList nodes){
	log("EnableMoves\n");
	//for n in nodes
	for(;nodes;nodes=nodes->tail){
		G_node node = nodes->head;
		//for m in NodeMoves(n)
		Live_moveList rel = RMrelatedMovs(node, activeMoves);
		//if m in activeMoves then
		if(inMoveList(node, activeMoves)){
			//activeMoves <- activeMoves\{m}
			activeMoves = activeMoves->tail;
			//workListMoves <- workListMoves + {m}
			worklistMoves = Live_MoveList(rel->src, rel->dst, worklistMoves);
		}
	}	
}

//procedure DecrementDegree(m)
static void DecrementDegree(G_node node){
	log("DecrementDegree\n");
	//let d = degree[m]
	nodeInfo info = G_nodeInfo(node);
	int d = info->degree;
	//degree[m] = d -1
	info->degree = d-1;
	//if d == K then
	if(d == REG_NUM){
		//EnableMoves({m} + Adjcent(m))
		EnableMoves(G_NodeList(node, Adjacent(node)));
		//spillWorkList <- spillWorkList\{m}
		spillWorkList = G_RmNode(spillWorkList, node);
		//if MoveRelated(m) then
		if(MoveRelated(node)){
			//freezeWorkList <- freezeWorkList + {m}
			freezeWorkList=G_NodeList(node, freezeWorkList);
		}
		else{
			//simplifyWorklist <- simplifyWorklist + {m}
			simplifyWorkList=G_NodeList(node, simplifyWorkList);
		}
	}
}

//function GetAlias(n)
static G_node GetAlias(G_node node){
	log("GetAlias\n");
	//if n in coalescedNodes then
	if(G_inNodeList(node, coalescedNode)){
		nodeInfo info = G_nodeInfo(node);
		//GetAlias(alias[n])
		return GetAlias(info->alias);
	}
	else{
		//else n
		return node;
	}
}

//PROCEDURE AddWorkList(u)
static void AddWorkList(G_node node){
	log("AddWorkList\n");
	nodeInfo info = G_nodeInfo(node);
	//if(u not in precolored && !MoveRelated(u)) && degree[u] < K then
	if(!G_inNodeList(node, precolored) && !MoveRelated(node) && info->degree < REG_NUM){
		//freezeWorkList <- freezeWorklist\{u}
		freezeWorkList = G_RmNode(freezeWorkList, node);
		//simplifyWorklist <- simplifyWorklist + {u}
		simplifyWorkList=G_NodeList(node, simplifyWorkList);
	}
}

//function OK(t, r)
static bool OK(G_node t, G_node r){
	//degree[t] < K || t in precolored || (t, r) in adjSet
	nodeInfo tinfo = G_nodeInfo(t);
	return (tinfo->degree<REG_NUM 
		|| G_inNodeList(t,precolored)
		|| G_inNodeList(t, G_adj(r)));
}

//u in precolored && all Adjacent(v), OK(t, u)
static bool Check(G_node u, G_node v){
	bool res = FALSE;
	if(G_inNodeList(u, precolored)){
		res = TRUE;
		for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail){
			G_node t = nl->head;
			if(!OK(t,u)){
				res = FALSE;
				break;
			}
			
		}
	}
	else{
		G_nodeList nodes = G_UnionList(Adjacent(u),Adjacent(v));
		int cnt = 0;
		for(;nodes;nodes=nodes->tail){
			G_node n = nodes->head;
			nodeInfo info = G_nodeInfo(n);
			if(info->degree >= REG_NUM) 
				cnt += 1;
		}
		res = (cnt < REG_NUM)?TRUE:FALSE;
	}
	return res;
}

//procedure Combine
static void Combine(G_node u, G_node v){
	log("Combine\n");
	//if v in freezeWorklist then
	if(G_inNodeList(v, freezeWorkList))
		//freezeWorklist <- freezeWorklist\{v}
		freezeWorkList = G_RmNode(freezeWorkList, v);
	else
		//spillWorklist <- spillWorklist\{v}
		spillWorkList = G_RmNode(spillWorkList, v);
	//coalescedNodes <- coalescedNodes + {v}
	coalescedNode = G_NodeList(v, coalescedNode);
	//alias[v] <- u
	nodeInfo vinfo = G_nodeInfo(v);
	vinfo->alias = u;
	//EnableMoves(v)
	EnableMoves(G_NodeList(v, NULL));
	//for t in Adjacent(v)
	for(G_nodeList nl=Adjacent(v);nl;nl=nl->tail){
		G_node t = nl->head;
		//if(G_goesTo(u, t) || u == t)
		//	continue;
		//AddEdge(t, u)
		G_addEdge(t, u);	
		//DecremetnDegree(t)	
		DecrementDegree(t);
	}
	nodeInfo uinfo = G_nodeInfo(u);
	//if degree[u] >= K && u in freezeWorklist
	if(uinfo->degree>=REG_NUM && G_inNodeList(u, freezeWorkList)){
		//freezeWorklist <- freezeWorklist\{u}
		freezeWorkList = G_RmNode(freezeWorkList, u);
		//spillWorklist <- spillWorklist + {u}
		spillWorkList = G_NodeList(u, spillWorkList);
	}	
}

//procedure FreezeMoves(u)
static void FreezeMoves(G_node node){
	log("FreezeMoves\n");
	Live_moveList ml = RMrelatedMovs(node, activeMoves);
	//activeMoves <- activeMoves\{m}
	if(inMoveList(node, activeMoves))
		activeMoves = activeMoves->tail;
	//for m(=copy(x, y)) in NodeMoves(u)
	for(;ml;ml=ml->tail){
		G_node src = GetAlias(ml->src);
		G_node dst = GetAlias(ml->dst);
		G_node v;
		//if Getalias(y)=GetAlias(u) then
		if(GetAlias(node) == src)
			//v <- GetAlias(x)
			v = dst;
		else
			//v<-GetAlias(y)
			v = src;
		//forzenMoves <- frozenMoves+{m}
		frozenMoves = Live_MoveList(ml->src, ml->dst, frozenMoves);
	
		nodeInfo vinfo = G_nodeInfo(v);
		//if NodeMoves(v) = {} && degree[v] < K then
		if(!G_inNodeList(v,precolored) && !inMoveList(v, activeMoves) && vinfo->degree<REG_NUM){
			//freezeWorklist <- freezeWorklist\{v}
			freezeWorkList = G_RmNode(freezeWorkList, v);
			//simplifyWorklist <- simplifyWorklist + {v}
			simplifyWorkList = G_NodeList(v, simplifyWorkList);
		}
	}
}

//procedure MakeWorkList()
static void MakeWorkList(G_graph cfgraph){
	log("MakeWorkList\n");
	G_nodeList nl = G_nodes(cfgraph);
	//for n in initial
	for(;nl;nl=nl->tail){
		//initial = initial\{n}
		G_node node = nl->head;
		nodeInfo info = G_nodeInfo(node);
		int degree = G_degree(node);/* Tell how many edges lead to or from "n" */
		info->degree = degree;
		//find hard register
		if(Temp_look(F_tempMap, info->reg)){
			//info->stat = PRECOLORED;
			info->degree = __INT_MAX__;
			precolored = G_NodeList(node, precolored);
			continue;
		}		
		if(degree >= REG_NUM){
			//if degree[n] >= K then spillWorklist <- spillworkList + {n}
			spillWorkList=G_NodeList(node, spillWorkList);
		}
		else if(MoveRelated(node)){
			//else if MoveRelated(n)
			freezeWorkList=G_NodeList(node, freezeWorkList);
		}
		else{
			//else simplifyWorklist <- simplifyWorklist + {n}
			simplifyWorkList=G_NodeList(node, simplifyWorkList);
		}

	}
}

//procedure Simplify()
static void Simplify(){
	log("Simplify\n");
	//let n = simplifyWorkList->head
	G_node node = simplifyWorkList->head;
	//simplifyWorkList <- simplifyWorklist\{n}
	simplifyWorkList = simplifyWorkList->tail;	
	nodeInfo info = G_nodeInfo(node);
	SelectStack = G_NodeList(node, SelectStack);
	//for m in {Adjacent(n)}
	for(G_nodeList nl=Adjacent(node);nl;nl=nl->tail){
		//DecrementDegree(m)
		DecrementDegree(nl->head);
	}
}

//procedure Coalesce
static void Coalesce(){
	log("Coalesce\n");
	//let m(=copy(x,y)) in worklistMoves
	Live_moveList p = Live_MoveList(worklistMoves->src,worklistMoves->dst,NULL);
	
	//x<-GetAlias(x)
	G_node src = GetAlias(p->src);
	//y<-GetAlias(y)
	G_node dst = GetAlias(p->dst);

	//Live_printMoveList(Live_MoveList(p->src,p->dst,NULL));
	G_node u,v;
	//if y in precolored then
	if(G_inNodeList(src, precolored)){
		//let(u,v) = (y,x)
		u = src; v = dst;
	}
	else{
		//else let(u,v) = (x,y)
		u = dst; v = src;
	}
	//worklistMoves <- worklistMoves\{m}
	worklistMoves = worklistMoves->tail;
	//if u =v then
	if(u == v){
		//coalescedMOves <- coalescedMoves + {m}
		coalescedMoves = Live_MoveList(p->src, p->dst, coalescedMoves);
		//AddWorkList(u)
		AddWorkList(u);
	}
	//else if v in precolored || (u, v) in adjSet then
	else if(G_inNodeList(v, precolored) || G_inNodeList(u, G_adj(v))){
		//constrainedMoves <- constrainedMoves+{m}
		constrainedMoves = Live_MoveList(p->src, p->dst, constrainedMoves);
		//AddWorkList(u)
		AddWorkList(u);
		//AddWorkList(v)
		AddWorkList(v);
	}
	//else if u in precolored && (all Adjacent(v), OK(t, u))
	//		|| u not in precolored && Conservative(Adjacent(u) + Adjacent(v)) then
	else if(Check(u, v)){
		//coelescedMoves<-coalescedMoves + {m}
		coalescedMoves = Live_MoveList(p->src, p->dst, coalescedMoves);
		//Combine(u, v)
		Combine(u, v);
		//AddWorkList(u)
		AddWorkList(u);
	}
	else{
		//else activeMoves <- activeMoves + {m}
		activeMoves = Live_MoveList(p->src, p->dst, activeMoves);
	}
}

//procedure Freeze()
static void Freeze(){
	log("Freeze\n");
	//let u in freezeWorklist
	G_node node = freezeWorkList->head;
	//freezeWorklist <- freezeWorklist\{u}
	freezeWorkList = freezeWorkList->tail;
	//simplifyWorklist <- simplifyWorklist+{u}
	simplifyWorkList = G_NodeList(node, simplifyWorkList);
	//FreezeMoves(u)
	FreezeMoves(node);
}

//procedure SelectSpill()
static void SelectSpill(){
	log("SelectSpill\n");
	//let m in spillWorklist
	G_node node = spillWorkList->head;
	//spillWorklist <- spillWorklist\{m}
	spillWorkList = spillWorkList->tail;
	//simplifyWorklist <- simplifyWorklist+{m}
	simplifyWorkList = G_NodeList(node, simplifyWorkList);
	//FreezeMoves(m)
	FreezeMoves(node);
}

//procedure AssignColors()
static void AssignColor(){
	log("AssignColor\n");
	COL_map();
	//while(selectSTACK not empty)
	for(G_nodeList nl=SelectStack;nl;nl=nl->tail){
		//let n = pop(selectStack)
		G_node node = nl->head;
		//Temp_map map = Temp_layerMap(F_tempMap, Temp_name());
		//printf("t%s\n", Temp_look(map, Live_gtemp(node)));
		//okCOLORS <- {0,1,2....K-1}
		Temp_tempList colors = COL_allColor();
		//for w in adjList[n]
		for(G_nodeList adj=G_adj(node);adj;adj=adj->tail){
			G_node t = adj->head;
			//printf("\tadj t%s\n", Temp_look(map, Live_gtemp(t)));
			G_nodeList used = G_UnionList(precolored, coloredNode);
			//if GetAlias(w) in (coloredNodes + precolred) then
			if(G_inNodeList(GetAlias(t), used)){
				//okColors <- okColors\{color|GetAlias(w)}
				colors = COL_rmColor(GetAlias(t), colors);
			}
		}
		//if okColor != {} then
		if(!colors){
			//spilledNodes <- spilledNodes + {n}
			spilledNode = G_NodeList(node, spilledNode);
		}
		else{
			//else coloredNodes <- coloredNodes + {n}
			coloredNode = G_NodeList(node, coloredNode);
			//let c in okColors, color[n] <-c
			COL_assignColor(node, colors);
		}
	}
	SelectStack = NULL;
	//for n in coalescedNodes
	for(G_nodeList nl=coalescedNode;nl;nl=nl->tail){
		G_node node = nl->head;
		//color[n] <- color[GetAlias(n)]
		COL_sameColor(GetAlias(node), node);
	}
}

void printMovs(){
	printf("\n-------==== spillworklist =====-----\n");
	G_show(stdout, spillWorkList, RA_showInfo);	
	printf("\n-------==== stack =====-----\n");
	G_show(stdout, SelectStack, RA_showInfo);	
	printf("\n-------==== coalescedMoves =====-----\n");
	Live_printMoveList(coalescedMoves);
	printf("\n-------==== frozenMoves =====-----\n");
	Live_printMoveList(frozenMoves);
	printf("\n-------==== constrainedMoves =====-----\n");
	Live_printMoveList(constrainedMoves);
	printf("\n-------==== activeMoves =====-----\n");
	Live_printMoveList(activeMoves);
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	log("RA_regAlloc\n");
	clear();
	//Flowgraph
	G_graph fg = FG_AssemFlowGraph(il);  /* 10.1 */
	//G_show(stdout, G_nodes(fg), FG_showInfo);
	//printf("\n-------====flow graph=====-----\n");

	//liveness analysis
	struct Live_graph lg = Live_liveness(fg);  /* 10.2 */
	//G_show(stdout, G_nodes(lg.graph), Live_showInfo);
	//printf("\n-------==== CF graph=====-----\n");
	//Live_printMoveList(lg.moves);

	worklistMoves = lg.moves;
	MakeWorkList(lg.graph);
	//G_show(stdout, simplifyWorkList, RA_showInfo);
	//Live_printMoveList(worklistMoves);
	//printf("\n-------==== init =====-----\n");
	
	//repeat
	while(1){
		//if simplifyWorklist !={} then Simplify()
		if(simplifyWorkList){
			Simplify();
		}
		//else if worklistMoves != {} then Coalesce()
		else if(worklistMoves){
			Coalesce();
		}
		//else if freezeWorkList != {} then Freeze()
		else if(freezeWorkList){
			Freeze();
		}
		//else if spillWorkList != {} then SelectSpill()
		else if(spillWorkList){
			SelectSpill();
		}
		//until simplifyWorklist = {} && worklistMoves = {} && freezeWorklist = {} && spillWorklist = {}
		else
			break;
	}
	//printf("\n-------==== loop over =====-----\n");
	//printMovs();
	
	//AssignColor()
	AssignColor();

	Temp_map map = Temp_layerMap(COL_map(),Temp_layerMap(F_tempMap, Temp_name()));
	
	//if spilledNodes != {} then RewriteProgram(spilledNodes);Main()
	if(spilledNode){
		printf("\n-------==== spillnode =====-----\n");
		G_show(stdout, spilledNode, RA_showInfo);
		COL_clearMap();
		AS_instrList nil = AS_rewriteSpill(f, il, spilledNode);
		printf("\n");
		//AS_printInstrList (stdout, nil, map);
		return RA_regAlloc(f, nil);
	}
	struct RA_result ret;
	ret.coloring = COL_map();
	ret.il=il;

	//AS_rewrite(il, map);
	//printf("BEGIN function\n");
	//AS_printInstrList (stdout, il, map);
	printf("\n-------==== after RA =====-----\n");
	return ret;
}
