/*
 * flowgraph.h - Function prototypes to represent control flow graphs.
 */

#ifndef FLOWGRAPH_H
#define FLOWGRAPH_H

#include "graph.h"
#include "temp.h"
#include "assem.h"

Temp_tempList FG_def(G_node n);
Temp_tempList FG_use(G_node n);
bool FG_isMove(G_node n);
G_graph FG_AssemFlowGraph(AS_instrList il);
void FG_showInfo(void *p);

#endif
