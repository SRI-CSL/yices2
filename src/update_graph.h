/***********************************************************
 *  EXTENSION OF THE EGRAPH TO DEAL WITH FUNCTION UPDATES  *
 **********************************************************/

/*
 * Started 2012/09/14:
 * - the array solver is currently implemented as a
 *   satellite of the egraph. This makes if hard to support
 *   new things such as lambda terms and type predicates.
 * - new approach: get rid of fun_solver and implement
 *   instantiation of the update/extensionality axioms
 *   directly in the Egraph.
 *
 * To do this, we add to the egraph and optional new component
 * called the update graph. Vertices in this graph are 
 * equivalence classes of function terms (extracted from the egraph)
 * and edges correspond to update terms. If a = (update b t1 .. tn v)
 * then there's an edge from Class(a) to Class(b) labeled by a.
 * Also, there's an edge from Class(b) to Class(a). If two nodes
 * are connected in the update graph, then they represent functions
 * that differ by finitely many values.
 *
 */

#ifndef __UPDATE_GRAPH_H
#define __UPDATE_GRAPH_H

#include <stdint.h>

#include "egraph_types.h"




#endif
