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


/*
 * Graph:
 * - for each node, we keep:
 *   the corresponding egraph class
 *   the set of outgoing edges from that node
 *   the lambda tag (as defined in the egraph ltag_table)
 * - the set of edges is stored in a pointer vector (cf. pointer_vectors.h)
 * - we also store the reverse map: egraph class to nodes
 * - and we keep track of the lambda terms
 */
struct update_graph_s {
  uint32_t size;  // size of arrays class, edges, and tag
  uint32_t nodes; // number of nodes
  class_t *class; // class[i] = class of node i
  void ***edges;  // edges[i] = array of (void*) pointers
  int32_t *tag;   // tag[i] = lambda tag

  uint32_t nclasses;    // size of array class2node
  int32_t *class2node;  // class2node[c] = node for class c (-1 if none)  

  // MORE TBD
};

#define MAX_UGRAPH_SIZE (UINT32_MAX/sizeof(void **))
#define DEF_UGRAPH_SIZE 100

#define MAX_UGRAPH_NCLASSES (UINT32_MAX/sizeof(int32_t))
#define DEF_UGRAPH_NCLASSES 100



/*
 * Initialize ugraph (to the empty graph)
 */
extern void init_ugraph(update_graph_t *ugraph);

/*
 * Reset to the empty graph
 */
extern void reset_ugraph(update_graph_t *ugraph);

/*
 * Delete ugraph:
 * - free all internal structures
 */
extern void delete_ugraph(update_graph_t *ugraph);


/*
 * Build ugraph based on the current egraph partition
 * - ugraph must be initialized and empty
 * - one node is created for each egraph class that has function type
 * - for each update term b = (update a ... ) that's in the congruence 
 *   table (congruence root),  we create two egdes: 
 *   a direct edge from node[class[a]] to node[class[b]]
 *   a reverse edge from node[class[b]] to node[class[a]]
 */
extern void build_ugraph(update_graph_t *ugraph, egraph_t *egraph);


#endif
