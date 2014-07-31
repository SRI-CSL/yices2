/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

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
 * To do this, we add to the egraph an optional new component
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

#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#include "utils/bitvectors.h"
#include "utils/ptr_partitions.h"
#include "solvers/egraph/egraph_types.h"


/*
 * Tree/queue for visiting the graph from a source node
 * - for each visited node, we store three things
 *   - the node id
 *   - the index of the previous triple on the path from source to the node
 *   - the incoming edge from the previous node
 * - data[0 ... top-1] = the triples for each visited node
 * - ptr = next node to process
 * - top = next record
 * - size = size of the data array
 *
 * We explore the graph breadth first:
 * - triples in data[0 ... ptr - 1] correspond to nodes
 *   whose successors have been visited
 * - triples in data[ptr ... top - 1] is a queue of nodes
 *   that are reachable but whose successors have not been
 *   explored yet.
 *
 * - let x be data[ptr].node
 * - if edge u of x leads to node y, then we add
 *   a new record at the end of the queue
 *     data[top].node = y
 *     data[top].pre  = ptr
 *     data[top].edge = u
 */
typedef struct ugraph_visit_s {
  int32_t node;
  int32_t pre;
  composite_t *edge;
} ugraph_visit_t;

typedef struct ugraph_queue_s {
  uint32_t size;
  uint32_t top;
  uint32_t ptr;
  ugraph_visit_t *data;
} ugraph_queue_t;

#define DEF_UGRAPH_QUEUE_SIZE 20
#define MAX_UGRAPH_QUEUE_SIZE (UINT32_MAX/sizeof(ugraph_visit_t))


/*
 * Set of pairs [tag, type] for which there exists a lambda term.
 * If a  lambda term has type [tau_1 x ... x tau_n -> sigma]
 * then we add the pair (tag, sigma) where tag is the lambda-tag for
 * tau_1 x ... x tau_n.
 *
 * For now, we just store the pairs in an array (since there shouldn't
 * be many pairs). We keep a pointer to the type table.
 */
typedef struct lambda_pair_s {
  int32_t tag;
  type_t range;
} lambda_pair_t;

typedef struct lpair_set_s {
  uint32_t size;
  uint32_t nelems;
  lambda_pair_t *data;
  type_table_t *types;
} lpair_set_t;

#define DEF_LPAIR_SET_SIZE 10
#define MAX_LPAIR_SET_SIZE (UINT32_MAX/sizeof(lambda_pair_t))



/*
 * Statistics
 */
typedef struct ugraph_stats_s {
  uint32_t num_update_props;
  uint32_t num_lambda_props;
  uint32_t num_update_conflicts;
  uint32_t num_lambda_conflicts;
} ugraph_stats_t;




/*
 * Graph:
 * - for each node x, we keep:
 *   class[x] = the corresponding egraph
 *   egdes[x] = vector of outgoing edges from that node
 *     tag[x] = the lambda tag (as defined in the egraph ltag_table)
 *    mark[x] = one bit: 1 means x has been visited
 * - the set of edges is stored in a pointer vector (cf. pointer_vectors.h)
 *
 * For every class c, we store
 *   class2node[c] = -1 if c has no matching node in the graph
 *                 =  x is c is matched to node x (i.e., class[x] = c)
 *
 * For propagation:
 * - queue = visited nodes
 * - partition = to group composite terms that have equal arguments
 * - lpair_set = types for the lambda terms
 */
struct update_graph_s {
  egraph_t *egraph;   // pointer to the egraph

  uint32_t size;  // size of arrays class, edges, and tag
  uint32_t nodes; // number of nodes
  class_t *class; // class[i] = class of node i
  void ***edges;  // edges[i] = array of (void*) pointers
  int32_t *tag;   // tag[i] = lambda tag
  byte_t *mark;   // mark[i] = one bit

  uint32_t nclasses;    // size of array class2node
  int32_t *class2node;  // class2node[c] = node for class c (-1 if none)

  ugraph_queue_t queue;   // for exploration
  ppart_t partition;      // partition of apply terms
  lpair_set_t lpair_set;  // types of lambda terms

  ugraph_stats_t stats;

  ivector_t aux_vector;
  ivector_t lemma_vector;
};


#define MAX_UGRAPH_SIZE (UINT32_MAX/sizeof(void **))
#define DEF_UGRAPH_SIZE 100

#define MAX_UGRAPH_NCLASSES (UINT32_MAX/sizeof(int32_t))
#define DEF_UGRAPH_NCLASSES 100



/*
 * Initialize ugraph (to the empty graph)
 */
extern void init_ugraph(update_graph_t *ugraph, egraph_t *egraph);


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
extern void build_ugraph(update_graph_t *ugraph);


/*
 * Propagate at the base level
 * - make sure build_ugraph was called first
 * - this searches for equalities implied by the update graph
 *   and adds them to the egraph (as axioms)
 * - return the number of equalities found
 */
extern uint32_t ugraph_base_propagate(update_graph_t *ugraph);





/*
 * Marks
 */
static inline bool ugraph_node_is_marked(update_graph_t *ugraph, int32_t i) {
  assert(0 <= i && i < ugraph->nodes);
  return tst_bit(ugraph->mark, i);
}

static inline bool ugraph_node_is_unmarked(update_graph_t *ugraph, int32_t i) {
  assert(0 <= i && i < ugraph->nodes);
  return ! tst_bit(ugraph->mark, i);
}

static inline void ugraph_mark_node(update_graph_t *ugraph, int32_t i) {
  assert(0 <= i && i < ugraph->nodes);
  set_bit(ugraph->mark, i);
}

static inline void clear_ugraph_node_mark(update_graph_t *ugraph, int32_t i) {
  assert(0 <= i && i < ugraph->nodes);
  clr_bit(ugraph->mark, i);
}


#endif
