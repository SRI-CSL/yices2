/***********************************************************
 *  EXTENSION OF THE EGRAPH TO DEAL WITH FUNCTION UPDATES  *
 **********************************************************/

#include <assert.h>

#include "memalloc.h"
#include "pointer_vectors.h"
#include "tagged_pointers.h"

#include "egraph.h"
#include "update_graph.h"


/*
 * Initialize ugraph (to the empty graph)
 */
void init_ugraph(update_graph_t *ugraph) {
  ugraph->size = 0;
  ugraph->nodes = 0;
  ugraph->class = NULL;
  ugraph->edges = NULL;
  ugraph->tag  = NULL;
  ugraph->nclasses = 0;
  ugraph->class2node = NULL;
}


/*
 * Make room for new nodes
 */
static void extend_ugraph_nodes(update_graph_t *ugraph) {
  uint32_t n;

  n = ugraph->size;
  if (n == 0) {
    // first allocation: use the default size
    n = DEF_UGRAPH_SIZE;
    assert(n <= MAX_UGRAPH_SIZE);

    ugraph->class = (class_t *) safe_malloc(n * sizeof(class_t));
    ugraph->edges = (void ***) safe_malloc(n * sizeof(void **));
    ugraph->tag = (int32_t *) safe_malloc(n * sizeof(int32_t));

    ugraph->size = n;
    
  } else {
    // increase the size by 50%
    n += ((n + 1) >> 1);
    if (n > MAX_UGRAPH_SIZE) {
      out_of_memory();
    }

    ugraph->class = (class_t *) safe_realloc(ugraph->class, n * sizeof(class_t));
    ugraph->edges = (void ***) safe_realloc(ugraph->edges, n * sizeof(void **));
    ugraph->tag = (int32_t *) safe_realloc(ugraph->tag, n * sizeof(int32_t));

    ugraph->size = n;
  }
}


/* 
 * Extend the class2node array to size large enough to store n classes
 * - do nothing if the array is large enough already
 * - extend the current array otherwise and initialize class2node[i] to -1 for all new i
 */
static void ugraph_resize_classes(update_graph_t *ugraph, uint32_t n) {
  uint32_t i;

  if (n >= ugraph->nclasses) {
    if (n > MAX_UGRAPH_NCLASSES) {
      out_of_memory();
    }

    ugraph->class2node = (int32_t *) safe_realloc(ugraph->class2node, n * sizeof(int32_t));
    for (i= ugraph->nclasses; i<n; i++) {
      ugraph->class2node[i] = -1;
    }
    ugraph->nclasses = n;
  }
}


/*
 * Add a new node to represent class c
 * - tag = lambda tag for class c
 * - return the node id
 */
static int32_t ugraph_add_node(update_graph_t *ugraph, class_t c, int32_t tag) {
  uint32_t i;

  i = ugraph->nodes;
  if (i == ugraph->size) {
    extend_ugraph_nodes(ugraph);
  }
  assert(i < ugraph->size);
  ugraph->class[i] = c;
  ugraph->edges[i] = NULL;
  ugraph->tag[i] = tag;

  ugraph->nodes = i+1;

  return i;
}



/*
 * Reset to the empty graph
 */
void reset_ugraph(update_graph_t *ugraph) {
  uint32_t i, n;

  n = ugraph->nodes;
  for (i=0; i<n; i++) {
    reset_ptr_vector(ugraph->edges[i]);
  }
  ugraph->nodes = 0;  
  
  n = ugraph->nclasses;
  for (i=0; i<n; i++) {
    ugraph->class2node[i] = -1;
  }
}


/*
 * Delete ugraph:
 * - free all internal structures
 */
void delete_ugraph(update_graph_t *ugraph) {
  uint32_t i, n;

  n = ugraph->nodes;
  for (i=0; i<n; i++) {
    delete_ptr_vector(ugraph->edges[i]);
  }
  safe_free(ugraph->class);
  safe_free(ugraph->edges);
  safe_free(ugraph->tag);
  safe_free(ugraph->class2node);

  ugraph->class = NULL;
  ugraph->edges = NULL;
  ugraph->tag = NULL;
  ugraph->class2node = NULL;
}


/*
 * Get the node if for class c
 */
static inline int32_t node_of_class(update_graph_t *ugraph, class_t c) {
  assert(0 <= c && c < ugraph->nclasses);
  return ugraph->class2node[c];
}

/*
 * Store i as the node id for class c
 */
static inline void set_node_of_class(update_graph_t *ugraph, class_t c, int32_t i) {
  assert(0 <= c && c < ugraph->nclasses && 0 <= i && i < ugraph->nodes && ugraph->class2node[c] < 0);
  ugraph->class2node[c] = i;
}


/*
 * Add a term t to the update graph
 * - c = class of t
 * - tau = type of t
 * - create a new node for c if there's not one already
 */
static void ugraph_add_term(update_graph_t *ugraph, egraph_t *egraph, eterm_t t, class_t c, type_t tau) {
  int32_t node;
  int32_t tag;

  node = node_of_class(ugraph, c);
  if (node < 0) {
    tag = egraph_get_lambda_tag(egraph, tau);
    node = ugraph_add_node(ugraph, c, tag);
    set_node_of_class(ugraph, c, node);
  }
}


/*
 * Add cmp as a new edge from a to b
 * - also add the reverse edge from b to a
 * - the reverse edge is tagged with 01
 */
static void ugraph_add_edge(update_graph_t *ugraph, int32_t a, int32_t b, composite_t *cmp) {
  assert(0 <= a && a < ugraph->nodes && 0 <= b && b < ugraph->nodes);
  add_ptr_to_vector(ugraph->edges + a, cmp);
  add_ptr_to_vector(ugraph->edges + b, tag_ptr(cmp, 1));
}


/*
 * Get the node id for term t
 */
static inline int32_t node_of_term(update_graph_t *ugraph, egraph_t *egraph, eterm_t t) {
  return node_of_class(ugraph, egraph_term_class(egraph, t));
}


/*
 * Add the two edges defined by update term cmp
 */
static void ugraph_add_edges_for_update(update_graph_t *ugraph, egraph_t *egraph, composite_t *cmp) {
  int32_t source, target;

  assert(composite_kind(cmp) == COMPOSITE_UPDATE);
  source = node_of_term(ugraph, egraph, cmp->child[0]); 
  target = node_of_term(ugraph, egraph, cmp->id);
  ugraph_add_edge(ugraph, source, target, cmp);
}


/*
 * Build ugraph based on the current egraph partition
 * - one node is created for each egraph class that has function type
 * - for each update term b = (update a ... ) that's in the congruence 
 *   table (congruence root),  we create two edges: 
 *   a direct edge from node[class[a]] to node[class[b]]
 *   a reverse edge from node[class[b]] to node[class[a]]
 */
void build_ugraph(update_graph_t *ugraph, egraph_t *egraph) {
  uint32_t i, n;
  type_t tau;
  composite_t *cmp;

  assert(ugraph->nodes == 0);

  // first pass: create the nodes
  ugraph_resize_classes(ugraph, egraph->classes.nclasses);
  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    tau = egraph_term_real_type(egraph, i);
    if (is_function_type(egraph->types, tau)) {
      ugraph_add_term(ugraph, egraph, i, egraph_term_class(egraph, i), tau);
    }
  }

  // second pass: add the edges
  for (i=0; i<n; i++) {
    cmp = egraph_term_body(egraph, i);
    if (composite_body(cmp) && composite_kind(cmp) == COMPOSITE_UPDATE) {
      ugraph_add_edges_for_update(ugraph, egraph, cmp);
    }
  }
}

