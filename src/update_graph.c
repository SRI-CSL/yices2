/***********************************************************
 *  EXTENSION OF THE EGRAPH TO DEAL WITH FUNCTION UPDATES  *
 **********************************************************/

#include <assert.h>

#include "memalloc.h"
#include "pointer_vectors.h"
#include "tagged_pointers.h"

#include "composites.h"
#include "egraph.h"
#include "update_graph.h"



/****************
 *  QUEUE/TREE  *
 ***************/

/*
 * Initialization: nothing allocated yet
 */
static void init_ugraph_queue(ugraph_queue_t *queue) {
  queue->size = 0;
  queue->top = 0;
  queue->ptr = 0;
  queue->data = NULL;
}


/*
 * Make room
 */
static void extend_ugraph_queue(ugraph_queue_t *queue) {
  uint32_t n;

  n = queue->size;
  if (n == 0) {
    n = DEF_UGRAPH_QUEUE_SIZE;
    assert(n <= MAX_UGRAPH_QUEUE_SIZE);
    queue->data = (ugraph_visit_t *) safe_malloc(n * sizeof(ugraph_visit_t));
    queue->size = n;

  } else {
    // try 50% larger
    n ++;
    n += n>>1;
    if (n > MAX_UGRAPH_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = (ugraph_visit_t *) safe_realloc(queue->data, n * sizeof(ugraph_visit_t));
    queue->size = n;
  }
}


/*
 * Delete the queue
 */
static void delete_ugraph_queue(ugraph_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}


/*
 * Reset the queue
 */
static void reset_ugraph_queue(ugraph_queue_t *queue) {
  queue->top = 0;
  queue->ptr = 0;
}


/*
 * Push triple (x, p, u) at the end of the queue
 * - x = node index
 * - p = previous record
 * - u = edge (update composite)
 */
static void ugraph_queue_push(ugraph_queue_t *queue, int32_t x, int32_t p, composite_t *u) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_ugraph_queue(queue);
  }
  assert(i < queue->size);

  queue->data[i].node = x;
  queue->data[i].pre = p;
  queue->data[i].edge = u;

  queue->top = i+1;
}


/*
 * Add a root node x
 */
static inline void ugraph_queue_push_root(ugraph_queue_t *queue, int32_t x) {
  assert(queue->top == 0 && queue->ptr == 0);
  ugraph_queue_push(queue, x, -1, NULL);
}

/*
 * Add node y 
 * - y must be a successor of the node stored in queue->data[ptr]
 * - u = edge from the current node to y
 */
static inline void ugraph_queue_push_next(ugraph_queue_t *queue, int32_t y, composite_t *u) {
  assert(queue->top > 0);
  ugraph_queue_push(queue, y, queue->ptr, u);
}

/*
 * Check whether the queue is empty
 */
static inline bool empty_ugraph_queue(ugraph_queue_t *queue) {
  return queue->top == queue->ptr;
}

/*
 * Get the id of the current node (at index ptr)
 */
static inline int32_t ugraph_queue_current_node(ugraph_queue_t *queue) {
  assert(queue->ptr < queue->top);
  return queue->data[queue->ptr].node;
}

/*
 * Move to the next node
 */
static inline void ugraph_queue_pop(ugraph_queue_t *queue) {
  assert(queue->ptr < queue->top);
  queue->ptr ++;
}




/******************
 *  UPDATE GRAPH  *
 *****************/

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

  init_ugraph_queue(&ugraph->queue);
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

  reset_ugraph_queue(&ugraph->queue);
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

  delete_ugraph_queue(&ugraph->queue);
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

  /*
   * second pass: add the edges
   * each edge is an update term that's a congruence root
   *
   * TODO: check whether we can get better explanations by keeping all
   * update terms even the ones that are not congruence root?
   */
  for (i=0; i<n; i++) {
    cmp = egraph_term_body(egraph, i);
    if (composite_body(cmp) && 
	composite_kind(cmp) == COMPOSITE_UPDATE &&
	congruence_table_is_root(&egraph->ctable, cmp, egraph->terms.label)) {
      ugraph_add_edges_for_update(ugraph, egraph, cmp);
    }
  }
}




/*************************************
 *  PROPAGATION IN THE UPDATE GRAPH  *
 ************************************/

/*
 * Given an edge u = (update _ x1 ... xn _) and a term a = (apply _ t1 ... tn)
 * - the edge is opaque for a if t1 == x1 and .... and tn == xn.
 * - the edge is transparent if the disequality ti /= xi holds in the Egraph
 *   for some index i
 *
 * Propagation through update chains
 * ---------------------------------
 * If we have two terms a = (apply f t1 ... t_n) and b = (apply g u1 ... u_n),
 * such that t1 == u1 .... tn == un, and there's a path from
 * node(f) to node(g) that's transparent for a, then we can deduce
 * that a and b must be equal (by the array update axioms).
 *
 * If we have terms a = (apply f t1 ... tn) and g = (lambda ... b)
 * and there's a path from node(f) to g that's transparent for a
 * then we can deduce a = b.
 *
 * Final check
 * -----------
 * We generate instances of the update axiom by searching for
 * terms a = (apply f t1 ... tn) and b = (apply g u1 ... u_n)
 * such that:
 *   1) t1 == u1 ... t_n == u_n
 *   2) a and b are in distinct egraph classes
 *   3) there's a path from node(f) to node(g) that contains no edge 
 *      opaque for a
 *
 * For g = (lamdba .. b ..), we add an instance of path => (apply f t1 ... tn) = b
 * if there's a path from node(f) to node(g) that doesn't contain an edge
 * opaque to a.
 */
static bool opaque_edge(egraph_t *egraph, composite_t *u, composite_t *a) {
  uint32_t i, n;

  assert(composite_kind(u) == COMPOSITE_UPDATE && composite_kind(a) == COMPOSITE_APPLY);

  n = composite_arity(a);
  assert(composite_arity(u) == n+1);

  for (i=1; i<n; i++) {
    if (! egraph_check_eq(egraph, a->child[i], u->child[i])) {
      return false;
    }
  }

  return true;
}

static bool transparent_edge(egraph_t *egraph, composite_t *u, composite_t *a) {
  uint32_t i, n;

  assert(composite_kind(u) == COMPOSITE_UPDATE && composite_kind(a) == COMPOSITE_APPLY);

  n = composite_arity(a);
  assert(composite_arity(u) == n+1);

  for (i=1; i<n; i++) {
    if (egraph_check_diseq(egraph, a->child[i], u->child[i])) {
      return true;
    }
  }

  return false;
}


