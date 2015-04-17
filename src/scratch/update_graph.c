/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/***********************************************************
 *  EXTENSION OF THE EGRAPH TO DEAL WITH FUNCTION UPDATES  *
 **********************************************************/

#include <assert.h>

#include "scratch/update_graph.h"
#include "solvers/egraph/composites.h"
#include "solvers/egraph/egraph.h"
#include "utils/memalloc.h"
#include "utils/pointer_vectors.h"
#include "utils/tagged_pointers.h"



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



/*************************************
 *  SET OF PAIRS (tags, range type)  *
 ************************************/

/*
 * Initialize to the empty set
 * - types = the relevant type table
 */
static void init_lpair_set(lpair_set_t *set, type_table_t *types) {
  set->size = 0;
  set->nelems = 0;
  set->data = NULL;
  set->types = types;
}


/*
 * Make the array larger
 */
static void extend_lpair_set(lpair_set_t *set) {
  uint32_t n;

  n = set->size;
  if (n == 0) {
    n = DEF_LPAIR_SET_SIZE;
    assert(n <= MAX_LPAIR_SET_SIZE);
    set->data = (lambda_pair_t *) safe_malloc(n * sizeof(lambda_pair_t));
    set->size = n;
  } else {
    n ++;
    n += n>>1;

    if (n > MAX_LPAIR_SET_SIZE) {
      out_of_memory();
    }
    set->data = (lambda_pair_t *) safe_realloc(set->data, n * sizeof(lambda_pair_t));
    set->size = n;
  }
}


/*
 * Add pair [tag, tau] at the end of set->data
 */
static void lpair_set_push(lpair_set_t *set, int32_t tag, type_t tau) {
  uint32_t i;

  i = set->nelems;
  if (i == set->size) {
    extend_lpair_set(set);
  }
  assert(i < set->size);
  set->data[i].tag = tag;
  set->data[i].range = tau;
  set->nelems = i+1;
}


/*
 * Empty the table
 */
static inline void reset_lpair_set(lpair_set_t *set) {
  set->nelems = 0;
}


/*
 * Free memory
 */
static void delete_lpair_set(lpair_set_t *set) {
  safe_free(set->data);
  set->data = NULL;
}


/*
 * Check whether the set is empty
 */
#ifndef NDEBUG
static inline bool lpair_set_is_empty(lpair_set_t *set) {
  return set->nelems == 0;
}
#endif

/*
 * Check whether the set contains a pair [tag, sigma]
 * where sigma is compatible with tau
 */
static bool lpair_set_has_match(lpair_set_t *set, int32_t tag, type_t tau) {
  lambda_pair_t *data;
  uint32_t i, n;

  assert(good_type(set->types, tau));

  n = set->nelems;
  data = set->data;
  for (i=0; i<n; i++) {
    if (data->tag == tag &&
        (data->range == tau || compatible_types(set->types, tau, data->range))) {
      return true;
    }
    data ++;
  }

  return false;
}


/*
 * Check whether the set contains the pair [tag, tau]
 */
static bool lpair_set_member(lpair_set_t *set, int32_t tag, type_t tau) {
  lambda_pair_t *data;
  uint32_t i, n;

  assert(good_type(set->types, tau));

  n = set->nelems;
  data = set->data;
  for (i=0; i<n; i++) {
    if (data->tag == tag && data->range == tau) {
      return true;
    }
    data ++;
  }

  return false;
}


/*
 * Add pair [tag, tau] to the set. No change if the pair is already in the set.
 */
static void lpair_set_add(lpair_set_t *set, int32_t tag, type_t tau) {
  if (! lpair_set_member(set, tag, tau)) {
    lpair_set_push(set, tag, tau);
  }
}


/*
 * Add the pair [tag, sigma] where sigma = range type for tau
 */
static inline void lpair_set_add_ftype(lpair_set_t *set, int32_t tag, type_t tau) {
  lpair_set_add(set, tag, function_type_range(set->types, tau));
}



/*********************
 *  PARTITION TABLE  *
 ********************/

/*
 * Hash and match function required for the partition table:
 * - the table store composites of the form (apply f t_1 ... t_n)
 * - two composites c and d match each other if their arguments t_1 ... t_n
 *   and u_1 ... u_n are equal in the Egraph
 */
static uint32_t ugraph_hash_arg(egraph_t *egraph, composite_t *c) {
  return hash_arg_signature(c, egraph->terms.label);
}

static uint32_t ugraph_match_arg(egraph_t *egraph, composite_t *c, composite_t *d) {
  return same_arg_signature(c, d, egraph->terms.label);
}


/*
 * Initialize the partition table
 */
static inline void init_ugraph_partition(ppart_t *partition, egraph_t *egraph) {
  init_ptr_partition(partition, 0, egraph, (ppart_hash_fun_t) ugraph_hash_arg, (ppart_match_fun_t) ugraph_match_arg);
}




/***********************
 *  STATISTICS RECORD  *
 **********************/

static void init_ugraph_stats(ugraph_stats_t *stats) {
  stats->num_update_props = 0;
  stats->num_lambda_props = 0;
  stats->num_update_conflicts = 0;
  stats->num_lambda_conflicts = 0;
}

static inline void reset_ugraph_stats(ugraph_stats_t *stats) {
  init_ugraph_stats(stats);
}




/******************
 *  UPDATE GRAPH  *
 *****************/

/*
 * Initialize ugraph (to the empty graph)
 */
void init_ugraph(update_graph_t *ugraph, egraph_t *egraph) {
  ugraph->egraph = egraph;

  ugraph->size = 0;
  ugraph->nodes = 0;
  ugraph->class = NULL;
  ugraph->edges = NULL;
  ugraph->tag  = NULL;
  ugraph->mark = NULL;
  ugraph->nclasses = 0;
  ugraph->class2node = NULL;

  init_ugraph_queue(&ugraph->queue);
  init_ugraph_partition(&ugraph->partition, egraph);
  init_lpair_set(&ugraph->lpair_set, egraph->types);

  init_ugraph_stats(&ugraph->stats);

  init_ivector(&ugraph->aux_vector, 10);
  init_ivector(&ugraph->lemma_vector, 10);
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
    ugraph->mark = allocate_bitvector(n);

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
    ugraph->mark = extend_bitvector(ugraph->mark, n);

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
  clr_bit(ugraph->mark, i);

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
  reset_ptr_partition(&ugraph->partition);
  reset_lpair_set(&ugraph->lpair_set);

  reset_ugraph_stats(&ugraph->stats);
  ivector_reset(&ugraph->aux_vector);
  ivector_reset(&ugraph->lemma_vector);
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
  delete_bitvector(ugraph->mark);
  safe_free(ugraph->class2node);

  ugraph->class = NULL;
  ugraph->edges = NULL;
  ugraph->tag = NULL;
  ugraph->mark = NULL;
  ugraph->class2node = NULL;

  delete_ugraph_queue(&ugraph->queue);
  delete_ptr_partition(&ugraph->partition);
  delete_lpair_set(&ugraph->lpair_set);

  delete_ivector(&ugraph->aux_vector);
  delete_ivector(&ugraph->lemma_vector);
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
static void ugraph_add_term(update_graph_t *ugraph, eterm_t t, class_t c, type_t tau) {
  int32_t node;
  int32_t tag;

  node = node_of_class(ugraph, c);
  if (node < 0) {
    tag = egraph_get_lambda_tag(ugraph->egraph, tau);
    node = ugraph_add_node(ugraph, c, tag);
    set_node_of_class(ugraph, c, node);

    // if t is a lambda term: store the pair [tag, sigma]
    // where sigma = range of type tau
    if (egraph_term_is_lambda(ugraph->egraph, t)) {
      lpair_set_add_ftype(&ugraph->lpair_set, tag, tau);
    }
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
static inline int32_t node_of_term(update_graph_t *ugraph, eterm_t t) {
  return node_of_class(ugraph, egraph_term_class(ugraph->egraph, t));
}


/*
 * Add the two edges defined by update term cmp
 */
static void ugraph_add_edges_for_update(update_graph_t *ugraph, composite_t *cmp) {
  int32_t source, target;

  assert(composite_kind(cmp) == COMPOSITE_UPDATE);
  source = node_of_term(ugraph, cmp->child[0]);
  target = node_of_term(ugraph, cmp->id);
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
void build_ugraph(update_graph_t *ugraph) {
  egraph_t *egraph;
  uint32_t i, n;
  type_t tau;
  composite_t *cmp;

  assert(ugraph->nodes == 0 &&
         ptr_partition_is_empty(&ugraph->partition) &&
         lpair_set_is_empty(&ugraph->lpair_set));

  egraph = ugraph->egraph;


  /*
   * First pass: create the nodes and build the lpair_set
   */
  ugraph_resize_classes(ugraph, egraph->classes.nclasses);
  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    tau = egraph_term_real_type(egraph, i);
    if (is_function_type(egraph->types, tau)) {
      ugraph_add_term(ugraph, i, egraph_term_class(egraph, i), tau);
    }
  }


  /*
   * Second pass: add the edges and build the apply term partition
   */
  for (i=0; i<n; i++) {
    cmp = egraph_term_body(egraph, i);
    if (composite_body(cmp)) {
      switch (composite_kind(cmp)) {
      case COMPOSITE_APPLY:
        // add cmp to the partition (if it's a congruence root)
        if (congruence_table_is_root(&egraph->ctable, cmp, egraph->terms.label)) {
          ptr_partition_add(&ugraph->partition, cmp);
        }
        break;

      case COMPOSITE_UPDATE:
        // add cmp as an edge (it it's a congruence root)
        if (congruence_table_is_root(&egraph->ctable, cmp, egraph->terms.label)) {
          ugraph_add_edges_for_update(ugraph, cmp);
        }
        break;

      default:
        break;
      }
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
 * For g = (lambda .. b ..), we add an instance of path => (apply f t1 ... tn) = b
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



/*
 * Check whether c is relevant to propagation
 * - c is relevant if there's another term d such that the arguments of c and d are equal
 *   or if there's a lambda term that has a type compatible with c
 * - for the first part, we check whether c's class in the partition table contains
 *   at least two elements
 *
 * We could do more:
 * - if c and d are in the same class in the partition table
 *   then there's no path from c to d if they have incompatible types
 * - if c and d are already equal in the egraph, then we don't care
 *   whether a path exists
 */

// x must be the node of c->child[0]
static bool compatible_lambda(update_graph_t *ugraph, int32_t x, composite_t *c) {
  type_t tau;

  assert(composite_kind(c) == COMPOSITE_APPLY && 0 <= x && x < ugraph->nodes);

  tau = egraph_term_real_type(ugraph->egraph, c->id); // c has type tau
  return lpair_set_has_match(&ugraph->lpair_set, ugraph->tag[x], tau);
}

// x must be the node of c->child[0]
static bool relevant_apply(update_graph_t *ugraph, int32_t x, composite_t *c) {
  int32_t k;

  k = ptr_partition_get_index(&ugraph->partition, c);
  return k>=0 || compatible_lambda(ugraph, x, c);
}



/*
 * Return a term whose signature matches [ label[y], label[i_1], ..., label[i_n] ]
 * - y = node in the update graph
 * - c = composite of the form (apply f i_1 ... i_n)
 */
static composite_t *find_modified_application(update_graph_t *ugraph, int32_t y, composite_t *c) {
  egraph_t *egraph;
  signature_t *sgn;
  elabel_t *label;

  assert(composite_kind(c) == COMPOSITE_APPLY);
  assert(0 <= y && y < ugraph->nodes);

  egraph = ugraph->egraph;
  label = egraph->terms.label;
  sgn = &egraph->sgn;
  signature_modified_apply2(c, pos_label(ugraph->class[y]), label, sgn);
  return congruence_table_find(&egraph->ctable, sgn, label);
}


/*
 * Return the lambda term in node y
 * - return NULL if there's no lambda term in this node
 *
 * TODO: for this to work, we must change egraph.c so that the theory
 * variable attached to a function class is the representative lambda
 * term for that class.
 */
static composite_t *find_lambda_term(update_graph_t *ugraph, int32_t y) {
  egraph_t *egraph;
  composite_t *d;
  class_t c;
  eterm_t lambda;

  assert(0 <= y && y < ugraph->nodes);

  egraph= ugraph->egraph;
  d = NULL;
  c = ugraph->class[y];
  assert(egraph_class_is_function(egraph, c));

  lambda = egraph_class_thvar(egraph, c);
  if (lambda >= 0) {
    // lambda is an egraph term
    d = egraph_term_body(egraph, lambda);
    assert(composite_body(d) && composite_kind(d) == COMPOSITE_LAMBDA);
  }

  return d;
}



/*
 * For debugging: check that no node is marked
 */
#ifndef NDEBUG
static bool no_node_is_marked(update_graph_t *ugraph) {
  uint32_t i, n;

  n = ugraph->nodes;
  for (i=0; i<n; i++) {
    if (ugraph_node_is_marked(ugraph, i)) {
      return false;
    }
  }
  return true;
}
#endif


/*
 * Empty the queue and remove the mark of all nodes in the queue
 */
static void ugraph_unmark_queued_nodes(update_graph_t *ugraph, ugraph_queue_t *queue) {
  uint32_t i, n;
  int32_t x;

  n = queue->top;
  for (i=0; i<n; i++) {
    x = queue->data[i].node;
    assert(ugraph_node_is_marked(ugraph, x));
    clear_ugraph_node_mark(ugraph, x);
  }

  reset_ugraph_queue(queue);

  assert(no_node_is_marked(ugraph));
}



/*
 * BASE-LEVEL PROPAGATION
 */

/*
 * Push all unmarked successors of x that can be reached by an edge transparent to c
 * into queue
 */
static void ugraph_push_transparent_successors(update_graph_t *ugraph, ugraph_queue_t *queue, int32_t x, composite_t *c) {
  void **edges;
  composite_t *u;
  uint32_t i, n;
  int32_t y;

  assert(0 <= x && x < ugraph->nodes);

  edges = ugraph->edges[x];
  if (edges != NULL) {
    n = pv_size(edges);
    for (i=0; i<n; i++) {
      u = edges[i];
      if (ptr_tag(u) == 0) {
        // direct edge of the form g := (update f ...) for f in class[x]
        y = node_of_term(ugraph, u->id);
      } else {
        // reverse edge: f := (update g ...) for f in class[x]
        u = untag_ptr(u);
        y = node_of_term(ugraph, term_of_occ(u->child[0]));
      }

      assert(0 <= y && y < ugraph->nodes);

      if (ugraph_node_is_unmarked(ugraph, y) && transparent_edge(ugraph->egraph, u, c)) {
        ugraph_queue_push_next(queue, y, u); // u is not used here
      }
    }
  }
}


/*
 * Propagation through transparent edges
 * - propagate c through all transparent edges from node x
 * - c must be of the form (apply f t_1 ... t_n)
 * - x should be the node for class of f
 *
 * Whenever we find a term d = (apply g t_1 ... t_n) then
 * we add the constraint d == c to the egraph (as a toplevel axiom).
 * - return the number of equalities propagated
 */
static uint32_t ugraph_base_propagate_application(update_graph_t *ugraph, int32_t x, composite_t *c) {
  ugraph_queue_t *queue;
  composite_t *d;
  uint32_t neqs;
  int32_t y;

  queue = &ugraph->queue;
  assert(empty_ugraph_queue(queue) && no_node_is_marked(ugraph));

  neqs = 0;

  ugraph_queue_push_root(queue, x);
  ugraph_mark_node(ugraph, x);
  ugraph_push_transparent_successors(ugraph, queue, x, c);
  ugraph_queue_pop(queue);

  while (! empty_ugraph_queue(queue)) {
    y = ugraph_queue_current_node(queue);

    d = find_modified_application(ugraph, y, c);
    if (d != NULL) {
      if (! egraph_equal_occ(ugraph->egraph, pos_occ(c->id), pos_occ(d->id))) {
        egraph_assert_eq_axiom(ugraph->egraph, pos_occ(c->id), pos_occ(d->id));
        ugraph->stats.num_update_props ++;
        neqs ++;
      }

      /*
       * If d and c are equal, there's no point propagating c to y's neighbors
       * (the propagations we miss now were or will be done when we propagate d) .
       */

    } else {
      d = find_lambda_term(ugraph, y);
      if (d != NULL && !egraph_equal_occ(ugraph->egraph, pos_occ(c->id), d->child[0])) {
        egraph_assert_eq_axiom(ugraph->egraph, pos_occ(c->id), d->child[0]);
        ugraph->stats.num_lambda_props ++;
        neqs ++;
      }

      ugraph_push_transparent_successors(ugraph, queue, y, c);
      ugraph_queue_pop(queue);
    }
  }

  ugraph_unmark_queued_nodes(ugraph, queue);

  return neqs;
}



/*
 * Full propagation at the base level
 * - go through all relevant composite and propagate
 * - return the total number of propagated equalities
 */
uint32_t ugraph_base_propagate(update_graph_t *ugraph) {
  egraph_t *egraph;
  composite_t *c;
  uint32_t i, n, neqs;
  int32_t x;

  neqs = 0;
  egraph = ugraph->egraph;

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    c = egraph_term_body(egraph, i);
    if (composite_body(c) &&
        composite_kind(c) == COMPOSITE_APPLY &&
        congruence_table_is_root(&egraph->ctable, c, egraph->terms.label)) {
      // c is of the form (apply f ... ) is a congruence root
      x = node_of_term(ugraph, term_of_occ(c->child[0])); // x := node of f
      if (relevant_apply(ugraph, x, c)) {
        neqs += ugraph_base_propagate_application(ugraph, x, c);
      }
    }
  }

  return neqs;
}



/*
 * SEARCH FOR INSTANCES OF UPDATE/LAMBDA AXIOMS
 */

/*
 * Push all unmarked successors of x that can be reached by a non-opaque edge for c
 */
static void ugraph_push_successors(update_graph_t *ugraph, ugraph_queue_t *queue, int32_t x, composite_t *c) {
  void **edges;
  composite_t *u, *v;
  uint32_t i, n;
  int32_t y;

  assert(0 <= x && x < ugraph->nodes);

  edges = ugraph->edges[x];
  if (edges != NULL) {
    n = pv_size(edges);
    for (i=0; i<n; i++) {
      u = edges[i];
      v = untag_ptr(u);
      if (ptr_tag(u) == 0) {
        // direct edge of the form g := (update f ...) for f in class[x]
        y = node_of_term(ugraph, u->id);
      } else {
        // reverse edge: f := (update g ...) for f in class[x]
        y = node_of_term(ugraph, term_of_occ(u->child[0]));
      }

      assert(0 <= y && y < ugraph->nodes);

      if (ugraph_node_is_unmarked(ugraph, y) && !opaque_edge(ugraph->egraph, v, c)) {
        ugraph_queue_push_next(queue, y, u);
      }
    }
  }
}


/*
 * Propagate c through non-opaque edges and search for instances
 * the update/lambda axioms.
 * - c must be of the form (apply f t_1 ... t_n)
 * - x should be the node for class of f
 */
static uint32_t ugraph_propagate_application(update_graph_t *ugraph, int32_t x, composite_t *c) {
  ugraph_queue_t *queue;
  composite_t *d;
  uint32_t nlemmas;
  int32_t y;

  queue = &ugraph->queue;
  assert(empty_ugraph_queue(queue) && no_node_is_marked(ugraph));

  nlemmas = 0;

  ugraph_queue_push_root(queue, x);
  ugraph_mark_node(ugraph, x);
  ugraph_push_successors(ugraph, queue, x, c);
  ugraph_queue_pop(queue);

  while (! empty_ugraph_queue(queue)) {
    y = ugraph_queue_current_node(queue);

    d = find_modified_application(ugraph, y, c);
    if (d != NULL) {
      if (! egraph_equal_occ(ugraph->egraph, pos_occ(c->id), pos_occ(d->id))) {
        // found instance of the update axiom
        // TBD
        nlemmas ++;
      }
    } else {
      d = find_lambda_term(ugraph, y);;
      if (d != NULL && !egraph_equal_occ(ugraph->egraph, pos_occ(c->id), d->child[0])) {
        // found instance of the lambda/update axiom
        // TBD
        nlemmas ++;
      }

      ugraph_push_successors(ugraph, queue, y, c);
      ugraph_queue_pop(queue);;
    }
  }

  ugraph_unmark_queued_nodes(ugraph, queue);

  return nlemmas;
}


/*
 * Full propagation
 */
uint32_t ugraph_propagate(update_graph_t *ugraph) {
  egraph_t *egraph;
  composite_t *c;
  uint32_t i, n, nlemmas;
  int32_t x;

  nlemmas = 0;
  egraph = ugraph->egraph;

  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    c = egraph_term_body(egraph, i);
    if (composite_body(c) &&
        composite_kind(c) == COMPOSITE_APPLY &&
        congruence_table_is_root(&egraph->ctable, c, egraph->terms.label)) {
      // c is of the form (apply f ... ) and is a congruence root
      x = node_of_term(ugraph, term_of_occ(c->child[0])); // x := node of f
      if (relevant_apply(ugraph, x, c)) {
        nlemmas += ugraph_propagate_application(ugraph, x, c);
      }
    }
  }

  return nlemmas;
}
