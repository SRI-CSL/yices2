/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * SOLVER FOR FUNCTION/ARRAY THEORY
 */

/*
 * Optimization in final check:
 * - We consider the following equivalence relation between composite terms
 *   in the egraph:
 *     (apply f t_1 ... t_n) may conflict with (apply g u_1 ... u_n)
 *   if t_1 == u_1 ... t_n == u_n (in the egraph)
 *   and (apply f t_1 ... t_n) is not in the same class as
 *   (apply g u_1 ... u_n) in the egraph.
 *
 * - When we check for conflict or extensionality instances, we
 *   don't need to consider (apply f t_1 ... t_n)  if there's
 *   no composite that may conflict with it.
 */

#include <inttypes.h>

#include "io/tracer.h"
#include "model/fun_trees.h"
#include "solvers/funs/fun_solver.h"
#include "solvers/funs/stratification.h"
#include "utils/hash_functions.h"
#include "utils/index_vectors.h"
#include "utils/int_array_sort2.h"
#include "utils/int_hash_classes.h"
#include "utils/memalloc.h"
#include "utils/pointer_vectors.h"
#include "utils/ptr_array_sort2.h"
#include "utils/ptr_partitions.h"


#define TRACE 0

#if TRACE

#include <stdio.h>

#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/funs/fun_solver_printer.h"

#endif



/**********************
 *  EDGE DESCRIPTORS  *
 *********************/

/*
 * Allocate an edge object of arity n
 */
static inline fun_edge_t *new_edge(uint32_t n) {
  assert(n <= MAX_COMPOSITE_ARITY);
  return (fun_edge_t *) safe_malloc(sizeof(fun_edge_t) + n * sizeof(occ_t));
}


/*
 * Create the edge for an update composite u
 * - x = source variable
 * - y = target variable
 * - u = update composite
 */
static fun_edge_t *make_edge(thvar_t x, thvar_t y, composite_t *u) {
  fun_edge_t *e;
  uint32_t i, n;

  assert(composite_kind(u) == COMPOSITE_UPDATE && composite_arity(u) >= 3);

  // u is (update f i_1 ... i_n v) where i_1,..., i_n are the edge labels
  n = composite_arity(u) - 2;
  e = new_edge(n);
  e->source = x;
  e->target = y;
  for (i=0; i<n; i++) {
    e->index[i] = composite_child(u, i+1);
  }
  return e;
}






/****************
 *  EDGE TABLE  *
 ***************/

/*
 * Initialize: default size
 */
static void init_edge_table(fun_edgetable_t *table) {
  assert(DEF_FUN_EDGETABLE_SIZE < MAX_FUN_EDGETABLE_SIZE);

  table->size = DEF_FUN_EDGETABLE_SIZE;
  table->nedges = 0;
  table->data = (fun_edge_t **) safe_malloc(DEF_FUN_EDGETABLE_SIZE * sizeof(fun_edge_t *));
}


/*
 * Make the table 50% larger
 */
static void extend_edge_table(fun_edgetable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_FUN_EDGETABLE_SIZE) {
    out_of_memory();
  }
  table->data = (fun_edge_t **) safe_realloc(table->data, n * sizeof(fun_edge_t *));
  table->size = n;
}


/*
 * Remove all edges of index >= n
 */
static void shrink_edge_table(fun_edgetable_t *table, uint32_t n) {
  uint32_t i, m;

  assert(n <= table->nedges);

  m = table->nedges;
  for (i=n; i<m; i++) {
    safe_free(table->data[i]);
  }
  table->nedges = n;
}


/*
 * Empty the table: delete all edge objects
 */
static void reset_edge_table(fun_edgetable_t *table) {
  shrink_edge_table(table, 0);
}


/*
 * Delete the table
 */
static void delete_edge_table(fun_edgetable_t *table) {
  shrink_edge_table(table, 0);
  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new edge index i
 * - data[i] is not initialized
 */
static int32_t edge_table_alloc(fun_edgetable_t *table) {
  uint32_t i;

  i = table->nedges;
  if (i == table->size) {
    extend_edge_table(table);
  }
  assert(i < table->size);
  table->nedges = i+1;

  return i;
}






/********************
 *  VARIABLE TABLE  *
 *******************/

/*
 * Initialize table with default size
 */
static void init_fun_vartable(fun_vartable_t *table) {
  uint32_t n;

  assert(DEF_FUN_VARTABLE_SIZE < MAX_FUN_VARTABLE_SIZE);

  n = DEF_FUN_VARTABLE_SIZE;
  table->size = n;
  table->nvars = 0;
  table->type = (type_t *) safe_malloc(n * sizeof(type_t));
  table->arity = (uint32_t *) safe_malloc(n * sizeof(uint32_t));
  table->fdom = allocate_bitvector(n);
  table->eterm = (eterm_t *) safe_malloc(n * sizeof(eterm_t));
  table->edges = (int32_t **) safe_malloc(n * sizeof(int32_t *));
  table->root = (thvar_t *) safe_malloc(n * sizeof(thvar_t));
  table->next = (thvar_t *) safe_malloc(n * sizeof(thvar_t));
  table->pre = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->base = (int32_t *) safe_malloc(n * sizeof(int32_t));
  table->app = (void ***) safe_malloc(n * sizeof(void **));
  table->mark = allocate_bitvector(n);
}


/*
 * Make the table 50% larger
 */
static void extend_fun_vartable(fun_vartable_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_FUN_VARTABLE_SIZE) {
    out_of_memory();
  }

  table->type = (type_t *) safe_realloc(table->type, n * sizeof(type_t));
  table->arity = (uint32_t *) safe_realloc(table->arity, n * sizeof(uint32_t));
  table->fdom = extend_bitvector(table->fdom, n);
  table->eterm = (eterm_t *) safe_realloc(table->eterm, n * sizeof(eterm_t));
  table->edges = (int32_t **) safe_realloc(table->edges, n * sizeof(int32_t *));
  table->root = (thvar_t *) safe_realloc(table->root, n * sizeof(thvar_t));
  table->next = (thvar_t *) safe_realloc(table->next, n * sizeof(thvar_t));
  table->pre = (int32_t *) safe_realloc(table->pre, n * sizeof(int32_t));
  table->base = (int32_t *) safe_realloc(table->base, n * sizeof(int32_t));
  table->app = (void ***) safe_realloc(table->app, n * sizeof(void **));
  table->mark = extend_bitvector(table->mark, n);
  table->size = n;
}


/*
 * Remove all variables of index >= n
 */
static void shrink_fun_vartable(fun_vartable_t *table, uint32_t n) {
  uint32_t i, m;

  m = table->nvars;
  assert(n <= m);
  for (i=n; i<m; i++) {
    delete_index_vector(table->edges[i]);
  }
  table->nvars = n;
}


/*
 * Empty the table
 */
static void reset_fun_vartable(fun_vartable_t *table) {
  shrink_fun_vartable(table, 0);
}


/*
 * Delete the table
 */
static void delete_fun_vartable(fun_vartable_t *table) {
  shrink_fun_vartable(table, 0);

  safe_free(table->type);
  safe_free(table->arity);
  delete_bitvector(table->fdom);
  safe_free(table->eterm);
  safe_free(table->edges);
  safe_free(table->root);
  safe_free(table->next);
  safe_free(table->pre);
  safe_free(table->base);
  safe_free(table->app);
  delete_bitvector(table->mark);

  table->type = NULL;
  table->arity = NULL;
  table->fdom = NULL;
  table->eterm = NULL;
  table->edges = NULL;
  table->root = NULL;
  table->next = NULL;
  table->pre = NULL;
  table->base = NULL;
  table->app = NULL;
  table->mark = NULL;
}


/*
 * Allocate a new variable index x
 * - type, arity, etc. are not initialized
 */
static thvar_t fun_vartable_alloc(fun_vartable_t *table) {
  uint32_t i;

  i = table->nvars;
  if (i == table->size) {
    extend_fun_vartable(table);
  }
  table->nvars = i+1;

  return i;
}



/*
 * Check type of variable x
 */
static inline type_t fun_var_type(fun_vartable_t *table, thvar_t x) {
  assert(0 <= x && x < table->nvars);
  return table->type[x];
}


/*
 * Check whether variable x has a finite domain
 */
static inline bool fun_var_has_finite_domain(fun_vartable_t *table, thvar_t x) {
  assert(0 <= x && x < table->nvars);
  return tst_bit(table->fdom, x);
}

static inline bool fun_var_has_infinite_domain(fun_vartable_t *table, thvar_t x) {
  return ! fun_var_has_finite_domain(table, x);
}




/***********
 *  QUEUE  *
 **********/

/*
 * Initialization: use default size
 */
static void init_fun_queue(fun_queue_t *queue) {
  uint32_t n;

  n = DEF_FUN_QUEUE_SIZE;
  assert(n < MAX_FUN_QUEUE_SIZE);

  queue->size = n;
  queue->top = 0;
  queue->ptr = 0;
  queue->data = (thvar_t *) safe_malloc(n * sizeof(thvar_t));
}


/*
 * Make the queue 50% larger
 */
static void extend_fun_queue(fun_queue_t *queue) {
  uint32_t n;

  n = queue->size + 1;
  n += n>>1;
  if (n >= MAX_FUN_QUEUE_SIZE) {
    out_of_memory();
  }

  queue->data = (thvar_t *) safe_realloc(queue->data, n * sizeof(thvar_t));
  queue->size = n;
}


/*
 * Delete the queue
 */
static void delete_fun_queue(fun_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}


/*
 * Reset the queue
 */
static void reset_fun_queue(fun_queue_t *queue) {
  queue->top = 0;
  queue->ptr = 0;
}


/*
 * Push a vertex x at the end of the queue
 */
static void fun_queue_push(fun_queue_t *queue, thvar_t x) {
  uint32_t i;

  i = queue->top;
  if (i == queue->size) {
    extend_fun_queue(queue);
  }
  assert(i < queue->size);
  queue->data[i] = x;
  queue->top = i+1;
}


/*
 * Check whether the queue is empty
 */
static inline bool empty_fun_queue(fun_queue_t *queue) {
  return queue->top == queue->ptr;
}


/*
 * Get the first element of the queue and increment ptr
 */
static thvar_t fun_queue_pop(fun_queue_t *queue) {
  uint32_t i;
  thvar_t x;

  i = queue->ptr;
  assert(i < queue->top);
  x = queue->data[i];
  queue->ptr = i+1;

  return x;
}







/*********************
 *   PUSH/POP STACK  *
 ********************/

/*
 * Initialize the stack
 */
static void init_fun_trail_stack(fun_trail_stack_t *stack) {
  assert(DEF_FUN_TRAIL_SIZE < MAX_FUN_TRAIL_SIZE);

  stack->size = DEF_FUN_TRAIL_SIZE;
  stack->top = 0;
  stack->data = (fun_trail_t *) safe_malloc(DEF_FUN_TRAIL_SIZE * sizeof(fun_trail_t));
}


/*
 * Make the stack 50% larger
 */
static void extend_fun_trail_stack(fun_trail_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n >= MAX_FUN_TRAIL_SIZE) {
    out_of_memory();
  }

  stack->data = (fun_trail_t *) safe_realloc(stack->data, n * sizeof(fun_trail_t));
  stack->size = n;
}


/*
 * Empty the stack
 */
static inline void reset_fun_trail_stack(fun_trail_stack_t *stack) {
  stack->top = 0;
}


/*
 * Delete the stack
 */
static void delete_fun_trail_stack(fun_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Save data for the current base level:
 * - nv = number of variables
 * - ne = number of edges
 */
static void fun_trail_stack_save(fun_trail_stack_t *stack, uint32_t nv, uint32_t ne) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_fun_trail_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].nvars = nv;
  stack->data[i].nedges = ne;
  stack->top = i + 1;
}


/*
 * Get the top record
 */
static inline fun_trail_t *fun_trail_stack_top(fun_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}


/*
 * Remove the top record
 */
static inline void fun_trail_stack_pop(fun_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}




/**********************
 *  STATISTIC RECORD  *
 *********************/

static void init_fun_solver_statistics(fun_solver_stats_t *stat) {
  stat->num_init_vars = 0;
  stat->num_init_edges = 0;
  stat->num_update_axiom1 = 0;
  stat->num_update_axiom2 = 0;
  stat->num_extensionality_axiom = 0;
}

static inline void reset_fun_solver_statistics(fun_solver_stats_t *stat) {
  init_fun_solver_statistics(stat);
}





/*******************
 *  VALUE VECTOR   *
 ******************/

/*
 * Allocate and initialize the value vector:
 * - its size is the number of variables
 * - value[x] is set to NULL for all x
 */
static void fun_solver_init_values(fun_solver_t *solver) {
  map_t **tmp;
  uint32_t i, n;

  assert(solver->value == NULL);

  n = solver->vtbl.nvars;
  tmp = (map_t **) safe_malloc(n * sizeof(map_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }
  solver->value = tmp;
  solver->value_size = n;
}


/*
 * Delete the value vector and all the maps it contains.
 */
static void fun_solver_delete_values(fun_solver_t *solver) {
  map_t **v;
  uint32_t i, n;

  assert(solver->value != NULL);

  v = solver->value;
  n = solver->value_size;
  for (i=0; i<n; i++) {
    if (v[i] != NULL) {
      free_map(v[i]);
    }
  }

  safe_free(v);

  solver->value = NULL;
  solver->value_size = 0;
}



/*
 * Allocate and initialize the base_map vector
 * - its size = n (should be equal to num_bases)
 * - base_map[i] is initialized to NULL for all connected components
 */
static void fun_solver_init_base_maps(fun_solver_t *solver, uint32_t n) {
  map_t **tmp;
  uint32_t i;

  assert(solver->base_map == NULL);

  tmp = (map_t **) safe_malloc(n * sizeof(map_t *));
  for (i=0; i<n; i++) {
    tmp[i] = NULL;
  }
  solver->base_map = tmp;
  solver->base_map_size = n;
}


/*
 * Delete the base_map vector and all the maps it contains
 */
static void fun_solver_delete_base_maps(fun_solver_t *solver) {
  map_t **v;
  uint32_t i, n;

  assert(solver->base_map != NULL);

  v = solver->base_map;
  n = solver->base_map_size;
  for (i=0; i<n; i++) {
    if (v[i] != NULL) {
      free_map(v[i]);
    }
  }
  safe_free(v);

  solver->base_map = NULL;
  solver->base_map_size = 0;
}



/*
 * HASH MAP FOR FRESH PARTICLES
 */

/*
 * Return the map. allocate and initialize it if necessary
 */
static int_hmap2_t *fun_solver_get_fresh_hmap(fun_solver_t *solver) {
  int_hmap2_t *map;

  map = solver->fresh_hmap;
  if (map == NULL) {
    map = (int_hmap2_t *) safe_malloc(sizeof(int_hmap2_t));
    init_int_hmap2(map, 0); // use the default size
    solver->fresh_hmap = map;
  }

  return map;
}


/*
 * Delete the map if it exists
 */
static void fun_solver_delete_fresh_hmap(fun_solver_t *solver) {
  int_hmap2_t *map;

  map = solver->fresh_hmap;
  if (map != NULL) {
    delete_int_hmap2(map);
    safe_free(map);
    solver->fresh_hmap = NULL;
  }
}



/***************************************
 *  UTILITIES FOR EXPLORING THE GRAPH  *
 **************************************/

/*
 * Edge descriptor of edge i
 */
static inline fun_edge_t *get_edge(fun_edgetable_t *table, int32_t i) {
  assert(0 <= i && i < table->nedges);
  return table->data[i];
}

/*
 * Node adjacent to x via edge i
 * - x must be either the source or the target of edge i
 */
static thvar_t adjacent_node(fun_edgetable_t *table, thvar_t x, int32_t i) {
  fun_edge_t *e;

  e = get_edge(table, i);
  assert(e->source == x || e->target == x);
  return e->source ^ e->target ^ x;
}


/*
 * Root of the node adjacent to x via edge i
 */
static inline thvar_t adjacent_root(fun_solver_t *solver, thvar_t x, int32_t i) {
  return solver->vtbl.root[adjacent_node(&solver->etbl, x, i)];
}


/*
 * Predecessor of x
 * - get the root var y that precedes root var x via edge i
 * - i = vtbl->pre[x] must be the edge id for an edge u <---> t with
 *   t in class of x  and u in class of y
 */
static thvar_t previous_root(fun_solver_t *solver, thvar_t x, int32_t i) {
  fun_edge_t *e;
  thvar_t y, z;

  e = get_edge(&solver->etbl, i);
  y = solver->vtbl.root[e->source];
  z = solver->vtbl.root[e->target];
  assert(x == y || x == z);
  return (x == y) ? z : y;
}


/*
 * Node in class of x that's the real source or target of edge i
 * - x must be a root variable
 * - i must be the index of an edge whose source or target has root x
 */
static thvar_t node_for_root(fun_solver_t *solver, thvar_t x, int32_t i) {
  fun_edge_t *e;

  e = get_edge(&solver->etbl, i);
  if (solver->vtbl.root[e->source] == x) {
    return e->source;
  } else {
    assert(solver->vtbl.root[e->target] == x);
    return e->target;
  }
}






/***************************
 *  ARRAY/FUNCTION AXIOMS  *
 **************************/

/*
 * AXIOM 1: ((update f i_1 ... i_n v) i_1 ... i_n) == v
 */

/*
 * Create an instance of update axiom 1:
 * - u must be (update f i_1 ... i_n v)
 * - t must be the term whose body is u
 * - tau is the type of u (and t)
 */
static void fun_solver_update_axiom1(fun_solver_t *solver, eterm_t t, composite_t *u, type_t tau) {
  egraph_t *egraph;
  ivector_t *v;
  uint32_t i, n;
  eterm_t a;
  literal_t eq;

  // t is (update f i_1 ... i_n v)
  assert(composite_kind(u) == COMPOSITE_UPDATE && composite_arity(u) >= 3 && u->id == t);

  egraph = solver->egraph;

  // create (t i_1 ... i_n)
  v = &solver->aux_vector;
  assert(v->size == 0);
  n = composite_arity(u) - 2;
  for (i=0; i<n; i++) {
    ivector_push(v, composite_child(u, i+1));
  }
  a = egraph_make_apply(egraph, pos_occ(t), n, v->data, function_type_range(solver->types, tau));

  // assert the equality (a == v)
  if (solver->decision_level == solver->base_level) {
    egraph_assert_eq_axiom(egraph, pos_occ(a), composite_child(u, n+1));
  } else {
    eq = egraph_make_eq(egraph, pos_occ(a), composite_child(u, n+1));
    add_unit_clause(solver->core, eq);
  }

  // cleanup
  ivector_reset(v);

  // increment counter
  solver->stats.num_update_axiom1 ++;
}




/*
 * UPDATE AXIOM 2: GENERALIZED FORM
 *
 * Instances are created from two terms (f i_1 ... i_n) and (g j_1 ... j_n) and
 * a path in the graph from a source x to a target variable y. The path is formed
 * of a list of edges (x_1 --> y_1) ... (x_t --> y_t) with the following property:
 * - y_k is in the class of x_{k+1} for k= 1,.., t-1
 * - f is in the class of variable x_1 = class of x
 * - g is in the class of variable y_t = class of y
 *
 * Let [k_11 ... k_1n], ..., [k_t1 ... k_tn] be the labels on the successive edges,
 * and let u_i = eterm[x_i] and v_i = eterm[y_i] then the instance derived from
 * (f i_1 ... i_n) and (g j_1 ... j_n) is of the form:
 *
 *       (f = u_1 and v_1 = u_2 ... v_{t-1} = u_t and v_t = g and i_1 = j_1 ... i_n = j_n)
 *   and (not (i_1 = k_11 and ... and i_n = k_1n))
 *   ...
 *   and (not (i_1 = k_t1 and ... and i_n = k_tn))
 *   implies (f i_1 ... i_n) = (g j_1 ... j_n)
 *
 */


/*
 * Given two composites
 * - c = (apply f i_1 ... i_n)
 * - d = (apply g j_1 ... j_n),
 * add the atoms (i_1 = j_1) ... (i_n = j_n) to vector *v.
 * (skip the trivial atoms where i_t and j_t are equal).
 */
static void collect_equal_arg_atoms(fun_solver_t *solver, composite_t *c, composite_t *d, ivector_t *v) {
  egraph_t *egraph;
  uint32_t i, n;
  occ_t u1, u2;
  literal_t l;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_kind(d) == COMPOSITE_APPLY &&
         composite_arity(c) == composite_arity(d));

  egraph = solver->egraph;
  n = composite_arity(c);
  assert (n >= 2);
  for (i=1; i<n; i++) {
    u1 = composite_child(c, i);
    u2 = composite_child(d, i);
    if (u1 != u2) {
      l = egraph_make_eq(egraph, u1, u2);
      ivector_push(v, l);
    }
  }
}


/*
 * Given
 * - c = (apply f i_1 ... i_n)
 * - x = a root variable
 * - k = an edge index
 * add the atom (f = u) to vector v,  where u = term attached to the extremity of k
 * that's in the same class as x.
 */
static void add_equal_fun_and_node_atom(fun_solver_t *solver, composite_t *c, thvar_t x, int32_t k, ivector_t *v) {
  thvar_t y;
  occ_t f, u;
  literal_t l;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_arity(c) >= 1);

  f = composite_child(c, 0);
  y = node_for_root(solver, x, k);
  assert(solver->vtbl.eterm[y] != null_eterm);
  u = pos_occ(solver->vtbl.eterm[y]);
  if (f != u) {
    l = egraph_make_eq(solver->egraph, f, u);
    ivector_push(v, l);
  }
}


/*
 * Given the composites c and d and a source var x and target var y
 * collect the atoms for the path from x to y: add all atoms to vector v.
 */
static void collect_path_atoms(fun_solver_t *solver, thvar_t x, thvar_t y, composite_t *c, composite_t *d, ivector_t *v) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  thvar_t z, u;
  literal_t l;
  int32_t k;

  egraph = solver->egraph;
  vtbl = &solver->vtbl;

  // end node: y. add the constraint (g == extremity of edge k in class of y)
  k = vtbl->pre[y];
  assert(k >= 0 && k != null_fun_pred);
  add_equal_fun_and_node_atom(solver, d, y, k, v);

  // intermediate nodes
  y = previous_root(solver, y, k);
  while (y != x) {
    z = node_for_root(solver, y, k); // extremity of edge k in class of y
    k = vtbl->pre[y];                // previous edge on the path
    u = node_for_root(solver, y, k); // extremity of that edge in class of y
    assert(vtbl->root[z] == y && vtbl->root[u] == y);
    if (u != z) {
      l = egraph_make_eq(egraph, pos_occ(vtbl->eterm[z]), pos_occ(vtbl->eterm[u]));
      ivector_push(v, l);
    }
    y = previous_root(solver, y, k);
  }

  // source node: x. add the constraint (f == extremity of edge k in class of x)
  add_equal_fun_and_node_atom(solver, c, x, k, v);
}



/*
 * Create the conjunct (i_1 == j_1 and ... and i_n == j_n) for an apply term and an edge
 * - c must be (apply f i_1 ... i_n) for some f
 * - e must be an edge with label [j_1 ... j_n]
 */
static literal_t apply_edge_equal_args(fun_solver_t *solver, composite_t *c, fun_edge_t *e) {
  egraph_t *egraph;
  ivector_t *v;
  uint32_t i, n;
  literal_t l;

  assert(composite_kind(c) == COMPOSITE_APPLY &&
         composite_arity(c) == 1 + solver->vtbl.arity[e->source]);

  egraph = solver->egraph;
  n = composite_arity(c);
  if (n == 2) {
    l = egraph_make_eq(egraph, composite_child(c, 1), e->index[0]);

#if TRACE
    printf("edge constraint: f!%"PRId32" --> f!%"PRId32"\n", e->source, e->target);
    print_literal(stdout, l);
    printf(" := ");
    print_egraph_atom_of_literal(stdout, egraph, l);
    printf("\n");
#endif

  } else {
    assert(n >= 3);
    v = &solver->aux_vector;
    assert(v->size == 0);
    for (i=1; i<n; i++) {
      l = egraph_make_eq(egraph, composite_child(c, i), e->index[i-1]);
      ivector_push(v, l);
    }
    l = mk_and_gate(solver->gate_manager, v->size, v->data);

#if TRACE
    printf("edge constraint: f!%"PRId32" --> f!%"PRId32"\n", e->source, e->target);
    print_literal(stdout, l);
    printf(" := (AND");
    for (i=0; i<v->size; i++) {
      print_egraph_atom_of_literal(stdout, egraph, v->data[i]);
    }
    printf(")\n");
#endif

    ivector_reset(v);
  }

  return l;
}



/*
 * Construct the atom (eq (f i_1 ... i_n) (g j_1 ... j_n)) for two apply terms
 * - c = (f i_1 ... i_n)
 * - d = (g j_1 ... j_n)
 */
static inline literal_t equal_applies(fun_solver_t *solver, composite_t *c, composite_t *d) {
  return egraph_make_eq(solver->egraph, pos_occ(c->id), pos_occ(d->id));
}







/*
 * EXTENSIONALITY AXIOM
 *
 * The axiom for two variables f and g is
 *    (OR (= f g) (/= (f i_1 ... i_n) (g i_1 ... i_n)))
 * where i_1, ..., i_n are fresh skolem constants.
 */

/*
 * Create fresh skolem constants in the egraph for the domain of type tau
 * - tau must be a function type
 * - the skolem constants are added to vector v (as a vector of egraph occurrences)
 */
static void fun_solver_skolem_domain(fun_solver_t *solver, type_t tau, ivector_t *v) {
  function_type_t *d;
  egraph_t *egraph;
  uint32_t i, n;
  eterm_t t;

  egraph = solver->egraph;
  d = function_type_desc(solver->types, tau);
  n = d->ndom;
  for (i=0; i<n; i++) {
    t = egraph_make_variable(egraph, d->domain[i]);
    ivector_push(v, pos_occ(t));
  }
}


/*
 * Range of variable x:
 * - x has function type tau = [tau_1 ... tau_n --> sigma]
 * - the range is sigma
 */
static inline type_t fun_var_range_type(fun_solver_t *solver, thvar_t x) {
  return function_type_range(solver->types, solver->vtbl.type[x]);
}

/*
 * Create the extensionality axiom for (x != y)
 * - x and y must have the same domain
 */
static void fun_solver_extensionality_axiom(fun_solver_t *solver, thvar_t x, thvar_t y) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  ivector_t *v;
  eterm_t t, u;
  literal_t l1, l2;

  assert(0 <= x && x < solver->vtbl.nvars && 0 <= y && y < solver->vtbl.nvars && x != y);

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  v = &solver->aux_vector;
  assert(v->size == 0);
  fun_solver_skolem_domain(solver, vtbl->type[x], v);

  t = egraph_make_apply(egraph, pos_occ(vtbl->eterm[x]), v->size, v->data, fun_var_range_type(solver, x));
  u = egraph_make_apply(egraph, pos_occ(vtbl->eterm[y]), v->size, v->data, fun_var_range_type(solver, y));
  l1 = egraph_make_eq(egraph, pos_occ(t), pos_occ(u));
  l2 = egraph_make_eq(egraph, pos_occ(vtbl->eterm[x]), pos_occ(vtbl->eterm[y]));

#if 0
  printf("---> ARRAY SOLVER: extensionality axiom for f!%"PRId32" /= f!%"PRId32" ----\n", x, y);
#endif

#if TRACE
  printf("\n---- Extensionality axiom for f!%"PRId32" /= f!%"PRId32" ----\n", x, y);
  print_eterm_def(stdout, solver->egraph, vtbl->eterm[x]);
  print_eterm_def(stdout, solver->egraph, vtbl->eterm[y]);
  printf("New terms:\n");
  print_eterm_def(stdout, egraph, t);
  print_eterm_def(stdout, egraph, u);
  printf("Atoms:\n");
  print_literal(stdout, l1);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, egraph, l1);
  printf("\n");
  print_literal(stdout, l2);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, egraph, l2);
  printf("\n");
  printf("Clause:\n");
  printf("  (OR ");
  print_literal(stdout, not(l1));
  printf(" ");
  print_literal(stdout, l2);
  printf(")\n\n");
#endif

  add_binary_clause(solver->core, not(l1), l2);

  ivector_reset(v);

  solver->stats.num_extensionality_axiom ++;
}




/************************************
 *  COLLECT ROOTS AND APPLICATIONS  *
 ***********************************/

/*
 * Find root variable for variable x
 * - we pick the theory variable in the egraph class of term of x
 */
static inline thvar_t root_var(fun_solver_t *solver, thvar_t x) {
  egraph_t *egraph;
  eterm_t t;

  assert(0 <= x && x < solver->vtbl.nvars);
  egraph = solver->egraph;
  t = solver->vtbl.eterm[x];
  return egraph_class_thvar(egraph, egraph_term_class(egraph, t));
}


/*
 * Build the equivalence classes
 * - set root[x] for all variables
 * - construct the list of elements for every root variable x
 */
static void fun_solver_build_classes(fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  // set the roots and initialize lists
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    x = root_var(solver, i);
    assert(x != null_thvar);
    vtbl->root[i] = x;
    if (x == i) {
      vtbl->next[i] = null_thvar;
    }
  }

  // add all elements to the root's list
  for (i=0; i<n; i++) {
    x = vtbl->root[i];
    if (x != i) {
      vtbl->next[i] = vtbl->next[x];
      vtbl->next[x] = i;
    }
  }
}


/*
 * Assign base label k to all root variables connected to x
 * (including x)
 * - x must be a root
 * - k must be non-negative
 */
static void fun_solver_label_component(fun_solver_t *solver, thvar_t x, int32_t k) {
  fun_queue_t *queue;
  fun_vartable_t *vtbl;
  int32_t *edges;
  thvar_t y;
  uint32_t n, i;
  int32_t j;

  vtbl = &solver->vtbl;
  queue = &solver->queue;
  assert(queue->top == 0 && queue->ptr == 0);

  fun_queue_push(queue, x);
  vtbl->base[x] = k;
  while (! empty_fun_queue(queue)) {
    x = fun_queue_pop(queue);
    assert(vtbl->base[x] == k && vtbl->root[x] == x);
    do {
      // explore edges incident to x's class
      edges = vtbl->edges[x];
      if (edges != NULL) {
        n = iv_size(edges);
        for (i=0; i<n; i++) {
          j = edges[i];
          y = adjacent_root(solver, x, j);
          if (vtbl->base[y] < 0) {
            fun_queue_push(queue, y);
            vtbl->base[y] = k;
          }
        }
      }
      x = vtbl->next[x];
    } while (x != null_thvar);
  }

  reset_fun_queue(queue);
}


/*
 * Compute the connected components
 * - all root variables in the same connected component are assigned the same label
 *   (stored in base[x]).
 * - set bases_ready flag to true
 * - store the number of connected components in num_bases
 */
static void fun_solver_build_components(fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;
  int32_t l;

  l = 0;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i && vtbl->base[i] < 0) {
      fun_solver_label_component(solver, i, l);
      l ++;
    }
  }

  solver->bases_ready = true;
  solver->num_bases = l;
}




/*
 * Cleanup:
 * - delete the vectors vtbl->app[x] for all roots
 * - reset vtbl->base[x] to -1
 * - reset apps_ready and bases_ready to false
 */
static void fun_solver_cleanup(fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      delete_ptr_vector(vtbl->app[i]);
      vtbl->app[i] = NULL;
      vtbl->base[i] = -1;
    }
    assert(vtbl->base[i] == -1 && vtbl->app[i] == NULL);
  }

  solver->apps_ready = false;
  solver->bases_ready = false;
}









/***********************************************
 *  EQUIVALENCE AND ORDER BETWEEN APPLY TERMS  *
 **********************************************/

/*
 * For each root variable x, we store a set of apply terms in app[x].
 * This set encodes what is known about x as a partial mapping.
 * If (f i_1 ... i_n) has egraph label C and  belongs to app[x]
 * then x maps the tuple (L(i_1) ... L(i_n)) to C, where
 *  L(i_k) is the label of i_k in the egraph.
 *
 * To normalize app[x], we sort the set using the order:
 *  (f i_1 ... i_n) <= (g j_1 ... j_n) if
 * [L(i_1), ... ,L(i_n)] <= [L(j_1), ..., L(j_n)] in lexicographic order.
 *
 * Two apply terms (f i_1 ... i_n) and (g j_1 ... j_n) are equivalent if
 *  L(i_1) = L(j_1) ... L(i_n) = L(j_n).
 */

/*
 * Test whether c and d are equivalent
 */
static bool app_equiv(egraph_t *egraph, composite_t *c, composite_t *d) {
  uint32_t i, n;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_kind(d) == COMPOSITE_APPLY &&
         composite_arity(c) == composite_arity(d));

  n = composite_arity(c);
  for (i=1; i<n; i++) {
    if (! egraph_equal_occ(egraph, composite_child(c, i), composite_child(d, i))) {
      return false;
    }
  }
  return true;
}


/*
 * Comparison between c and d:
 * - return a negative number if c < d
 * - return 0 if c = d
 * - return a positive number if c > d
 */
static int32_t app_cmp(egraph_t *egraph, composite_t *c, composite_t *d) {
  uint32_t i, n;
  elabel_t l1, l2;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_kind(d) == COMPOSITE_APPLY &&
         composite_arity(c) == composite_arity(d));

  n = composite_arity(c);
  for (i=1; i<n; i++) {
    l1 = egraph_label(egraph, composite_child(c, i));
    l2 = egraph_label(egraph, composite_child(d, i));
    if (l1 != l2) {
      return (l1 - l2); // negative if l1 < l2, positive if l1 > l2
    }
  }

  return 0;
}


/*
 * Test whether c precedes d in the order (strictly)
 */
static bool app_lt(egraph_t *egraph, composite_t *c, composite_t *d) {
  return app_cmp(egraph, c, d) < 0;
}


/*
 * Sort vector v of composites and remove equivalent elements
 * - v must be non NULL
 */
static void normalize_app_vector(fun_solver_t *solver, void **v) {
  egraph_t *egraph;
  uint32_t i, j, n;
  composite_t *c, *d;

  assert(v != NULL);

  egraph = solver->egraph;
  n = pv_size(v);

  if (n > 0) {
    ptr_array_sort2(v, n, egraph, (ptr_cmp_fun_t) app_lt);

    // remove duplicates
    c = v[0];
    j = 1;
    for (i=1; i<n; i++) {
      d = v[i];
      if (! app_equiv(egraph, c, d)) {
        v[j] = d;
        c = d;
        j ++;
      } else {
        assert(egraph_equal_terms(egraph, c->id, d->id));
      }
    }

    // update size of v
    ptr_vector_shrink(v, j);
  }
}



/*
 * Normalize the app vectors of all the roots
 * - set apps_ready flag to true
 */
static void fun_solver_normalize_apps(fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i && vtbl->app[i] != NULL) {
      normalize_app_vector(solver, vtbl->app[i]);
    }
  }

  solver->apps_ready = true;
}





/********************************************
 *  PROPAGATION/CHECK FOR UPDATE CONFLICTS  *
 *******************************************/

/*
 * If x is a root variable and c = (apply f i_1 ... i_n) is a composite with class[f] == x
 * then we propagate that (apply z i_1 ... i_n) must be equal to (apply f i_1 ... i_n) for
 * all nodes z connected to x via a path that does not mask i_1 ... i_n.
 *
 * A path masks i_1 ... i_n, if it contains an edge labelled by [j_1 ... j_n] and
 * j_1 == i_1, ..., j_n == i_n holds in the egraph.
 *
 * There's a conflict if there's a composite d congruent to (apply z
 * i_1 ... i_n) that's in a different equivalence class than c in
 * the egraph.
 *
 * If a conflict is found, we add instances of axiom2 to the core.
 * Otherwise, we add c to app[root[z]] for all z found along the way.
 */


/*
 * Check whether edge i is masking for application c
 */
static bool masking_edge(fun_solver_t *solver, int32_t i, composite_t *c) {
  egraph_t *egraph;
  fun_edge_t *e;
  uint32_t n, j;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_arity(c) > 0);

  egraph = solver->egraph;
  e = get_edge(&solver->etbl, i);
  n = composite_arity(c) - 1;

  assert(solver->vtbl.arity[e->source] == n);

  for (j=0; j<n; j++) {
    if (! egraph_equal_occ(egraph, e->index[j], composite_child(c, j+1))) {
      return false;
    }
  }
  return true;
}


/*
 * Check whether c = (apply f i_1 ... i_n) and d = (apply g j_1 ... j_n)
 * are equal in the egraph
 */
static inline bool egraph_equal_apps(egraph_t *egraph, composite_t *c, composite_t *d) {
  assert(c->tag == d->tag && composite_kind(c) == COMPOSITE_APPLY);
  return egraph_equal_terms(egraph, c->id, d->id);
}


/*
 * Negate all literals in vector v
 */
static void negate_vector(ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    v->data[i] = not(v->data[i]);
  }
}


#if TRACE
/*
 * For debugging/trace: return the length of the path from x to z
 */
static uint32_t path_length(fun_solver_t *solver, thvar_t x, thvar_t z) {
  fun_vartable_t *vtbl;
  int32_t i;
  thvar_t y;
  uint32_t n;

  vtbl = &solver->vtbl;

  n = 0;
  y = z;
  do {
    n ++;
    i = vtbl->pre[y];
    y = previous_root(solver, y, i);
  } while (y != x);

  return n;
}

#endif


/*
 * Add instance of the update2 axiom corresponding to the non-masking
 * path from x to z encoded in the vtbl->pre fields.
 * - x = source node
 * - z = end node
 * - c = composite of the form (apply f i_1 ... i_n) with f in class of x
 * - d = composite of the from (apply g j_1 ... j_n) with g in class of z
 * - c and d are in distinct classes in the egraph
 * - i_1 == j_1 .... i_n == j_n hold in the egraph
 * Since there's path from x to z and the path is non-masking, we should
 * have c == d. We add the axiom that states this.
 */
static void fun_solver_add_axiom2(fun_solver_t *solver, thvar_t x, thvar_t z, composite_t *c, composite_t *d) {
  ivector_t *lemma;
  fun_vartable_t *vtbl;
  thvar_t y;
  int32_t i;
  literal_t l;

  vtbl = &solver->vtbl;

#if TRACE
  printf("\n--- Update conflict ---\n");
#if 0
  printf("Classes:\n");
  print_fsolver_classes(stdout, solver);
  printf("Disequalities:\n");
  print_fsolver_diseqs(stdout, solver);
  printf("Applications:\n");
  print_fsolver_apps(stdout, solver);
  printf("\n\n");
#endif

  printf("Source var: f!%"PRId32", ", x);
  print_eterm_def(stdout, solver->egraph, fun_solver_eterm_of_var(solver, x));
  printf("Target var: f!%"PRId32", ", z);
  print_eterm_def(stdout, solver->egraph, fun_solver_eterm_of_var(solver, z));
  printf("Source app: ");
  print_eterm_def(stdout, solver->egraph, c->id);
  printf("Target app: ");
  print_eterm_def(stdout, solver->egraph, d->id);
  printf("Path length: %"PRIu32"\n", path_length(solver, x, z));

#if 0
  printf("Path:\n");
  y = z;
  do {
    i = vtbl->pre[y];
    assert(i >= 0 && i != null_fun_pred);
    print_fsolver_edge(stdout, solver, i);
    printf("\n");
    y = previous_root(solver, y, i);
  } while (y != x);
#endif

  fflush(stdout);

#endif

  /*
   * Create the lemma
   */
  lemma = &solver->lemma_vector;
  assert(lemma->size == 0);
  // collect the path atoms + equal args atom
  collect_path_atoms(solver, x, z, c, d, lemma);
  collect_equal_arg_atoms(solver, c, d, lemma);

#if TRACE
  printf("\n--- Update lemma ---\n");
#endif

  if (lemma->size > 0) {
#if TRACE
    printf("path constraints:\n");
    if (lemma->size == 1) {
      print_egraph_atom_of_literal(stdout, solver->egraph, lemma->data[0]);
    } else {
      printf("(AND");
      for (i=0; i<lemma->size; i++) {
        printf(" ");
        print_egraph_atom_of_literal(stdout, solver->egraph, lemma->data[i]);
      }
      printf(")");
    }
    printf("\n");
#endif

    negate_vector(lemma);
  }

  // add the edge constraints
  y = z;
  do {
    i = vtbl->pre[y];
    assert(i >= 0 && i != null_fun_pred);
    l = apply_edge_equal_args(solver, c, get_edge(&solver->etbl, i));
    //    l = apply_edge_equal_args(solver, d, get_edge(&solver->etbl, i));
    if (l != false_literal) {
      ivector_push(lemma, l);
    }
    y = previous_root(solver, y, i);
  } while (y != x);


  // add the consequent: (c == d)
  l = equal_applies(solver, c, d);
  ivector_push(lemma, l);

#if TRACE
  if (lemma->size > 1) {
    printf("antecedents:\n");
    for (i=0; i<lemma->size - 1; i++) {
      print_literal(stdout, lemma->data[i]);
      printf(" := ");
      print_egraph_atom_of_literal(stdout, solver->egraph, lemma->data[i]);
      printf("\n");
    }
  }
  printf("consequent:\n");
  print_literal(stdout, l);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, solver->egraph, l);
  printf("\n\n");
#endif

  add_clause(solver->core, lemma->size, lemma->data);

#if TRACE
  printf("clause:\n  (OR");
  for (i=0; i<lemma->size; i++) {
    printf(" ");
    print_literal(stdout, lemma->data[i]);
  }
  printf(")\n\n");
  fflush(stdout);
#endif

  ivector_reset(lemma);

  solver->stats.num_update_axiom2 ++;
}


/*
 * Propagate c = (apply f i_1 ... i_n) to all root variables z reachable from
 * x via a non-masking path and check for conflict. A conflict is found if
 * there's d = (apply g j_1 ... j_n) such that
 *  1) g is in the class of a variable z, reachable from x via a non-masking path
 *  2) j_1 ... j_n are equal to i_1 ... i_n in the egraph.
 *
 * Input:
 * - x must be a root variable
 * - c = (apply f ...) where f belongs to the class of x
 *
 * Result:
 * - return true if there's a conflict, false otherwise
 * - if there's no conflict, c is added to vtbl->app[z] for all root variables z
 * - if there's a conflict, c may be added to vtbl->app[z] for some z's
 * - if a conflict is found, then an instance of the generalized update axiom 2
 *   is added to the core.
 */
static bool update_conflict_for_application(fun_solver_t *solver, thvar_t x, composite_t *c) {
  fun_queue_t *queue;
  egraph_t *egraph;
  fun_vartable_t *vtbl;
  composite_t *d;
  int32_t *edges;
  thvar_t y, z;
  uint32_t n, i;
  int32_t k;
  bool result;

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  assert(vtbl->root[x] == x);
  queue = &solver->queue;
  assert(queue->top == 0 && queue->ptr == 0);


  fun_queue_push(queue, x);
  // mark that x is the source
  vtbl->pre[x] = null_fun_pred;

  while (! empty_fun_queue(queue)) {
    z = fun_queue_pop(queue);
    assert(vtbl->root[z] == z);

    /*
     * Check for conflicts
     */
    d = egraph_find_modified_application(egraph, vtbl->eterm[z], c);
    if (z != x && d != NULL_COMPOSITE) {
      if (! egraph_equal_apps(egraph, c, d)) {
        // conflict: add an instance of the update axiom
        fun_solver_add_axiom2(solver, x, z, c, d);
        result = true;
        goto done;
      }
    } else {
      /*
       * No conflict and no matching composite in z's class
       * - add c to app[z]
       * - explore the neighbors of all nodes in the class of z
       */
      add_ptr_to_vector(vtbl->app + z, c); // We could do this only after checking for conflicts
      do {
        // edges incident to node z
        edges = vtbl->edges[z];
        if (edges != NULL) {
          n = iv_size(edges);
          for (i=0; i<n; i++) {
            k = edges[i];
            y = adjacent_root(solver, z, k);
            if (vtbl->pre[y] < 0 && !masking_edge(solver, k, c)) {
              // y not visited yet: add it to the queue
              fun_queue_push(queue, y);
              vtbl->pre[y] = k;
            }
          }
        }
        z = vtbl->next[z];
      } while (z != null_thvar);
    }
  }

  result = false;

 done:
  // reset pre[y] to null for all y in the queue
  n = queue->top;
  for (i=0; i<n; i++) {
    y = queue->data[i];
    assert(vtbl->pre[y] >= 0);
    vtbl->pre[y] = null_fun_edge;
  }
  reset_fun_queue(queue);

  return result;
}


/*
 * Get the root variable for f in c = (apply f ....)
 */
static thvar_t root_app_var(egraph_t *egraph, composite_t *c) {
  eterm_t f;

  assert(composite_kind(c) == COMPOSITE_APPLY);
  f = term_of_occ(c->child[0]);
  return egraph_class_thvar(egraph, egraph_term_class(egraph, f));
}


/*
 * Collect all applications and check for update conflicts
 * - the equivalence classes and roots must be set first
 * - return true if no conflict is found, false otherwise
 */
static bool update_conflicts(fun_solver_t *solver) {
  egraph_t *egraph;
  ppart_t *pp;
  void **v;
  composite_t *c;
  uint32_t i, j, n, m;
  thvar_t x;
  bool result;
  uint32_t num_updates;

  assert(solver->vtbl.nvars > 0);

  // build the classes of relevant composites in the egraph
  egraph = solver->egraph;
  egraph_build_arg_partition(egraph);

  // limit: one conflict per class
  result = false;
  num_updates = 0;

  // get the partition and process all composites that
  // are in a non-singleton class
  pp = egraph_app_partition(egraph);
  n = ptr_partition_nclasses(pp);
  for (i=0; i<n; i++) {
    v = pp->classes[i];
    m = ppv_size(v);
    assert(m >= 2);
    for (j=0; j<m; j++) {
      c = v[j];
      x = root_app_var(egraph, c);
      if (update_conflict_for_application(solver, x, c)) {
        result = true;
        num_updates ++;
        // exit if max_update_conflicts is reached
        // move to the next class otherwise
        if (num_updates >= solver->max_update_conflicts) goto done;
        break;
      }
    }
  }


#if 0
  // EXPERIMENT
  pp = egraph_app_partition(egraph);
  n = egraph->terms.nterms;
  for (i=0; i<n; i++) {
    c = egraph_term_body(egraph, i);
    if (composite_body(c) &&
        composite_kind(c) == COMPOSITE_APPLY &&
        congruence_table_is_root(&egraph->ctable, c, egraph->terms.label) &&
        ptr_partition_get_index(pp, c) >= 0) {
      x = root_app_var(egraph, c);
      if (update_conflict_for_application(solver, x, c)) {
        result = true;
        num_updates ++;
        // exit if max_update_conflicts is reached
        if (num_updates >= solver->max_update_conflicts) goto done;
      }
    }
  }
#endif


 done:
  if (num_updates > 0) {
    if (num_updates == 1) {
      trace_printf(solver->core->trace, 5, "(array solver: 1 update lemma)\n");
    } else {
      trace_printf(solver->core->trace, 5, "(array solver: %"PRIu32" update lemmas)\n", num_updates);
    }
#if TRACE
    printf("---> ARRAY SOLVER: update axioms in %"PRIu32" classes out of %"PRIu32"\n", num_updates, n);
#endif
  }

  // cleanup
  egraph_reset_app_partition(egraph);

  return result;
}









/*****************
 *  FULL SOLVER  *
 ****************/

/*
 * Initialization
 * - core = attached smt_core
 * - gates = gate manager for the core
 * - egraph = attached egraph
 * - ttbl = attached type table
 */
void init_fun_solver(fun_solver_t *solver, smt_core_t *core,
                     gate_manager_t *gates, egraph_t *egraph, type_table_t *ttbl) {

  solver->core = core;
  solver->gate_manager = gates;
  solver->egraph = egraph;
  solver->types = ttbl;

  solver->base_level = 0;
  solver->decision_level = 0;

  init_fun_solver_statistics(&solver->stats);

  solver->max_update_conflicts = DEFAULT_MAX_UPDATE_CONFLICTS;
  solver->max_extensionality = DEFAULT_MAX_EXTENSIONALITY;

  init_fun_vartable(&solver->vtbl);
  init_edge_table(&solver->etbl);
  init_fun_queue(&solver->queue);
  init_diseq_stack(&solver->dstack);
  init_fun_trail_stack(&solver->trail_stack);

  init_ivector(&solver->aux_vector, 10);
  init_ivector(&solver->lemma_vector, 10);
  init_pvector(&solver->app_vector, 10);

  solver->apps_ready = false;
  solver->bases_ready = false;
  solver->reconciled = false;

  solver->num_bases = 0;
  solver->base_value = NULL;

  solver->value = NULL;
  solver->base_map = NULL;
  solver->value_size = 0;
  solver->base_map_size = 0;
  solver->fresh_hmap = NULL;
}


/*
 * Delete the solver
 */
void delete_fun_solver(fun_solver_t *solver) {
  delete_fun_vartable(&solver->vtbl);
  delete_edge_table(&solver->etbl);
  delete_fun_queue(&solver->queue);
  delete_diseq_stack(&solver->dstack);
  delete_fun_trail_stack(&solver->trail_stack);

  delete_ivector(&solver->aux_vector);
  delete_ivector(&solver->lemma_vector);
  delete_pvector(&solver->app_vector);

  if (solver->value != NULL) {
    fun_solver_delete_values(solver);
    assert(solver->value == NULL);
  }

  if (solver->base_value != NULL) {
    safe_free(solver->base_value);
    solver->base_value = NULL;
  }

  if (solver->base_map != NULL) {
    fun_solver_delete_base_maps(solver);
    assert(solver->base_map == NULL);
  }

  fun_solver_delete_fresh_hmap(solver);
}


/*
 * Reset
 */
void fun_solver_reset(fun_solver_t *solver) {
  solver->base_level = 0;
  solver->decision_level = 0;
  reset_fun_solver_statistics(&solver->stats);
  reset_fun_vartable(&solver->vtbl);
  reset_edge_table(&solver->etbl);
  reset_fun_queue(&solver->queue);
  reset_diseq_stack(&solver->dstack);
  reset_fun_trail_stack(&solver->trail_stack);

  ivector_reset(&solver->aux_vector);
  ivector_reset(&solver->lemma_vector);
  pvector_reset(&solver->app_vector);

  solver->apps_ready = false;
  solver->bases_ready = false;
  solver->reconciled = false;

  solver->num_bases = 0;
  if (solver->value != NULL) {
    fun_solver_delete_values(solver);
    assert(solver->value == NULL);
  }

  if (solver->base_map != NULL) {
    fun_solver_delete_base_maps(solver);
    assert(solver->base_map == NULL);
  }

  if (solver->base_value != NULL) {
    safe_free(solver->base_value);
    solver->base_value = NULL;
  }

  fun_solver_delete_fresh_hmap(solver);
}



/*
 * Increase the decision level
 */
void fun_solver_increase_decision_level(fun_solver_t *solver) {
  uint32_t k;

  k = solver->decision_level + 1;
  solver->decision_level = k;
  diseq_stack_increase_dlevel(&solver->dstack, k);
}


/*
 * Backtrack to back_level:
 * - remove disequalities asserted at levels back_level + 1, ...
 */
void fun_solver_backtrack(fun_solver_t *solver, uint32_t back_level) {
  assert(solver->base_level <= back_level && back_level < solver->decision_level);
  diseq_stack_backtrack(&solver->dstack, back_level);
  solver->decision_level = back_level;
}


/*
 * Push:
 * - save number of variables & edges
 * - increase base level & decision level
 */
void fun_solver_push(fun_solver_t *solver) {
  assert(solver->base_level == solver->decision_level);

  fun_trail_stack_save(&solver->trail_stack, solver->vtbl.nvars, solver->etbl.nedges);
  solver->base_level ++;
  fun_solver_increase_decision_level(solver);
  assert(solver->base_level == solver->decision_level);
}


/*
 * Pop:
 * - remove variables & edges added at the current base level
 * - decrement base level and decision level
 */
void fun_solver_pop(fun_solver_t *solver) {
  fun_trail_t *top;
  fun_vartable_t *vtbl;
  fun_edgetable_t *etbl;
  fun_edge_t *e;
  uint32_t i, n;
  thvar_t x;

  assert(solver->base_level > 0 && solver->base_level == solver->decision_level);
  top = fun_trail_stack_top(&solver->trail_stack);
  vtbl = &solver->vtbl;
  etbl = &solver->etbl;

  // remove edges from vtbl->edges
  i = etbl->nedges;
  n = top->nvars;
  while (i > top->nedges) {
    i --;
    e = etbl->data[i];
    x = e->source;
    if (x < n) {
      remove_index_from_vector(vtbl->edges[x], i);
    }
    x = e->target;
    if (x < n) {
      remove_index_from_vector(vtbl->edges[x], i);
    }
  }

  // remove edges and variables
  shrink_fun_vartable(&solver->vtbl, top->nvars);
  shrink_edge_table(&solver->etbl, top->nedges);

  solver->base_level --;
  fun_trail_stack_pop(&solver->trail_stack);

  fun_solver_backtrack(solver, solver->base_level);
}


/*
 * Prepare for internalization: do nothing
 */
void fun_solver_start_internalization(fun_solver_t *solver) {
}

/*
 * Start search
 */
void fun_solver_start_search(fun_solver_t *solver) {
  solver->stats.num_init_vars = solver->vtbl.nvars;
  solver->stats.num_init_edges = solver->etbl.nedges;
  solver->reconciled = false;

#if TRACE
  printf("\n=== START SEARCH ===\n");
  print_fsolver_vars(stdout, solver);
  printf("\n");
  print_fsolver_edges(stdout, solver);
  printf("\n\n");
#endif
}


/*
 * Propagate: do nothing
 * - all the work is done in final_check
 */
bool fun_solver_propagate(fun_solver_t *solver) {
  return true;
}



/*
 * FINAL CHECK: deal only with update conflicts.
 * Extensionality is handled in reconcile_model.
 *
 * Search for update conflicts. If a conflict if found,
 * add an instance of Axiom 2 to get rid of it
 * - return FCHECK_CONTINUE if an instance is generated
 * - return FCHCEK_SAT otherwise (i.e., no update conflict was found)
 */
fcheck_code_t fun_solver_final_check(fun_solver_t *solver) {
  fcheck_code_t result;

#if TRACE
  printf("\n**** FUNSOLVER: FINAL CHECK ***\n\n");
#endif

#if TRACE
  print_egraph_terms(stdout, solver->egraph);
  printf("\n\n");
  print_egraph_root_classes_details(stdout, solver->egraph);
#endif

  if (solver->etbl.nedges == 0) {
    // nothing to do
    return FCHECK_SAT;
  }

  // check for update conflicts
  result = FCHECK_SAT;
  fun_solver_build_classes(solver);
  if (update_conflicts(solver)) {
#if TRACE
    printf("---> FUN Solver: update conflict\n");
#endif
    result = FCHECK_CONTINUE;
  }

  // cleanup and return
  fun_solver_cleanup(solver);
  return result;
}


/*
 * Clear: nothing to do
 */
void fun_solver_clear(fun_solver_t *solver) {
}



/***********************
 *   INTERNALIZATION   *
 **********************/

/*
 * Create a fresh array variable x of type tau
 * - type[x] and arity[x] are set
 * - fdom[x] = 1 if tau has finite domain or 0 otherwise
 * - eterm[x] = null_eterm
 * - edges[x] = NULL
 *
 * - pre[x] = null_edge
 * - app[x] = NULL
 * - base[x] = -1;
 * - mark[x] = 0
 * - root[x] and next[x] are not initialized
 */
thvar_t fun_solver_create_var(fun_solver_t *solver, type_t tau) {
  fun_vartable_t *vtbl;
  thvar_t x;

  assert(good_type(solver->types, tau) && type_kind(solver->types, tau) == FUNCTION_TYPE);
  vtbl = &solver->vtbl;
  x = fun_vartable_alloc(vtbl);
  vtbl->type[x] = tau;
  vtbl->arity[x] = function_type_arity(solver->types, tau);
  assign_bit(vtbl->fdom, x, type_has_finite_domain(solver->types, tau));
  vtbl->eterm[x] = null_eterm;
  vtbl->edges[x] = NULL;

  vtbl->pre[x] = null_fun_edge;
  vtbl->base[x] = -1;
  vtbl->app[x] = NULL;
  clr_bit(vtbl->mark, x);

  return x;
}



/*
 * Create a new edge
 * - x = source var
 * - y = target var
 * - u = update composite
 */
static void fun_solver_add_edge(fun_solver_t *solver, thvar_t x, thvar_t y, composite_t *u) {
  fun_edgetable_t *etbl;
  fun_vartable_t *vtbl;
  fun_edge_t *e;
  int32_t i;

  etbl = &solver->etbl;
  vtbl = &solver->vtbl;

  e = make_edge(x, y, u);
  i = edge_table_alloc(etbl);
  etbl->data[i] = e;
  add_index_to_vector(vtbl->edges + x, i);
  add_index_to_vector(vtbl->edges + y, i);
}


/*
 * Attach eterm t to variable x
 * - if t is an update term, add an edge and instantiate axiom1
 */
void fun_solver_attach_eterm(fun_solver_t *solver, thvar_t x, eterm_t t) {
  egraph_t *egraph;
  composite_t *cmp;
  occ_t f;
  thvar_t y;

  assert(0 <= x && x < solver->vtbl.nvars && solver->vtbl.eterm[x] == null_eterm);

  solver->vtbl.eterm[x] = t;

  egraph = solver->egraph;
  cmp = egraph_term_body(egraph, t);
  if (composite_body(cmp) && composite_kind(cmp) == COMPOSITE_UPDATE) {
    // t is (update f i_1 ... i_n v)
    f = composite_child(cmp, 0);
    y = egraph_term_base_thvar(egraph, term_of_occ(f));
    assert(0 <= y && y < solver->vtbl.nvars && solver->vtbl.eterm[y] == term_of_occ(f));
    // create the edge y ---> x
    fun_solver_add_edge(solver, y, x, cmp);

    // add the axiom ((update f i_1 ... i_n v) i_1 ... i_n) = v
    fun_solver_update_axiom1(solver, t, cmp, solver->vtbl.type[x]);

    // NOTE: adding the axiom may create a new array variable and recursively
    // call attach_eterm. This should be safe as the new term can't be an update.
  }
}


/*
 * Return the eterm attached to theory variable x
 * TODO: clean this up. No need to duplicate this?
 */
eterm_t fun_solver_get_eterm_of_var(fun_solver_t *solver, thvar_t x) {
  return fun_solver_eterm_of_var(solver, x);
}





/***********************
 *   EGRAPH INTERFACE  *
 **********************/

/*
 * Assert that x1 and x2 are equal: do nothing
 */
void fun_solver_assert_var_eq(fun_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id) {
  assert(0 <= x1 && x1 < solver->vtbl.nvars && 0 <= x2 && x2 < solver->vtbl.nvars);
}


/*
 * Assert that x1 and x2 are distinct: push the disequality onto the diseq stack
 */
void fun_solver_assert_var_diseq(fun_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint) {
  assert(0 <= x1 && x1 < solver->vtbl.nvars && 0 <= x2 && x2 < solver->vtbl.nvars);
  diseq_stack_push(&solver->dstack, x1, x2);
}


/*
 * Assert that all variables a[0] ... a[n-1] are pairwise distinct
 * - they are attached to egraph terms t[0] ... t[n-1]
 * - the function is called when (distinct t[0] ... t[n-1]) is asserted in the egraph
 */
void fun_solver_assert_var_distinct(fun_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
  thvar_t x, y;
  uint32_t i, j;

  for (i=0; i<n; i++) {
    x = a[i];
    assert(0 <= x && x < solver->vtbl.nvars);
    for (j=i+1; j<n; j++) {
      y = a[j];
      diseq_stack_push(&solver->dstack, x, y);
    }
  }
}



/*
 * Check whether x1 and x2 are distinct at the base level
 * - do nothing for now. Always return false.
 */
bool fun_solver_check_disequality(fun_solver_t *solver, thvar_t x1, thvar_t x2) {
  assert(0 <= x1 && x1 < solver->vtbl.nvars && 0 <= x2 && x2 < solver->vtbl.nvars);
  return false;
}


/*
 * Check whether x is a constant
 */
bool fun_solver_var_is_constant(fun_solver_t *solver, thvar_t x) {
  return false;
}


/*
 * Select whether to branch on (x1 == x2) or (x1 != x2)
 * - always return (not l): branch on (x1 != x2)
 */
literal_t fun_solver_select_eq_polarity(fun_solver_t *solver, thvar_t x1, thvar_t x2, literal_t l) {
  return not(l);
}


/*
 * INTERFACE EQUALITIES
 */

/*
 * Propagate c = (apply f i_1 ... i_n) to all root variables z reachable
 * from x = root variable for f via a non-masking path.
 */
static void propagate_application(fun_solver_t *solver, composite_t *c, thvar_t x) {
  fun_queue_t *queue;
  fun_vartable_t *vtbl;
#ifndef NDEBUG
  egraph_t *egraph;
  composite_t *d;
#endif
  int32_t *edges;
  thvar_t y, z;
  uint32_t n, i;
  int32_t k;

  vtbl = &solver->vtbl;
  queue = &solver->queue;
  assert(queue->top == 0 && queue->ptr == 0);

  assert(vtbl->root[x] == x);
  fun_queue_push(queue, x);
  set_bit(vtbl->mark, x);

  while (! empty_fun_queue(queue)) {
    z = fun_queue_pop(queue);
    assert(vtbl->root[z] == z && tst_bit(vtbl->mark, z));

#ifndef NDEBUG
    // there should be no update conflict when this function is called
    egraph = solver->egraph;
    d = egraph_find_modified_application(egraph, vtbl->eterm[z], c);
    assert(d == NULL_COMPOSITE || egraph_equal_apps(egraph, c, d));
#endif

    /*
     * Add c to z's app vector
     * - explore the neighbors of all nodes in z's class
     */
    add_ptr_to_vector(vtbl->app + z, c);
    do {
      edges = vtbl->edges[z]; // edges incident to z
      if (edges != NULL) {
	n = iv_size(edges);
	for (i=0; i<n; i++) {
	  k = edges[i];
	  y = adjacent_root(solver, z, k);
	  if (!tst_bit(vtbl->mark, y) && !masking_edge(solver, k, c)) {
	    // y not visited yet and reached via a non-masking path
	    fun_queue_push(queue, y);
	    set_bit(vtbl->mark, y);
	  }
	}
      }
      z = vtbl->next[z]; // next node in the class
    } while (z != null_thvar);
  }

  // clear the marks of all nodes in the queue
  n = queue->top;
  for (i=0; i<n; i++) {
    y = queue->data[i];
    assert(tst_bit(vtbl->mark, y));
    clr_bit(vtbl->mark, y);
  }

  reset_fun_queue(queue);
}


/*
 * Add all applications in vector v
 * - x = corresponding root variable.
 * - all composites in v must be of the form (apply f ....) where f
 *   is in the same egraph class as x's eterm.
 */
static void build_apps_from_var(fun_solver_t *solver, thvar_t x, pvector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    propagate_application(solver, v->data[i], x);
  }
}


/*
 * Build the full app vector for each root variable
 */
static void fun_solver_build_apps(fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  pvector_t v;
  uint32_t i, n;
  thvar_t x;

  assert(solver->vtbl.nvars > 0);

  init_pvector(&v, 50);
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    x = vtbl->root[i];
    if (x == i) {
      /*
       * x is a root
       * get all composites whose function symbol is in x's class
       * propagate them
       */
      egraph_collect_applications(solver->egraph, vtbl->eterm[x], &v);
      build_apps_from_var(solver, x, &v);
      pvector_reset(&v);
    }
  }

  delete_pvector(&v);
}



/*
 * Assign a base_value to each connected component i
 * - we want to ensure
 *   base_value[i] != base_value[j] ==> it's possible to assign
 *   different default values to components i and j
 * - base_value[i] < 0 means that we can assign a fresh object (not in the egraph)
 *   to component i.
 *
 * We use the following rules:
 * - if component i has an infinite range type, then base_value[i] = -(i+1)
 * - if component i has finite range type, then we count the number of
 *   egraph class with the same type and use them as base values
 * - if that's smaller than the cardinality of the range type,
 *   then we assign negative base_values to as many components as possible.
 */
#define UNKNOWN_BASE_VALUE  INT32_MAX
#define NULL_BASE_VALUE     INT32_MIN

/*
 * Allocate and initialize the base_value array
 */
static void fun_solver_init_base_value(fun_solver_t *solver) {
  uint32_t i, n;
  int32_t *bv;

  assert(solver->bases_ready && solver->base_value == NULL);
  n = solver->num_bases;
  bv = (int32_t *) safe_malloc(n * sizeof(int32_t));
  for (i=0; i<n; i++) {
    bv[i] = NULL_BASE_VALUE;
  }
  solver->base_value = bv;
}



/*
 * Comparison function for sorting the root variables
 * We want to group all variables of same type together.
 */
static bool root_lt(fun_vartable_t *vtbl, thvar_t x, thvar_t y) {
  assert(0 <= x && x < vtbl->nvars && vtbl->root[x] == x &&
	 0 <= y && y < vtbl->nvars && vtbl->root[y] == y);

  return vtbl->type[x] < vtbl->type[y];
}


/*
 * Assign a base value to all connected components
 */
static void fun_solver_assign_base_values(fun_solver_t *solver) {
  ivector_t buffer;
  fun_vartable_t *vtbl;
  type_table_t *types;
  ivector_t *v;
  type_t tau, sigma;
  uint32_t i, j, h, n, m, p;
  thvar_t x;
  int32_t k;

  assert(solver->base_value != NULL);

  vtbl = &solver->vtbl;
  v = &solver->aux_vector;
  assert(v->size == 0);

  /*
   * buffer is used only if we have functions
   * with finite ranges. init_ivector with size 0
   * does not allocate anything.
   */
  init_ivector(&buffer, 0);

  /*
   * Collect a root variable from each connected
   * component in vector v.
   */
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      k = vtbl->base[i];
      if (solver->base_value[k] == NULL_BASE_VALUE) {
        ivector_push(v, i);
        solver->base_value[k] = UNKNOWN_BASE_VALUE; // mark
      }
    }
  }

  /*
   * Sort v: group the variables with the same type together
   */
  assert(v->size == solver->num_bases);
  int_array_sort2(v->data, v->size, vtbl, (int_cmp_fun_t) root_lt);

  /*
   * Assign a base value to each connected component
   */
  types = solver->types;
  n = v->size;
  m = 0;
  while (m < n) {
    x = v->data[m];
    assert(vtbl->root[x] == x);
    tau = fun_var_type(vtbl, x);

    for (i=m+1; i<n; i++) {
      x = v->data[i];
      assert(vtbl->root[x] == x);
      if (fun_var_type(vtbl, x) != tau) break;
    }

    assert(m < i && i <= n);

    /*
     * v->data[m ... i-1] = components of type tau (one variable per component)
     */
    sigma = function_type_range(types, tau);
    if (is_finite_type(types, sigma)) {
      /*
       * Finite range: we need i - m base values of type sigma
       */
      h = type_card(solver->types, sigma);
      p = i - m;
      if (p > h) p = h;

#if TRACE
      printf("---> connected components of type tau: %"PRId32"\n", tau);
      printf("--->   range type: sigma = %"PRId32" of card = %"PRIu32"\n", sigma, h);
      printf("--->   num classes = %"PRIu32"\n", i - m);
      fflush(stdout);
#endif

      /*
       * Make the buffer large enough
       */
      resize_ivector(&buffer, p);
      assert(buffer.capacity >= p);

      /*
       * Fill in the buffer with values from the egraph (as many as we can)
       * then with fresh values. Since p <= card sigma, this is sound.
       */
      h = egraph_get_labels_for_type(solver->egraph, sigma, buffer.data, p);
      assert(h <= p);
      k = -1; // negative index for fresh values if needed
      while (h < p) {
	buffer.data[h] = k;
	k --;
	h ++;
      }

      /*
       * Assign base_values taken form buffer.data[0 .. p-1]
       */
      h = 0;
      for (j=m; j<i; j++) {
	x = v->data[j];
	k = vtbl->base[x];
	assert(solver->base_value[k] == UNKNOWN_BASE_VALUE);
	solver->base_value[k] = buffer.data[h];
#if TRACE
	printf("--->   base_value[%"PRId32"] = %"PRId32"\n", k, solver->base_value[k]);
#endif
	h ++;
	if (h >= p) h = 0;
      }

    } else {
      /*
       * Infinite range: all base values are fresh
       */
      for (j=m; j<i; j++) {
        x = v->data[j];
        k = vtbl->base[x];
        assert(solver->base_value[k] == UNKNOWN_BASE_VALUE);
        solver->base_value[k] = - (k+1); // encoding for 'fresh value'
      }
    }

    m = i;
  }

  // cleanup
  delete_ivector(&buffer);
  ivector_reset(v);

}



/*
 * Comparison between two functions defined by (v, dv) and (w, dw) respectively.
 * The functions are both of type [tau_1 ... tau_k --> sigma]
 * where tau_1, ..., tau_k and sigma are finite types.
 *
 * - v: sorted array of composites or NULL
 * - dv: default value outside of v's domain
 * - w: sorted array of composites or NULL
 * - dw: default value outside of w's domain
 * - card = approximate cardinality of the domain (tau_1 \times ... \times tau_k)
 *    (cf types.h: card = UINT32_MAX if the real card is >= UINT32_MAX)
 *
 * Assumptions:
 * - every term in v and w is a composite of type [tau_1 ... tau_k --> sigma]
 * - dv and dw are either labels of two terms in the egraph of type sigma
 *   or they are negative integers denoting fresh values of type sigma
 */
static bool equal_mappings(fun_solver_t *solver, void **v, void **w, int32_t dv, int32_t dw, uint32_t card) {
  egraph_t *egraph;
  composite_t *c, *d;
  uint32_t n, m, i, j, p;
  int32_t cmp;

  // n = size of v
  // m = size of w
  n = 0;
  if (v != NULL) {
    n = pv_size(v);
  }
  m = 0;
  if (w != NULL) {
    m = pv_size(w);
  }

  assert(n <= card && m <= card && dv != UNKNOWN_BASE_VALUE && dw != UNKNOWN_BASE_VALUE);

  egraph = solver->egraph;

  i = 0;
  j = 0;
  p = 0; // number of terms examined
  while (i < n && j < m) {
    c = v[i];
    d = w[j];
    if (c == d) {
      i ++;
      j ++;
      p ++;
    } else {
      cmp = app_cmp(egraph, c, d);
      if (cmp < 0) {
        // c < d in lex ordering
        if (egraph_term_label(egraph, c->id) != dw) {
          return false;
        }
        i ++;
      } else if (cmp > 0) {
        // c > d in lex ordering
        if (egraph_term_label(egraph, d->id) != dv) {
          return false;
        }
        j ++;
      } else {
        // c == d in lex ordering
        if (! egraph_equal_terms(egraph, c->id, d->id)) {
          return false;
        }
        i ++;
        j ++;
      }
      p ++;
    }
  }

  while (i < n) {
    assert(j == m);
    c = v[i];
    if (egraph_term_label(egraph, c->id) != dw) {
      return false;
    }
    i ++;
    p ++;
  }

  while (j < m) {
    assert(i == n);
    d = w[j];
    if (egraph_term_label(egraph, d->id) != dv) {
      return false;
    }
    j ++;
    p ++;
  }

  assert(p <= card);

  return p == card || dv == dw;
}



/*
 * Check whether x1 and x2 are equal in the model.
 */
static bool fun_solver_var_equal_in_model(fun_solver_t *solver, thvar_t x1, thvar_t x2) {
  fun_vartable_t *vtbl;
  int32_t b1, b2;
  int32_t v1, v2;
  uint32_t card;

  vtbl = &solver->vtbl;
  x1 = vtbl->root[x1];
  x2 = vtbl->root[x2];
  assert(vtbl->root[x1] == x1 && vtbl->root[x2] == x2);

  if (compatible_types(solver->types, fun_var_type(vtbl, x1), fun_var_type(vtbl, x2))) {
    b1 = vtbl->base[x1];
    b2 = vtbl->base[x2];

    if (b1 != b2 && fun_var_has_infinite_domain(vtbl, x1)) {
      // x1 and x2 are not connected and have infinite domain
      // they will be made disequal in the final model
      assert(fun_var_has_infinite_domain(vtbl, x2));
      return false;
    }

    v1 = solver->base_value[b1];
    v2 = solver->base_value[b2];
    card = card_of_domain_type(solver->types, fun_var_type(vtbl, x1));

    return equal_mappings(solver, vtbl->app[x1], vtbl->app[x2], v1, v2, card);

  } else {
    // x1 and x2 have incompatible types so they're distinct
    return false;
  }
}


/*
 * Hash function for separating distinct variables.
 *
 * For every variable x, we know the following
 * - its domain (sigma_1 x ... x sigma_n)
 * - its connected component index k = base[x]
 * - the default value for component k = default[x]
 * - the application map = array of composites = app[x]
 *
 * default[x] is either a label in the egraph or a fresh object,
 * distinct from any egraph term. default[x] is relevant for x if
 * app_size[x] < cardinality domain[x].
 *
 * We also use a sample_value(x): an index that occurs in the array x
 * and is such that x == y implies sample_value(x) = sample_value(y).
 *
 * To compute sample_value(x):
 * - if x has finite domain and default[x] is a fresh object and it's
 *   relevant for x, sample_vlaue(x) = default[x]
 * - otherwise sample_value(x) = max of default[x] and egraph labels
 *   of all elements that occur in app[x]
 *
 * Properties we use:
 * 1) if x == y then domain[x] = domain[y] (call it D)
 * 2) if x == y and D is infinite then base[x] = base[y]
 * 3) if x == y then sample_value(x) = sample_value(y)
 *
 * We associate the following signature with x:
 *   sgn(x) = (n, sigma_1, b, s)
 * where
 *   n = arity
 *   sigma_1 = first domain component
 *   b = base[x] if domain[x] is infinite
 *             -1  if domain[x] is finite
 *   s = sample_value(x)
 *
 * Then we have x == y implies sgn(x) = sgn(y).
 */
static int32_t fun_solver_sample_value_for_var(fun_solver_t *solver, thvar_t x) {
  fun_vartable_t *vtbl;
  composite_t *c;
  void **v;
  elabel_t label;
  uint32_t i, app_size;
  int32_t b, d;

  vtbl = &solver->vtbl;
  assert(0 <= x && x < vtbl->nvars && vtbl->root[x] == x);

  app_size = 0;
  v = vtbl->app[x];
  b = vtbl->base[x];
  d = solver->base_value[b];
  if (v != NULL) app_size = pv_size(v);

  if (app_size == 0) return d;

  if (fun_var_has_finite_domain(vtbl, x) && d < 0 &&
      app_size < card_of_domain_type(solver->types, fun_var_type(vtbl, x))) {
    return d;
  }

  d = -1;
  for (i=0; i<app_size; i++) {
    c = v[i];
    label = egraph_term_label(solver->egraph, c->id);
    if (label > d) d = label;
  }

  assert(d >= 0);
  return d;
}

static uint32_t fun_solver_model_hash(fun_solver_t *solver, thvar_t x) {
  fun_vartable_t *vtbl;
  int32_t sgn[4];

  vtbl = &solver->vtbl;
  assert(0 <= x && x < vtbl->nvars && vtbl->root[x] == x);

  sgn[0] = vtbl->arity[x];
  sgn[1] = function_type_domain(solver->types, vtbl->type[x], 0); // sigma_1
  sgn[2] = fun_var_has_infinite_domain(vtbl, x) ? vtbl->base[x] : -1;
  sgn[3] = fun_solver_sample_value_for_var(solver, x);

  return jenkins_hash_intarray(sgn, 4);
}



/*
 * Release model: reset apps and base labels
 */
static void fun_solver_release_model(fun_solver_t *solver) {
  fun_solver_cleanup(solver);
  safe_free(solver->base_value);
  solver->base_value = NULL;
}


/*
 * Stratification
 * - build stratification structure
 */
static void fun_solver_stratify(stratification_t *levels, fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  diseq_stack_t *dstack;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      stratify_incr_var_count(levels, fun_var_type(vtbl, i));
    }
  }
  dstack = &solver->dstack;
  n = dstack->top;
  for (i=0; i<n; i++) {
    x = dstack->data[i].left;
    stratify_incr_diseq_count(levels, fun_var_type(vtbl, x));
  }
  stratify_make_arrays(levels);

  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      stratify_add_var(levels, i, fun_var_type(vtbl, i));
    }
  }
  n = dstack->top;
  for (i=0; i<n; i++) {
    x = dstack->data[i].left;
    stratify_add_diseq(levels, i, fun_var_type(vtbl, x));
  }
}


/*
 * Check for extensionality axioms for explicit disequalities at level k
 * in the stratification.
 * - max_eq = bound on the number of aximos to generate
 * - return the total number of axioms produced
 */
static uint32_t gen_extensionality_for_diseqs(fun_solver_t *solver, stratification_t *levels,
					      uint32_t k, uint32_t max_eqs) {
  diseq_stack_t *dstack;
  uint32_t i, d, n, start_idx;
  uint32_t neqs;
  thvar_t x, y;

  n = num_diseqs_in_stratum(levels, k);
  if (n == 0) return 0; // nothing to do

  dstack = &solver->dstack;

  neqs = 0;

  start_idx = first_diseq_in_stratum(levels, k);
  for (i=start_idx; i<start_idx+n; i++) {
    d = levels->diseqs[i];
    assert(d < dstack->top);
    x = dstack->data[d].left;
    y = dstack->data[d].right;
    if (fun_solver_var_equal_in_model(solver, x, y)) {
      fun_solver_extensionality_axiom(solver, x, y);
      neqs ++;
      if (neqs == max_eqs) break;
    }
  }

  return neqs;
}


/*
 * Check for extensionality axioms caused by conflicts between
 * Egraph classes and solver model
 * - we create an axiom if (t == u) for the solver (same values in the model)
 *   but t and u are in different classes in the egraph
 * - k = stratification levels (only variables at this level are considered)
 * - hclass = hash table for checking  t == u
 * - max_eqs = bound on the number of axioms to generate
 * - return the total number of axioms produced
 */
static uint32_t gen_extensionality_for_vars(fun_solver_t *solver, stratification_t *levels,
					    int_hclass_t *hclass, uint32_t k, uint32_t max_eqs) {
  uint32_t i, n, start_idx;
  uint32_t neqs;
  thvar_t x, y;

  n = num_vars_in_stratum(levels, k);
  if (n == 0) return 0; // nothing to do

  neqs = 0;
  start_idx = first_var_in_stratum(levels, k);

  for (i=start_idx; i<start_idx+n; i++) {
    x = levels->vars[i];
    assert(0 <= x && x < solver->vtbl.nvars);
    assert(solver->vtbl.root[x] == x);

    y = int_hclass_get_rep(hclass, x);
    if (y != x) {
      fun_solver_extensionality_axiom(solver, y, x);
      neqs ++;
      if (neqs == max_eqs) break;
    }
  }

  return neqs;
}


/*
 * Build a model that attempt to minimize conflicts with the egraph.
 * Add instance of the extensionality axiom for the conflicts that remain.
 * - max_eq is ignored (we use max_extensionality instead)
 * - return the number of extensionality instances created
 * - set the reconciled_flag to true if no extensionality instances were
 *   created (and to false otherwise).
 *
 * NOTE: this is not called if the egraph has no higher-order terms (i.e., function
 * terms do not occur as children of other terms, except as first term of
 * (update f x1 ,,, x_n u). In this case, the model construction does not
 * have to ensure that function variables that are in distinct classes have
 * distinct values.
 */
uint32_t fun_solver_reconcile_model(fun_solver_t *solver, uint32_t max_eq) {
  stratification_t levels;
  int_hclass_t hclass;
  uint32_t k, n, neqs, nv0, max_eqs;

  assert(!solver->bases_ready && !solver->apps_ready);

#if TRACE
  printf("\n--- FUN SOLVER: Reconcile model ---\n");
  print_egraph_terms(stdout, solver->egraph);
  printf("\n\n");
  fflush(stdout);
#endif

  fun_solver_build_classes(solver);
  fun_solver_build_components(solver);
  fun_solver_build_apps(solver);
  fun_solver_normalize_apps(solver);
  fun_solver_init_base_value(solver);
  fun_solver_assign_base_values(solver);

  init_stratification(&levels, solver->types);
  fun_solver_stratify(&levels, solver);

#if TRACE
  printf("Egraph:\n");
  print_egraph_terms(stdout, solver->egraph);
  printf("\nClasses:\n");
  print_fsolver_classes(stdout, solver);
  printf("\nMaps:\n");
  print_fsolver_maps(stdout, solver);
  printf("\nBase values\n");
  print_fsolver_base_values(stdout, solver);;
  printf("\nDisequalities:\n");
  print_fsolver_diseqs(stdout, solver);
  printf("\n");
  printf("\nStratification:\n");
  print_fsolver_stratification(stdout, &levels, solver);
  printf("\n");
#endif


  // hclass to check for more conflicts egraph classes and the solver model.
  init_int_hclass(&hclass, 0, solver, (iclass_hash_fun_t) fun_solver_model_hash,
                  (iclass_match_fun_t) fun_solver_var_equal_in_model);

  /*
   * We keep track of the current number of variables before
   * generating any extensionality axioms (extensionality axioms
   * may create new variables in this solver).
   *
   * If new variables are created, the current model is wrong.
   */
  nv0 = solver->vtbl.nvars;
  max_eqs = solver->max_extensionality;
  neqs = 0;

  assert(max_eqs > 0);

  // process each level (level 0 is always empty)
  n = strat_num_levels(&levels);
  for (k=1; k<n; k++) {
    // handle the explicit disequalities first
    neqs += gen_extensionality_for_diseqs(solver, &levels, k, max_eqs);
    assert(neqs <= max_eqs);
    if (neqs == max_eqs || nv0 < solver->vtbl.nvars) break;

    // then variables in this level
    neqs += gen_extensionality_for_vars(solver, &levels, &hclass, k, max_eqs - neqs);
    assert(neqs <= max_eqs);
    if (neqs == max_eqs || nv0 < solver->vtbl.nvars) break;
  }

  delete_int_hclass(&hclass);
  delete_stratification(&levels);
  fun_solver_release_model(solver);
  solver->reconciled = (neqs == 0);

  return neqs;
}



/*
 * NEW MODEL RECONCILIATION API
 */
static void fun_solver_prepare_model(fun_solver_t *solver) {
  solver->reconciled = true;

  fun_solver_build_classes(solver);
  fun_solver_build_components(solver);
  fun_solver_build_apps(solver);
  fun_solver_normalize_apps(solver);
  fun_solver_init_base_value(solver);
  fun_solver_assign_base_values(solver);
}


// release model is defined above

//  equal_in_model is defined above too

/*
 * Generate the lemma l => x1 != x2
 * - we instantiate the extensionality axiom here:
 *   (i.e., we generate the clause (not l) or (x1 t) /= (x2 t) for a
 *    fresh Skolem constant t).
 */
static void fun_solver_gen_interface_lemma(fun_solver_t *solver, literal_t l, thvar_t x1, thvar_t x2, bool equiv) {
  fun_vartable_t *vtbl;
  egraph_t *egraph;
  ivector_t *v;
  eterm_t t, u;
  literal_t eq;

  solver->reconciled = false;

  assert(0 <= x1 && x1 < solver->vtbl.nvars && 0 <= x2 && x2 < solver->vtbl.nvars && x1 != x2);

  egraph = solver->egraph;
  vtbl = &solver->vtbl;
  v = &solver->aux_vector;
  assert(v->size == 0);

  fun_solver_skolem_domain(solver, vtbl->type[x1], v);
  t = egraph_make_apply(egraph, pos_occ(vtbl->eterm[x1]), v->size, v->data, fun_var_range_type(solver, x1));
  u = egraph_make_apply(egraph, pos_occ(vtbl->eterm[x2]), v->size, v->data, fun_var_range_type(solver, x2));
  eq = egraph_make_eq(egraph, pos_occ(t), pos_occ(u));

#if 0
  printf("---> ARRAY SOLVER: interface lemma for f!%"PRId32" /= f!%"PRId32" ----\n", x1, x2);
#endif

#if TRACE
  printf("\n---> Array solver: reconciliation lemma for f!%"PRId32" /= f!%"PRId32" ----\n", x1, x2);
  print_eterm_def(stdout, solver->egraph, vtbl->eterm[x1]);
  print_eterm_def(stdout, solver->egraph, vtbl->eterm[x2]);
  printf("New terms:\n");
  print_eterm_def(stdout, egraph, t);
  print_eterm_def(stdout, egraph, u);
  printf("Antecedent:\n");
  print_literal(stdout, l);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, egraph, l);
  printf("\n");
  printf("Disequality:\n");
  print_literal(stdout, eq);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, egraph, eq);
  printf("\n");
  printf("Clause:\n");
  printf("  (OR ");
  print_literal(stdout, not(l));
  printf(" ");
  print_literal(stdout, not(eq));
  printf(")\n\n");
#endif

  add_binary_clause(solver->core, not(l), not(eq));

  ivector_reset(v);

  solver->stats.num_extensionality_axiom ++;
}



/*************************
 *  MODEL CONSTRUCTION   *
 ************************/

/*
 * Collect all the root variables and group them by types
 * - all the root variables are added to vector roots
 * - they are sorted by types
 */
static void fun_solver_collect_roots(fun_solver_t *solver, ivector_t *roots) {
  fun_vartable_t *vtbl;
  uint32_t i, n;

  assert(roots->size == 0);

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (vtbl->root[i] == i) {
      // i is a root
      ivector_push(roots, i);
    }
  }

  // sort the vector
  int_array_sort2(roots->data, roots->size, vtbl, (int_cmp_fun_t) root_lt);
}


/*
 * Convert a negative base_value code into a fresh particle of type sigma
 * - k = code
 * - if sigma is finite, we use the fresh_hmap
 */
static particle_t fun_solver_fresh_particle(fun_solver_t *solver, int32_t k, type_t sigma, pstore_t *store) {
  int_hmap2_t *hmap;
  int_hmap2_rec_t *r;
  bool new;
  particle_t d;

  assert(k < 0);

  if (is_finite_type(solver->types, sigma)) {
    k = (- k) - 1;
    assert(0 <= k && k < type_card(solver->types, sigma));

    hmap = fun_solver_get_fresh_hmap(solver);
    r = int_hmap2_get(hmap, sigma, k, &new);
    if (new) {
      r->val = pstore_fresh_particle(store, sigma);
    }
    d = r->val;
  } else {
    // infinite type:
    d = pstore_fresh_particle(store, sigma);
  }

  return d;
}


/*
 * Convert a unary application c = (apply g i) to a pair [idx -> val]
 * - f = type descriptor for the function g
 * - idx is defined by the egraph label of i
 * - val is defined by the egraph label of c
 * - add the pair [idx -> val] to map
 */
static void convert_composite_to_map1(egraph_t *egraph, function_type_t *f, map_t *map, composite_t *c, pstore_t *store) {
  elabel_t l_idx, l_val;
  particle_t idx, val;

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_arity(c) == 2 && f->ndom == 1);

  l_idx = egraph_label(egraph, composite_child(c, 1));    // label of i
  l_val = egraph_term_label(egraph, c->id);               // label of c
  idx = pstore_labeled_particle(store, l_idx, f->domain[0]);
  val = pstore_labeled_particle(store, l_val, f->range);
  add_elem_to_map(map, idx, val);
}


/*
 * Convert a non-unary application c = (apply g i_1 ... i_n) to a pair [idx -> val]
 * - f = type descriptor for function g
 * - idx = tuple particle for [i_1, ..., i_n]
 * - val is defined by the label of c in egraph
 * - add the pair [idx -> val] to map
 */
static void convert_composite_to_map(egraph_t *egraph, function_type_t *f, map_t *map, composite_t *c, pstore_t *store) {
  particle_t *a;
  uint32_t i, n;
  elabel_t l;
  particle_t idx, val;
  particle_t aux[10];

  assert(composite_kind(c) == COMPOSITE_APPLY && composite_arity(c) == f->ndom + 1 && f->ndom > 1);

  n = f->ndom;
  if (n <= 10) {
    a = aux;
  } else {
    a = safe_malloc(n * sizeof(particle_t));
  }

  for (i=0; i<n; i++) {
    l = egraph_label(egraph, composite_child(c, i+1)); // label for i-th argument of (apply g ..)
    a[i] = pstore_labeled_particle(store, l, f->domain[i]); // corresponding particle
  }

  idx = pstore_tuple_particle(store, n, a, f->domain);  // tuple a[0 ... n-1]

  if (n > 10) {
    safe_free(a);
  }

  l = egraph_term_label(egraph, c->id);
  val = pstore_labeled_particle(store, l, f->range);
  add_elem_to_map(map, idx, val);
}


/*
 * Initialize a map for variable x
 * - f = the type descriptor for type of x
 * - store = to create particles
 */
static map_t *build_map_for_var(fun_solver_t *solver, function_type_t *f, thvar_t x, pstore_t *store) {
  void **app;
  map_t *map;
  map_t *base_map;
  egraph_t *egraph;
  int32_t b;
  uint32_t i, n;

  assert(0 <= x && x < solver->vtbl.nvars && solver->vtbl.root[x] == x);

  app = solver->vtbl.app[x]; // set of composites for x
  n = 0;
  if (app != NULL) {
    n = pv_size(app);
  }
  map = new_map(n);

  egraph = solver->egraph;


  /*
   * Convert each element of app into a pair [idx->value]
   * and add each pair to the map. Small optimization:
   * distinguish between unary and non-unary functions.
   */
  if (f->ndom == 1) {
    for (i=0; i<n; i++) {
      convert_composite_to_map1(egraph, f, map, app[i], store);
    }
  } else {
    for (i=0; i<n; i++) {
      convert_composite_to_map(egraph, f, map, app[i], store);
    }
  }

  /*
   * Copy the default value from the base_map
   */
  b = solver->vtbl.base[x];
  base_map = solver->base_map[b];
  assert(base_map != NULL);
  set_map_default(map, map_default_value(base_map));

  /*
   * Normalize this
   */
  normalize_map(map);

  return map;
}



/*
 * Collect the base maps of all elements in v[0 ... n-1]
 * and force these base maps to be all distinct.
 * - store = particle store
 * - f = type descriptors of all variables in v[0 ... n-1]
 */
static void fix_base_maps(fun_solver_t *solver, pstore_t *store, function_type_t *f, thvar_t *v, uint32_t n) {
  uint8_t *mark;
  pvector_t w;
  uint32_t i, m;
  thvar_t x;
  int32_t b;

  m = solver->num_bases;
  mark = (uint8_t *) safe_malloc(m * sizeof(uint8_t));
  for (i=0; i<m; i++) {
    mark[i] = false;
  }

  /*
   * collect the base maps in vector w
   * mark[b] true means that base_map[b] is present in w
   */
  init_pvector(&w, m);
  for (i=0; i<n; i++) {
    x = v[i];
    assert(solver->vtbl.root[x] == x);
    b = solver->vtbl.base[x];
    assert(0 <= b && b < m);
    if (! mark[b]) {
      pvector_push(&w, solver->base_map[b]);
      mark[b] = true;
    }
  }

  // make all elements of w differ
  if (! force_maps_to_differ(store, f, w.size, (map_t **) w.data)) {
    // BUG
    abort();
  }

  safe_free(mark);
  delete_pvector(&w);
}


/*
 * Add the base_map for x to the current value[x]
 */
static void copy_base_map(fun_solver_t *solver, thvar_t x) {
  map_t *map;
  map_t *base_map;
  int32_t b;
  uint32_t i, n;

  assert(0 <= x && x < solver->vtbl.nvars && solver->vtbl.root[x] == x);

  map = solver->value[x];
  b = solver->vtbl.base[x];
  base_map = solver->base_map[b];
  assert(map != NULL && base_map != NULL);

  n = map_num_elems(base_map);
  for (i=0; i<n; i++) {
    add_elem_to_map(map, base_map->data[i].index, base_map->data[i].value);
  }

  normalize_map(map);
}



/*
 * Build the mapping for n variables v[0,..., n-1] of type tau
 * - all elements of v are root variables
 * - tree = function tree
 * - store = particle store
 */
static void build_maps_for_type(fun_solver_t *solver, type_t tau, uint32_t n, thvar_t *v,
                                fun_tree_t *tree, pstore_t *store) {
  map_t *map;
  function_type_t *f;
  uint32_t i;
  thvar_t x;
  particle_t d;
  int32_t b;
  type_t sigma;
  bool collision;

  assert(solver->value != NULL);


  /*
   * Prepare the tree for type tau
   */
  f = function_type_desc(solver->types, tau);
  reset_fun_tree(tree);
  set_fun_tree_type(tree, f);

  /*
   * Build the base maps for all elements in v
   */
  sigma = function_type_range(solver->types, tau);
  for (i=0; i<n; i++) {
    x = v[i];
    assert(solver->vtbl.root[x] == x && solver->vtbl.base[x] >= 0);
    b = solver->vtbl.base[x];
    map  = solver->base_map[b];
    if (map == NULL) {
      // get the default value for this component
      if (solver->base_value[b] < 0) {
        d = fun_solver_fresh_particle(solver, solver->base_value[b], sigma, store);
      } else {
        assert(egraph_label_is_valid(solver->egraph, solver->base_value[b]));
        d = pstore_labeled_particle(store, solver->base_value[b], sigma);
      }
      // the default base maps everything to d
      map = new_map(0);
      set_map_default(map, d);

      solver->base_map[b] = map;
    }
  }


  /*
   * Build the initial map for each element of v
   * and check whether the maps are distinct.
   */
  collision = false;
  for (i=0; i<n; i++) {
    x = v[i];
    assert(solver->vtbl.root[x] == x && solver->value[x] == NULL);
    map = build_map_for_var(solver, f, x, store);
    solver->value[x] = map;
    if (solver->reconciled) {
      // we must force all variables to have distinct values
      // in the model
      collision = (! fun_tree_add_map(tree, map)) || collision;
    }
  }

  if (collision) {
    // this should not happen unless f has finite range and infinite domain
    assert(solver->reconciled && is_finite_type(solver->types, sigma) &&
           !type_has_finite_domain(solver->types, tau));

    // update the base maps to make them all distinct
    fix_base_maps(solver, store, f, v, n);

    // propagate the new base maps to the variables in v
    for (i=0; i<n; i++) {
      x = v[i];
      copy_base_map(solver, x);
    }

  }

}



/*
 * Build the mapping for all variables in vector v
 * - the variables are sorted by types in v
 * - all variables of v are root variables
 * - tree = function tree used to ensure distinct connected components (i.e., bases)
 *          have different base maps
 * - store = particle store to use
 */
static void fun_solver_build_maps(fun_solver_t *solver, ivector_t *v, fun_tree_t *tree, pstore_t *store) {
  fun_vartable_t *vtbl;
  thvar_t *a;
  thvar_t x;
  uint32_t i, n, m;
  type_t tau;

  vtbl = &solver->vtbl;

  m = 0;
  n = v->size;
  a = v->data;
  while (m < n) {
    x = a[m];
    assert(vtbl->root[x] == x);
    tau = vtbl->type[x];

    for (i = m+1; i<n; i++) {
      x = a[i];
      assert(vtbl->root[x] == x);
      if (vtbl->type[x] != tau) {
        assert(vtbl->type[x] > tau);
        break;
      }
    }

    // vars of type tau are in a[m ... i-1]: build their maps
    assert(m < i && i <= n);
    build_maps_for_type(solver, tau, i - m, a + m, tree, store);
    m = i;
  }
}


/*
 * Assign a map to all root variables
 * - each map is of type map_t *
 * - it's built as a map from abstract values to abstract values (particles)
 * - all particles used in the construction must be created in store
 */
void fun_solver_build_model(fun_solver_t *solver, pstore_t *store) {
  ivector_t root_vector;
  fun_tree_t fun_tree;

  assert(!solver->bases_ready && !solver->apps_ready);

#if TRACE
  printf("\n**** BUILD MODEL ***\n\n");
  print_egraph_terms(stdout, solver->egraph);
  printf("\n\n");
  print_egraph_root_classes_details(stdout, solver->egraph);
#endif

  if (solver->vtbl.nvars > 0) {
    // rebuild the classes, connected components, app maps, and base values
    fun_solver_build_classes(solver);
    fun_solver_build_components(solver);
    fun_solver_build_apps(solver);
    fun_solver_normalize_apps(solver);
    fun_solver_init_base_value(solver);
    fun_solver_assign_base_values(solver);

    // allocate internal arrays of maps
    fun_solver_init_values(solver);
    fun_solver_init_base_maps(solver, solver->num_bases);

#if TRACE
    printf("\n--- Build model ---\n");
    printf("Classes:\n");
    print_fsolver_classes(stdout, solver);
    printf("\nDisequalities:\n");
    print_fsolver_diseqs(stdout, solver);
    printf("\nMaps:\n");
    print_fsolver_maps(stdout, solver);
    printf("\nBase values\n");
    print_fsolver_base_values(stdout, solver);;
    printf("\n\n");
#endif

    init_ivector(&root_vector, 20);  // to collect the set of roots
    init_fun_tree(&fun_tree, store); // to ensure base maps are distinct

    fun_solver_collect_roots(solver, &root_vector);
    fun_solver_build_maps(solver, &root_vector, &fun_tree, store);

#if TRACE
    printf("\n--- Build model ---\n");
    print_fsolver_maps(stdout, solver);
    printf("\n\n");
    print_fsolver_values(stdout, solver);
    printf("\n\n");
#endif

    // cleanup
    fun_solver_delete_base_maps(solver);
    fun_solver_delete_fresh_hmap(solver);
    delete_fun_tree(&fun_tree);
    delete_ivector(&root_vector);
  }
}


/*
 * Return the map assigned to theory variable x
 * - that's the map of root[x]
 * - return NULL if there's no value for x (failure of some kind)
 */
map_t *fun_solver_value_in_model(fun_solver_t *solver, thvar_t x) {
  assert(0 <= x && x < solver->vtbl.nvars && solver->value != NULL);
  x = solver->vtbl.root[x];
  return solver->value[x];
}


/*
 * Free all internal structures used in the model construction
 */
void fun_solver_free_model(fun_solver_t *solver) {
  if (solver->vtbl.nvars > 0) {
    fun_solver_delete_values(solver);
    fun_solver_cleanup(solver);
    safe_free(solver->base_value);
    solver->base_value = NULL;
  }
}



/********************************
 *  GARBAGE COLLECTION SUPPORT  *
 *******************************/

/*
 * Mark all types used by solver (protect them from deletion in type_table_gc)
 * - scan the variable table and mark every type in table->type[x]
 */
void fun_solver_gc_mark(fun_solver_t *solver) {
  fun_vartable_t *vtbl;
  type_table_t *types;
  uint32_t i, n;

  types = solver->types;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    type_table_set_gc_mark(types, vtbl->type[i]);
  }
}





/***************************
 *  INTERFACE DESCRIPTORS  *
 **************************/

/*
 * Control and generic interface for the egraph
 */
static th_ctrl_interface_t fsolver_control = {
  (start_intern_fun_t) fun_solver_start_internalization,
  (start_fun_t) fun_solver_start_search,
  (propagate_fun_t) fun_solver_propagate,
  (final_check_fun_t) fun_solver_final_check,
  (increase_level_fun_t) fun_solver_increase_decision_level,
  (backtrack_fun_t) fun_solver_backtrack,
  (push_fun_t) fun_solver_push,
  (pop_fun_t) fun_solver_pop,
  (reset_fun_t) fun_solver_reset,
  (clear_fun_t) fun_solver_clear,
};

static th_egraph_interface_t fsolver_egraph = {
  (assert_eq_fun_t) fun_solver_assert_var_eq,
  (assert_diseq_fun_t) fun_solver_assert_var_diseq,
  (assert_distinct_fun_t) fun_solver_assert_var_distinct,
  (check_diseq_fun_t) fun_solver_check_disequality,
  (is_constant_fun_t) fun_solver_var_is_constant,
  NULL, // no need for expand_th_explanation
  (reconcile_model_fun_t) fun_solver_reconcile_model,
  (prepare_model_fun_t) fun_solver_prepare_model,
  (equal_in_model_fun_t) fun_solver_var_equal_in_model,
  (gen_inter_lemma_fun_t) fun_solver_gen_interface_lemma, // gen_interface_lemma
  (release_model_fun_t) fun_solver_release_model,
  NULL, // build_model_partition,
  NULL, // release_model_partition,
  (attach_to_var_fun_t) fun_solver_attach_eterm,
  (get_eterm_fun_t) fun_solver_get_eterm_of_var,
  (select_eq_polarity_fun_t) fun_solver_select_eq_polarity,
};


/*
 * Fun-theory interface for the egraph
 */
static fun_egraph_interface_t fsolver_fun_egraph = {
  (make_fun_var_fun_t) fun_solver_create_var,
  (fun_build_model_fun_t) fun_solver_build_model,
  (fun_val_fun_t) fun_solver_value_in_model,
  (fun_free_model_fun_t) fun_solver_free_model,
};



/*
 * Access to the interface descriptors
 */
th_ctrl_interface_t *fun_solver_ctrl_interface(fun_solver_t *solver) {
  return &fsolver_control;
}

th_egraph_interface_t *fun_solver_egraph_interface(fun_solver_t *solver) {
  return &fsolver_egraph;
}

fun_egraph_interface_t *fun_solver_fun_egraph_interface(fun_solver_t *solver) {
  return &fsolver_fun_egraph;
}


