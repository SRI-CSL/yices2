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

#include "weak_eq_graph.h"

#include "mcsat/tracing.h"

#include "utils/int_array_sort2.h"
#include "utils/ptr_vectors.h"
#include "utils/refcount_strings.h"


#define USE_ARRAY_DIFF 0 //experimental

// declaration
void weq_graph_stats_init(weq_graph_t* weq);

void weq_graph_construct(weq_graph_t* weq, plugin_context_t* ctx, eq_graph_t* eq) {
  weq->ctx = ctx;
  scope_holder_construct(&weq->scope);

  weq->eq_graph = eq;

  init_ivector(&weq->array_terms, 0);
  init_ivector(&weq->array_eq_terms, 0);
  init_ivector(&weq->select_terms, 0);

  init_int_hmap(&weq->type_to_diff, 0);
  init_int_hset(&weq->diff_funs, 0);
  init_ptr_hmap(&weq->fun_node_map, 0);

  init_int_hmap(&weq->val_id_term_map, 0);
  init_ivector(&weq->path_cond, 0);
  init_ivector(&weq->path_indices1, 0);
  init_ivector(&weq->path_indices2, 0);

  weq_graph_stats_init(weq);
}

void weq_graph_destruct(weq_graph_t* weq) {
  scope_holder_destruct(&weq->scope);

  delete_ivector(&weq->array_terms);
  delete_ivector(&weq->array_eq_terms);
  delete_ivector(&weq->select_terms);

  delete_int_hmap(&weq->type_to_diff);
  delete_int_hset(&weq->diff_funs);
  delete_ivector(&weq->path_cond);
  delete_ivector(&weq->path_indices1);
  delete_ivector(&weq->path_indices2);

  weq_graph_clear(weq);
  delete_ptr_hmap(&weq->fun_node_map);
  delete_int_hmap(&weq->val_id_term_map);
}

void weq_graph_push(weq_graph_t* weq) {
  scope_holder_push(&weq->scope,
                    &weq->array_terms.size,
                    &weq->array_eq_terms.size,
                    &weq->select_terms.size,
                    NULL);
}

void weq_graph_pop(weq_graph_t* weq) {
  uint32_t t1, t2, t3;

  // Pop the int variable values
  scope_holder_pop(&weq->scope,
                   &t1, &t2, &t3,
                   NULL);

  ivector_shrink(&weq->array_terms, t1);
  ivector_shrink(&weq->array_eq_terms, t2);
  ivector_shrink(&weq->select_terms, t3);
}

void weq_graph_stats_init(weq_graph_t* weq) {
  weq->stats.array_check_calls = statistics_new_int(weq->ctx->stats, "mcsat::uf::array_check_calls");
  weq->stats.array_terms = statistics_new_int(weq->ctx->stats, "mcsat::uf::array_terms");
  weq->stats.select_terms = statistics_new_int(weq->ctx->stats, "mcsat::uf::select_terms");
  weq->stats.array_update1_axioms = statistics_new_int(weq->ctx->stats, "mcsat::uf::array_update1_axioms");
  weq->stats.array_update2_axioms = statistics_new_int(weq->ctx->stats, "mcsat::uf::array_update2_axioms");
  weq->stats.array_ext_axioms = statistics_new_int(weq->ctx->stats, "mcsat::uf::array_ext_axioms");
}

// declaration
static void weq_graph_add_diff_terms_vars(weq_graph_t* weq, term_t arr);

// save array (vars and updates) terms
void weq_graph_add_array_term(weq_graph_t* weq, term_t arr) {
  if (USE_ARRAY_DIFF) {
    weq_graph_add_diff_terms_vars(weq, arr);
  }
  ivector_push(&weq->array_terms, arr);
}

// save array equality terms -- present in the formula
void weq_graph_add_array_eq_term(weq_graph_t* weq, term_t arr_eq) {
  ivector_push(&weq->array_eq_terms, arr_eq);
}

// save select terms
void weq_graph_add_select_term(weq_graph_t* weq, term_t sel) {
  term_table_t* terms = weq->ctx->terms;
  composite_term_t* t_desc = app_term_desc(terms, sel);
  if (!weq_graph_has_diff_fun(weq, t_desc->arg[0])) {
    ivector_push(&weq->select_terms, sel);
  }
}

// save diff function (not a diff function application)
void weq_graph_add_diff_fun(weq_graph_t* weq, term_t diff_fun) {
  int_hset_add(&weq->diff_funs, diff_fun);
}

// check if diff function is present in the diff_funs set
bool weq_graph_has_diff_fun(weq_graph_t* weq, term_t diff_fun) {
  return int_hset_member(&weq->diff_funs, diff_fun);
}


/* Weakly equivalant graph node, where
 * p = primary node
 * pstore = update term that created the primary edge (the edge between this node and p)
 * pi = index in the update term (pstore)
 * s = secondary node
 * sstore = update term that created the secondary edge (the edge between this node and s)
 *
 * see Weakly Equivalent Arrays paper:
 * https://link.springer.com/chapter/10.1007/978-3-319-24246-0_8
 */
typedef struct weq_graph_node_s {
  struct weq_graph_node_s* p;
  term_t pstore;
  term_t pi;
  struct weq_graph_node_s* s;
  term_t sstore;
} weq_graph_node_t;  

/* Clear the weq_graph
 * Free the memory used for the graph nodes
 * Clear the cache for the graph nodes
 * Clear the cache for the vales to terms map (used to find a rep term)
 */
void weq_graph_clear(weq_graph_t* weq) {
  ptr_hmap_pair_t *p;
  for (p = ptr_hmap_first_record(&weq->fun_node_map);
       p != NULL;
       p = ptr_hmap_next_record(&weq->fun_node_map, p)) {
    safe_free((weq_graph_node_t *) p->val);
  }
  ptr_hmap_reset(&weq->fun_node_map);
  int_hmap_reset(&weq->val_id_term_map);
}

/* Create a new weq_graph node
 */
static inline weq_graph_node_t *weq_new_node() {
  weq_graph_node_t *n = safe_malloc(sizeof(weq_graph_node_t));
  n->p = NULL;
  n->pstore = NULL_TERM;
  n->pi = NULL_TERM;
  n->s  = NULL;
  n->sstore = NULL_TERM;
  return n;
}

/* Find the weakly-equivalent root node of a given weq_graph node
 */
static const weq_graph_node_t* weq_graph_get_rep(const weq_graph_node_t* n) {
  const weq_graph_node_t* res = n;
  // root (rep) node doesn't have a primary edge
  while (res->p != NULL) {
    res = res->p;
  }
  return res;
}

/* Count the number of primary edges from a given node n to its root
 * node.
 */
static uint32_t count_primary(const weq_graph_node_t* n) {
  uint32_t res = 0;
  const weq_graph_node_t* tmp = n;
  
  while (tmp->p != NULL) {
    tmp = tmp->p;
    res++;
  }
  return res;
}

/* Find the weak-equivalent root node (weak-i rep node) of the weak
 * path on index idx.  The weak path on index idx doesn't mask on idx,
 * i.e. the indices in the updates present on the edges of the path
 * are not equivalent to idx.
 */
static const weq_graph_node_t* weq_graph_get_rep_i(const weq_graph_t* weq,
                                                   const weq_graph_node_t* n,
                                                   const term_t idx) {
  const weq_graph_node_t* res = n;
  while (res->p != NULL) {
    if (eq_graph_are_equal(weq->eq_graph, res->pi, idx)) {
      if (res->s == NULL) {
        // no secondary edge means that we have found the node
        break;
      }
      res = res->s;
    } else {
      res = res->p;
    }
  }
  return res;
}

/* Count the number of nodes that have primary edges masking the index
 * idx.
 */
static
uint32_t weq_graph_count_secondary(const weq_graph_t* weq, const weq_graph_node_t* n,
                                   const term_t idx) {
  uint32_t res = 0;
  const weq_graph_node_t* tmp = n;
  while (tmp->p != NULL) {
    if (eq_graph_are_equal(weq->eq_graph, tmp->pi, idx)) {
      if (tmp->s == NULL) {
        break;
      }
      tmp = tmp->s;
      res++;
    } else {
      tmp = tmp->p;
    }
  }
  return res;
}

/* Find the next node with primary edge masking index idx.
 */
static
weq_graph_node_t* weq_graph_find_secondary_node(weq_graph_t* weq,
                                                weq_graph_node_t* n, term_t idx) {
  weq_graph_node_t* res = n;
  while (res->p != NULL && !eq_graph_are_equal(weq->eq_graph, res->pi, idx)) {
    res = res->p;
  }
  return res;
}

/* const version of the weq_graph_find_secondary_node
 */
static
const weq_graph_node_t* weq_graph_find_secondary_node_const(weq_graph_t* weq,
                                                            const weq_graph_node_t* n,
                                                            term_t idx) {
  const weq_graph_node_t* res = n;
  while (res->p != NULL && !eq_graph_are_equal(weq->eq_graph, res->pi, idx)) {
    res = res->p;
  }
  return res;
}


#ifndef NDEBUG

/* helper function to extract index from an update term
 */
static inline
term_t weq_graph_get_index_from_store(weq_graph_t* weq, term_t store) {
  term_table_t* terms = weq->ctx->terms;
  assert(term_kind(terms, store) == UPDATE_TERM);
  composite_term_t* t_desc = update_term_desc(terms, store);
  return t_desc->arg[1];
}

#endif


/* add t to vec if t is not the true term
 */
static inline
void add_if_not_true_term(ivector_t* vec, term_t t) {
  if (t != true_term) {
    ivector_push(vec, t);
  }
}

/* make the given node weak-i representative, by inverting the
 * secondary edges
 */
static void weq_graph_make_rep_i(weq_graph_t* weq, weq_graph_node_t* n) {
  if (n->s == NULL) {
    return;
  }

  weq_graph_node_t* prev = n;
  weq_graph_node_t* next = n->s;
  term_t prev_store = n->sstore;
  term_t idx = n->pi;
  weq_graph_node_t* tmp = NULL;
  term_t tmp_sec_store = NULL_TERM;
  
  while (next) {
    next = weq_graph_find_secondary_node(weq, next, idx);
    tmp = next->s;
    tmp_sec_store = next->sstore;

    next->s = prev;
    next->sstore = prev_store;

    assert(!eq_graph_are_equal(weq->eq_graph, next->pi,
                               weq_graph_get_index_from_store(weq, next->sstore)));

    prev = next;
    prev_store = tmp_sec_store;
    next = tmp;
  }

  n->s = NULL;
  n->sstore = NULL_TERM;
}

/* make the given node a weak representative (root) node, by inverted
 * the primary edges
 */
static void weq_graph_make_rep(weq_graph_t* weq, weq_graph_node_t* n) {
  if (n->p == NULL) {
    return;
  }

  weq_graph_node_t* tmp = n;
  weq_graph_node_t* prev = NULL;
  weq_graph_node_t* next = NULL;
  pvector_t to_process;
  init_pvector(&to_process, 0);

  // invert all the primary edges
  // first goto the root and keep track of the visited nodes in a stack
  while (tmp) {
    pvector_push(&to_process, tmp);
    tmp = tmp->p;
  }

  // now invert he primary edges by popping nodes from the stack
  prev = pvector_pop2(&to_process);
  while (to_process.size > 0) {
    next = pvector_pop2(&to_process);
    prev->p = next;
    prev->pstore = next->pstore;
    prev->pi = next->pi;

    next->p = NULL;
    // make sure the node is weak-rep-i
    weq_graph_make_rep_i(weq, next);
    next->pstore = NULL_TERM;
    next->pi = NULL_TERM;

    prev = next;
  }

  delete_pvector(&to_process);
}

/* Get representative term w.r.t. the equality graph.
 * This assumes that the term has been assigned a value.
 * To find a representative term, we pick one term from
 * the equivalence class whose root is a value node.
 */
static term_t weq_graph_get_term_rep(weq_graph_t* weq, term_t t) {
  assert(eq_graph_term_has_value(weq->eq_graph, t));

  eq_node_id_t val_id = eq_graph_get_propagated_term_value_id(weq->eq_graph, t);

  int_hmap_pair_t *v = int_hmap_find(&weq->val_id_term_map, val_id);
  if (v == NULL) {
    v = int_hmap_get(&weq->val_id_term_map, val_id);
    v->val = t;
  }

  assert(eq_graph_are_equal(weq->eq_graph, t, v->val));

  return v->val;
}

/* Add secondary edge from the node a to node b. 
 * store is saved as the update term for that secondary edge.
 */
static void weq_graph_add_secondary(weq_graph_t* weq, int_hset_t* idx_set,
                                    weq_graph_node_t* a, weq_graph_node_t* b, term_t store) {
  assert(b->p == NULL);
  weq_graph_node_t* n = a;
  while (n != b) {
    assert(n->p);
    if (!int_hset_member(idx_set, weq_graph_get_term_rep(weq, n->pi)) &&
        weq_graph_get_rep_i(weq, n, n->pi) != b) {
      weq_graph_make_rep_i(weq, n);
      assert(!eq_graph_are_equal(weq->eq_graph, n->pi,
                                 weq_graph_get_index_from_store(weq, store)));
      n->s = b;
      n->sstore = store;
    }
    int_hset_add(idx_set, weq_graph_get_term_rep(weq, n->pi));
    n = n->p;
  }
}

/* Add the update term in the weq_graph.
 * Add the store (update term) on the primary edge or call add-secondary.
 */
static void weq_graph_add_store(weq_graph_t* weq, weq_graph_node_t* a, weq_graph_node_t* b,
                                term_t idx, term_t store) {
  if (a == b) {
    return;
  }

  weq_graph_make_rep(weq, b);
  if (weq_graph_get_rep(a) == b) {
    int_hset_t s;
    init_int_hset(&s, 0);
    int_hset_add(&s, weq_graph_get_term_rep(weq, idx));
    weq_graph_add_secondary(weq, &s, a, b, store);
    delete_int_hset(&s);
  } else {
    assert(b->p == NULL);
    b->p = a;
    b->pstore = store;
    b->pi = idx;
  }
}

/* Get the weq graph node for a given term.
 * We create a single node for all equivalent terms in the equality graph.
 * If not in cache, create a new one.
 */
static weq_graph_node_t *weq_graph_get_node(weq_graph_t* weq, term_t t) {
  term_t t_rep = weq_graph_get_term_rep(weq, t);
  ptr_hmap_pair_t *v = ptr_hmap_find(&weq->fun_node_map, t_rep);
  if (v == NULL) {
    v = ptr_hmap_get(&weq->fun_node_map, t_rep);
    weq_graph_node_t *n = weq_new_node();
    v->val = n;
  }

  return v->val;
}

/* Step through one primary edge, storing the path conditions and the
 * indices.
 */
static
term_t weq_graph_compute_weak_path_primary(weq_graph_t* weq, term_t arr,
                                           ivector_t* indices,
                                           ivector_t* path_cond) {
  const weq_graph_node_t* a = weq_graph_get_node(weq, arr);
  term_t res = NULL_TERM;
  composite_term_t* t_desc = NULL;
  term_table_t* terms = weq->ctx->terms;

  assert(a->p);
  t_desc = update_term_desc(terms, a->pstore);

  if (eq_graph_are_equal(weq->eq_graph, t_desc->arg[0], arr)) {
    ivector_push(path_cond, _o_yices_eq(t_desc->arg[0], arr));
    res = a->pstore;
  } else {
    ivector_push(path_cond, _o_yices_eq(a->pstore, arr));
    res = t_desc->arg[0];
  }

  assert(a->pi == weq_graph_get_index_from_store(weq, a->pstore));
  ivector_push(indices, a->pi);

  return res;
}

/* Compute a weak path between arr1 and arr2.
 * arr1 and arr2 are terms
 */
static void weq_graph_compute_weak_path(weq_graph_t* weq, term_t arr1,
                                        term_t arr2, ivector_t* indices,
                                        ivector_t* path_cond) {
  const weq_graph_node_t* a = weq_graph_get_node(weq, arr1);
  const weq_graph_node_t* b = weq_graph_get_node(weq, arr2);

  //arr1 and arr2 must be in the same weak equivalence class
  assert(weq_graph_get_rep(a) == weq_graph_get_rep(b));

  if (a == b) {
    ivector_push(path_cond, _o_yices_eq(arr1, arr2));
    return;
  }

  uint32_t prim_cnt1 = count_primary(a);
  uint32_t prim_cnt2 = count_primary(b);
  term_t t1 = arr1;
  term_t t2 = arr2;
  
  while (prim_cnt1 > prim_cnt2) {
    t1 = weq_graph_compute_weak_path_primary(weq, t1, indices, path_cond);
    a = a->p;
    prim_cnt1--;
  }

  while (prim_cnt2 > prim_cnt1) {
    t2 = weq_graph_compute_weak_path_primary(weq, t2, indices, path_cond);
    b = b->p;
    prim_cnt2--;
  }

  while (a != b) {
    t1 = weq_graph_compute_weak_path_primary(weq, t1, indices, path_cond);
    a = a->p;

    t2 = weq_graph_compute_weak_path_primary(weq, t2, indices, path_cond);
    b = b->p;
  }

  assert(a == b);
  if (t1 != t2) {
    ivector_push(path_cond, _o_yices_eq(t1, t2));
  }
}

/* Compute the path between the arr term and the next secondary node.
 * Save the update terms in the path_cond vector and the indices
 * present on the edges in the indices vector.
 */
static
term_t weq_graph_compute_path_secondary(weq_graph_t* weq, term_t arr,
                                        term_t idx,
                                        ivector_t* indices,
                                        ivector_t* path_cond) {
  term_t res = NULL_TERM;
  term_table_t* terms = weq->ctx->terms;
  const weq_graph_node_t* tmp =
    weq_graph_find_secondary_node_const(weq, weq_graph_get_node(weq, arr), idx);

  assert(tmp->sstore != NULL_TERM);
  assert(tmp->pi != NULL_TERM);
  assert(tmp->s);
  assert(eq_graph_are_equal(weq->eq_graph, tmp->pi, idx));
  assert(!eq_graph_are_equal(weq->eq_graph, idx,
                             weq_graph_get_index_from_store(weq, tmp->sstore)));

  composite_term_t* t_desc = update_term_desc(terms, tmp->sstore);

  if (weq_graph_find_secondary_node_const(weq, weq_graph_get_node(weq, t_desc->arg[0]),
                                          idx) == tmp) {
    weq_graph_compute_weak_path(weq, arr, t_desc->arg[0], indices, path_cond);
    res = tmp->sstore;
  } else {
    assert(weq_graph_find_secondary_node_const(weq,
                                               weq_graph_get_node(weq, tmp->sstore),
                                               idx) == tmp);

    weq_graph_compute_weak_path(weq, arr, tmp->sstore, indices, path_cond);
    res = t_desc->arg[0];
  }

  ivector_push(indices, t_desc->arg[1]);

  return res;
}

/* Compute weak-i (index) path, the path doesn't mask index idx.
 * Store the path conditions and the indices on the edges of the path.
 */
static
void weq_graph_compute_weak_path_i(weq_graph_t* weq, term_t arr1,
                                   term_t arr2, term_t idx,
                                   ivector_t* indices,
                                   ivector_t* path_cond) {
  const weq_graph_node_t* a = weq_graph_get_node(weq, arr1);
  const weq_graph_node_t* b = weq_graph_get_node(weq, arr2);
  uint32_t sec_cnt1 = weq_graph_count_secondary(weq, a, idx);  
  uint32_t sec_cnt2 = weq_graph_count_secondary(weq, b, idx);

  assert(weq_graph_get_rep_i(weq, a, idx) ==
         weq_graph_get_rep_i(weq, b, idx));

  while (sec_cnt1 > sec_cnt2) {
    arr1 = weq_graph_compute_path_secondary(weq, arr1, idx, indices, path_cond);
    sec_cnt1--;
    a = weq_graph_get_node(weq, arr1);

    assert(weq_graph_count_secondary(weq, a, idx) == sec_cnt1);
    assert(weq_graph_get_rep_i(weq, a, idx) == weq_graph_get_rep_i(weq, b, idx));
  }
  while (sec_cnt2 > sec_cnt1) {
    arr2 = weq_graph_compute_path_secondary(weq, arr2, idx, indices, path_cond);
    sec_cnt2--;
    b = weq_graph_get_node(weq, arr2);

    assert(weq_graph_count_secondary(weq, b, idx) == sec_cnt2);
    assert(weq_graph_get_rep_i(weq, a, idx) == weq_graph_get_rep_i(weq, b, idx));
  }

  assert(sec_cnt1 == sec_cnt2);
  while (weq_graph_find_secondary_node_const(weq, a, idx) !=
         weq_graph_find_secondary_node_const(weq, b, idx)) {

    assert(weq_graph_count_secondary(weq, a, idx) ==
           weq_graph_count_secondary(weq, b, idx));

    arr1 = weq_graph_compute_path_secondary(weq, arr1, idx, indices, path_cond);
    arr2 = weq_graph_compute_path_secondary(weq, arr2, idx, indices, path_cond);
    a = weq_graph_get_node(weq, arr1);
    b = weq_graph_get_node(weq, arr2);

    assert(weq_graph_get_rep_i(weq, a, idx) == weq_graph_get_rep_i(weq, b, idx));
  }

  weq_graph_compute_weak_path(weq, arr1, arr2, indices, path_cond);
}

/* Add variables for the diff terms. It will create diff terms for the
 * give arr term and all the earlier stored array terms. It will also
 * store select terms on these diff terms as well.
 */
static
void weq_graph_add_diff_terms_vars(weq_graph_t* weq, term_t arr) {
  term_table_t* terms = weq->ctx->terms;
  type_t arr_type = term_type(terms, arr);
  type_t idx_type = function_type_domain(weq->ctx->types, arr_type, 0);

  term_t diff_fun;
  int_hmap_pair_t *diff = int_hmap_find(&weq->type_to_diff, arr_type);
  if (diff != NULL) {
    diff_fun = diff->val;
  } else {
    type_t dom[] = {arr_type, arr_type};
    type_t diff_fun_type = function_type(weq->ctx->types, idx_type, 2, dom);
    diff_fun = new_uninterpreted_term(terms, diff_fun_type);

    char fun_name_str[10];
    sprintf(fun_name_str, "diff_%i", weq->type_to_diff.nelems);
    set_term_name(terms, diff_fun, clone_string(fun_name_str));

    int_hmap_add(&weq->type_to_diff, arr_type, diff_fun);
    int_hset_add(&weq->diff_funs, diff_fun);
  }

  variable_db_get_variable(weq->ctx->var_db, arr);
  uint32_t i;
  for (i = 0; i < weq->array_terms.size; ++ i) {
    term_t arr2 = weq->array_terms.data[i];
    if (arr == arr2) {
      continue;
    }

    type_t arr2_type = term_type(terms, arr2);
    if (arr_type == arr2_type) {
      variable_db_get_variable(weq->ctx->var_db, arr2);

      term_t args[2];
      if (arr < arr2) {
        args[0] = arr;
        args[1] = arr2;
      } else {
        args[0] = arr2;
        args[1] = arr;
      }

      term_t diff_term = app_term(terms, diff_fun, 2, args);
      term_t select_arg[] = {diff_term};
      term_t diff_select1 = app_term(terms, arr, 1, select_arg);
      term_t diff_select2 = app_term(terms, arr2, 1, select_arg);
      variable_db_get_variable(weq->ctx->var_db, diff_term);
      variable_db_get_variable(weq->ctx->var_db, diff_select1);
      variable_db_get_variable(weq->ctx->var_db, diff_select2);

      ivector_push(&weq->select_terms, diff_select1);
      ivector_push(&weq->select_terms, diff_select2);
    }
  }
}

/* Check Array idx lemma.
 * Read over write 1: when idices are equal.
 */
/*
static
bool weq_graph_array_idx_check(weq_graph_t* weq, ivector_t* conflict,
                               const ivector_t* array_terms) {
  term_table_t* terms = weq->ctx->terms;
  uint32_t i;

  // array-idx lemma
  for (i = 0; i < array_terms->size; ++i) {
    term_t arr = array_terms->data[i];
    term_kind_t t_kind = term_kind(terms, arr);
    if (t_kind == UPDATE_TERM) {
      composite_term_t* t_desc = update_term_desc(terms, arr);
      term_t r = app_term(terms, arr, t_desc->arity - 2, t_desc->arg + 1);
      term_t v = t_desc->arg[t_desc->arity - 1];
      if (!eq_graph_term_has_value(weq->eq_graph, r) ||
          !eq_graph_term_has_value(weq->eq_graph, v))
        continue;
      if (!eq_graph_are_equal(weq->eq_graph, r, v)) {
        add_if_not_true_term(conflict, _o_yices_neq(r, v));

        if (ctx_trace_enabled(weq->ctx, "weq_graph::array")) {
          ctx_trace_printf(weq->ctx, ">1 Array conflict 1 BEGIN\n");
          uint32_t k;
          for (k = 0; k < conflict->size; ++ k) {
            ctx_trace_term(weq->ctx, conflict->data[k]);
          }
          ctx_trace_printf(weq->ctx, ">1 Array conflict 1 END\n");
        }
        return false;
      }
    }
  }
  return true;
}
*/


/* Checks if arr1 and arr2 terms are weakly equivalanet on index idx.
 * If it is case, it also stores indices and path conditions.
 */
static
bool weq_graph_array_weak_eq_i(weq_graph_t* weq, term_t arr1, term_t arr2,
                               term_t idx, ivector_t* indices,
                               ivector_t* path_cond) {
  bool res = false;
  uint32_t old_indices_size, old_path_cond_size;

  const weq_graph_node_t* fn_arr1 =
    weq_graph_get_rep_i(weq, weq_graph_get_node(weq, arr1), idx);
  const weq_graph_node_t* fn_arr2 =
    weq_graph_get_rep_i(weq, weq_graph_get_node(weq, arr2), idx);

  assert(fn_arr1 != NULL);
  assert(fn_arr2 != NULL);

  old_indices_size = indices->size;
  old_path_cond_size = path_cond->size;

  if (fn_arr1 == fn_arr2) {
    uint32_t k;

    res = true;
    weq_graph_compute_weak_path_i(weq, arr1, arr2, idx, indices, path_cond);

    // add indices
    for (k = old_indices_size; k < indices->size; ++k) {
      if (eq_graph_are_equal(weq->eq_graph, idx, indices->data[k])) {
        res = false;
        break;
      }
    }
  }

  if (!res) {
    ivector_shrink(indices, old_indices_size);
    ivector_shrink(path_cond, old_path_cond_size);
  }

  return res;
}

/* Check if arr1 and arr2 terms are weakly congruent on index idx.
 * If that is case, store path conditions in the path_cond vector.
 */
static
bool weq_graph_array_weak_congruence_i(weq_graph_t* weq, const ivector_t* select_terms,
                                       term_t arr1, term_t arr2,
                                       term_t idx, ivector_t* path_cond) {
  assert(eq_graph_term_has_value(weq->eq_graph, idx));

  bool res = false;
  term_table_t* terms = weq->ctx->terms;

  uint32_t i, j, k;
  uint32_t old_path_cond_size;
  
  if (path_cond) {
    old_path_cond_size = path_cond->size;
  }

  ivector_shrink(&weq->path_indices1, 0);
  if (weq_graph_array_weak_eq_i(weq, arr1, arr2, idx, &weq->path_indices1, path_cond)) {
    for (k =0; k < weq->path_indices1.size; ++k) {
      assert(idx != weq->path_indices1.data[k]);
      if (eq_graph_are_equal(weq->eq_graph, idx, weq->path_indices1.data[k])) {
        goto nextcheck;
      }
    }

    res = true;

    for (k =0; k < weq->path_indices1.size; ++k) {
      add_if_not_true_term(path_cond, _o_yices_neq(idx, weq->path_indices1.data[k]));
    }

    goto done;
  }

 nextcheck:
  if (path_cond) {
    ivector_shrink(path_cond, old_path_cond_size);
  }

  for (i = 0; !res && i < select_terms->size; ++ i) {
    term_t t_i = select_terms->data[i];
    type_t t_i_type = term_type(terms, t_i);
    assert(variable_db_get_variable_if_exists(weq->ctx->var_db, t_i) != variable_null);

    ivector_shrink(&weq->path_indices1, 0);
    composite_term_t* e_i_desc = app_term_desc(terms, t_i);
    if (!eq_graph_are_equal(weq->eq_graph, e_i_desc->arg[1], idx) ||
        !weq_graph_array_weak_eq_i(weq, arr1, e_i_desc->arg[0], idx, &weq->path_indices1, path_cond)) {
      continue;
    }

    uint32_t size1 = weq->path_indices1.size;
    uint32_t size2;
    if (path_cond) {
      size2 = path_cond->size;
    }

    for (j = 0; !res && j < select_terms->size; ++ j) {
      term_t t_j = select_terms->data[j];
      type_t t_j_type = term_type(terms, t_j);
      if (t_i_type != t_j_type ||
          !eq_graph_are_equal(weq->eq_graph, t_i, t_j)) {
        continue;
      }
      
      ivector_shrink(&weq->path_indices1, size1);
      if (path_cond) {
        ivector_shrink(path_cond, size2);
      }

      composite_term_t* e_j_desc = app_term_desc(terms, t_j);
      if (!eq_graph_are_equal(weq->eq_graph, e_j_desc->arg[1], idx) ||
          !weq_graph_array_weak_eq_i(weq, arr2, e_j_desc->arg[0], idx, &weq->path_indices1, path_cond)) {
        continue;
      }
      
      res = true;
      if (path_cond) {
        // Conditions of arr1 weakly-eq-i to a and arr2 weakly-eq-i to b'
        for (k = 0; k < weq->path_indices1.size; ++k) {
          if (eq_graph_are_equal(weq->eq_graph, weq->path_indices1.data[k], idx)) {
            res = false;
            break;
          }
        }

        if (res) {
          for (k = 0; k < weq->path_indices1.size; ++k) {
            add_if_not_true_term(path_cond, _o_yices_neq(idx, weq->path_indices1.data[k]));
          }

          add_if_not_true_term(path_cond, _o_yices_eq(idx, e_i_desc->arg[1]));
          add_if_not_true_term(path_cond, _o_yices_eq(t_i, t_j));
          add_if_not_true_term(path_cond, _o_yices_eq(idx, e_j_desc->arg[1]));

          goto done;
        }
      }
    }
  }

 done:
  if (!res && path_cond) {
    ivector_shrink(path_cond, old_path_cond_size);
  }

  return res;
}

/* Check array ext lemma: arr1 and arr2 should be equal, but they are
 * given different values. If that case, conflict will have the terms
 * that are in conflict.
 */
static
bool weq_graph_array_ext_lemma(weq_graph_t* weq, ivector_t* conflict,
                               term_t arr1, term_t arr2,
                               const ivector_t* select_terms) {
  bool res = true;
  term_table_t* terms = weq->ctx->terms;

  type_t arr1_type = term_type(terms, arr1);
  type_t arr2_type = term_type(terms, arr2);
  if (arr1 == arr2 || arr1_type != arr2_type ||
      eq_graph_are_equal(weq->eq_graph, arr1, arr2)) {
    return res;
  }
      
  const weq_graph_node_t* fn_arr1 = weq_graph_get_rep(weq_graph_get_node(weq, arr1));
  const weq_graph_node_t* fn_arr2 = weq_graph_get_rep(weq_graph_get_node(weq, arr2));

  if (fn_arr1 == fn_arr2) {
    bool ok = true;
    uint32_t k;
    
    ivector_shrink(&weq->path_cond, 0);
    ivector_shrink(&weq->path_indices2, 0);
    weq_graph_compute_weak_path(weq, arr1, arr2, &weq->path_indices2, &weq->path_cond);

    ivector_remove_duplicates(&weq->path_indices2);
    for (k = 0; k < weq->path_indices2.size; ++ k) {
      term_t idx = weq->path_indices2.data[k];
      if (!weq_graph_array_weak_congruence_i(weq, select_terms, arr1, arr2,
                                             idx, &weq->path_cond)) {
        ok = false;
        break;
      }
    }

    if (ok) {
      res = false;
      assert(conflict->size == 0);

      for (k = 0; k < weq->path_cond.size; ++k) {
        add_if_not_true_term(conflict, weq->path_cond.data[k]);
      }

      ivector_push(conflict, _o_yices_neq(arr1, arr2));

      ivector_remove_duplicates(conflict);

      if (ctx_trace_enabled(weq->ctx, "weq_graph::array")) {
        ctx_trace_printf(weq->ctx, ">2 Array conflict BEGIN 2\n");
        for (k = 0; k < conflict->size; ++ k) {
          ctx_trace_term(weq->ctx, conflict->data[k]);
        }
        ctx_trace_printf(weq->ctx, ">2 Array conflict END 2\n");
      }

      assert(conflict->size > 1);
      (*weq->stats.array_ext_axioms) ++;
    }
  }

  return res;
}

/* Check array ext conflicts (based on weakly equivalent arrays
 * reasoning) for all the array terms. It first check the lemma
 * between array terms that are present in the input formula. Then, it
 * check for all array pairs. If a conflict is found, the conflicting
 * terms are added to the conflict vector.
 */
static
bool weq_graph_array_ext_check(weq_graph_t* weq, ivector_t* conflict,
                               const ivector_t* array_eq_terms,
                               const ivector_t* array_terms,
                               const ivector_t* select_terms) {
  uint32_t i, j;
  bool res = true;

  term_table_t* terms = weq->ctx->terms;
  composite_term_t* t_desc = NULL;
  term_t arr1, arr2;
  int_hset_t seen;

  init_int_hset(&seen, 0);

  for (i = 0; res && i < array_eq_terms->size; ++i) {
    if (!int_hset_member(&seen, array_eq_terms->data[i])) {
      t_desc = eq_term_desc(terms, array_eq_terms->data[i]);
      arr1 = t_desc->arg[0];
      arr2 = t_desc->arg[1];

      res = weq_graph_array_ext_lemma(weq, conflict, arr1, arr2, select_terms);
      int_hset_add(&seen, array_eq_terms->data[i]);
    }
  }

  for (i = 1; res && i < array_terms->size; ++i) {
    arr1 = array_terms->data[i];
    
    for (j = 0; res && j < i; ++j) {
      arr2 = array_terms->data[j];
      if (!int_hset_member(&seen, _o_yices_eq(arr1, arr2))) {
        res = weq_graph_array_ext_lemma(weq, conflict, arr1, arr2, select_terms);
        int_hset_add(&seen, _o_yices_eq(arr1, arr2));
      }
    }
  }

  delete_int_hset(&seen);

  return res;
}

/* Check array ext conflicts (based on extensionality axiom over the
 * diff terms) between arr1 and arr2 terms. If a conflict is found,
 * the conflict terms are added in the conflict vector.
 */
static
bool weq_graph_array_ext_diff_lemma(weq_graph_t* weq, ivector_t* conflict,
                                    term_t arr1, term_t arr2) {

  term_table_t* terms = weq->ctx->terms;
  type_t arr1_type = term_type(terms, arr1);
  term_t diff_fun;
  int_hmap_pair_t *diff = int_hmap_find(&weq->type_to_diff, arr1_type);
  if (diff != NULL) {
    diff_fun = diff->val;
  } else {
    assert(false);
  }

  type_t arr2_type = term_type(terms, arr2);
  if (arr1 == arr2 ||
      !eq_graph_term_has_value(weq->eq_graph, arr1) ||
      !eq_graph_term_has_value(weq->eq_graph, arr2) ||
      arr1_type != arr2_type) {
    return true;
  }

  // order the arguments
  term_t args[2];
  if (arr1 < arr2) {
    args[0] = arr1;
    args[1] = arr2;
  } else {
    args[0] = arr2;
    args[1] = arr1;
  }
  term_t diff_term = app_term(terms, diff_fun, 2, args);
  term_t select_arg[] = {diff_term};
  term_t diff_select1 = app_term(terms, arr1, 1, select_arg);
  term_t diff_select2 = app_term(terms, arr2, 1, select_arg);
  if (!eq_graph_term_has_value(weq->eq_graph, diff_term) ||
      !eq_graph_term_has_value(weq->eq_graph, diff_select1) ||
      !eq_graph_term_has_value(weq->eq_graph, diff_select2)) {
    return true;
  }
      
  if (!eq_graph_are_equal(weq->eq_graph, arr1, arr2) &&
      eq_graph_are_equal(weq->eq_graph, diff_select1, diff_select2)) {

    assert(conflict->size == 0);

    add_if_not_true_term(conflict, _o_yices_neq(arr1, arr2));
    add_if_not_true_term(conflict, _o_yices_eq(diff_select1, diff_select2));

    ivector_remove_duplicates(conflict);

    if (ctx_trace_enabled(weq->ctx, "weq_graph::array")) {
      ctx_trace_printf(weq->ctx, ">2 Array conflict 2 BEGIN\n");
      uint32_t k;
      for (k = 0; k < conflict->size; ++ k) {
        ctx_trace_term(weq->ctx, conflict->data[k]);
      }
      ctx_trace_printf(weq->ctx, ">2 Array conflict 2 END\n");
    }

    assert(conflict->size > 1);
    (*weq->stats.array_ext_axioms) ++;

    return false;
  }

  return true;
}

/* Check array ext conflict (based on extensionality axiom over diff
 * terms) for all pairs of array terms. It first check for array pairs
 * that are present in an equality in the input formula. If a conflict
 * is found, the conflict terms are added in the conflict vector.
 */
static
bool weq_graph_array_ext_diff_check(weq_graph_t* weq, ivector_t* conflict,
                                    const ivector_t* array_eq_terms,
                                    const ivector_t* array_terms) {

  bool res = true;
  term_table_t* terms = weq->ctx->terms;
  uint32_t i, j;

  if (array_eq_terms) {
    composite_term_t* t_desc = NULL;
    for (i = 0; res && i < array_eq_terms->size; ++i) {
      t_desc = eq_term_desc(terms, array_eq_terms->data[i]);
      term_t arr1 = t_desc->arg[0];
      term_t arr2 = t_desc->arg[1];

      res = weq_graph_array_ext_diff_lemma(weq, conflict, arr1, arr2);
    }
  }

  if (array_terms) {
    for (i = 1; res && i < array_terms->size; ++i) {
      term_t arr1 = array_terms->data[i];
      assert(variable_db_get_variable_if_exists(weq->ctx->var_db, arr1) !=
             variable_null);
      if (!eq_graph_term_has_value(weq->eq_graph, arr1)) {
        continue;
      }

      for (j = 0; res && j < i; ++j) {
        term_t arr2 = array_terms->data[j];
        res = weq_graph_array_ext_diff_lemma(weq, conflict, arr1, arr2);
      }
    }
  }

  return res;
}

/* Check read-over-right conflict (based on weakly equivalent array
 * reasoning) for all select terms. If a conflict is found, the
 * conflict terms are added in the conflict vector.
 */
static
bool weq_graph_array_read_over_write_check(weq_graph_t* weq, ivector_t* conflict,
                                           const ivector_t* select_terms) {
  term_table_t* terms = weq->ctx->terms;
  uint32_t i, j, k;

  // generalized read-over-write lemma
  for (i = 1; i < select_terms->size; ++ i) {
    term_t t_i = select_terms->data[i];
    type_t t_i_type = term_type(terms, t_i);
    assert(variable_db_get_variable_if_exists(weq->ctx->var_db, t_i) != variable_null);
    composite_term_t* e_i_desc = app_term_desc(terms, t_i);

    for (j = 0; j < i; ++ j) {
      term_t t_j = select_terms->data[j];
      type_t t_j_type = term_type(terms, t_j);
      composite_term_t* e_j_desc = app_term_desc(terms, t_j);
      if (t_i == t_j ||
          t_i_type != t_j_type ||
          !eq_graph_are_equal(weq->eq_graph, e_i_desc->arg[1], e_j_desc->arg[1]) ||
          eq_graph_are_equal(weq->eq_graph, t_i, t_j)) {
        continue;
      }
      
      ivector_shrink(&weq->path_indices1, 0);
      ivector_shrink(&weq->path_cond, 0);

      if (weq_graph_array_weak_eq_i(weq, e_i_desc->arg[0], e_j_desc->arg[0],
                                    e_i_desc->arg[1], &weq->path_indices1, &weq->path_cond)) {
        // found conflict
        assert(conflict->size == 0);

        bool ok = true;
        for (k = 0; k < weq->path_indices1.size; ++ k) {
          assert(weq->path_indices1.data[k] != e_i_desc->arg[1]);
          if (eq_graph_are_equal(weq->eq_graph,
                                 e_i_desc->arg[1], weq->path_indices1.data[k])) {
            ok = false;
            break;
          }

          add_if_not_true_term(conflict,
                               _o_yices_neq(e_i_desc->arg[1], weq->path_indices1.data[k]));
        }

        if (!ok) {
          ivector_reset(conflict);
        } else {
          for (k = 0; k < weq->path_cond.size; ++k) {
            add_if_not_true_term(conflict, weq->path_cond.data[k]);
          }

          add_if_not_true_term(conflict, _o_yices_eq(e_i_desc->arg[1], e_j_desc->arg[1]));
          add_if_not_true_term(conflict, _o_yices_neq(t_i, t_j));

          ivector_remove_duplicates(conflict);

          if (ctx_trace_enabled(weq->ctx, "weq_graph::array")) {
            ctx_trace_printf(weq->ctx, ">3 Array conflict BEGIN 3\n");
            for (k = 0; k < conflict->size; ++ k) {
              ctx_trace_term(weq->ctx, conflict->data[k]);
            }
            ctx_trace_printf(weq->ctx, ">3 Array conflict END 3\n");
          }

          assert(conflict->size > 1);
          (*weq->stats.array_update2_axioms) ++;

          goto done;
        }
      }
    }
  }

 done:
  return conflict->size == 0;
}

/* Build weak equivalence graph. 
 */
static
void weq_graph_array_build_weak_eq_graph(weq_graph_t* weq,
                                         const ivector_t* array_terms) {
  term_table_t* terms = weq->ctx->terms;
  uint32_t i;

  // clear the fun node map
  // we start from a fresh weak equivalence graph
  weq_graph_clear(weq);

  // build the graph
  for (i = 0; i < array_terms->size; ++ i) {
    term_t t = array_terms->data[i];
    term_kind_t t_kind = term_kind(terms, t);
    assert(is_function_term(terms, t));
    assert(t_kind == UNINTERPRETED_TERM || t_kind == UPDATE_TERM);

    weq_graph_node_t *b = weq_graph_get_node(weq, t);
    if (t_kind == UPDATE_TERM) {
      composite_term_t* t_desc = update_term_desc(terms, t);
      weq_graph_node_t *a = weq_graph_get_node(weq, t_desc->arg[0]);
      term_t idx = t_desc->arg[1];
      weq_graph_add_store(weq, a, b, idx, t);
    }
  }
}

/* Return array update index lemma (when select and update indices are
 * the same
 */
term_t weq_graph_get_array_update_idx_lemma(weq_graph_t* weq, term_t update_term) {
  term_table_t* terms = weq->ctx->terms;
  assert(term_kind(terms, update_term) == UPDATE_TERM);

  composite_term_t* t_desc = update_term_desc(terms, update_term);
  term_t r = app_term(terms, update_term, t_desc->arity - 2, t_desc->arg + 1);
  term_t r_lemma = _o_yices_eq(r, t_desc->arg[t_desc->arity - 1]);

  (*weq->stats.array_update1_axioms) ++;

  return r_lemma;
}

/* Compare terms according to their heuristic score
 */
static
bool weq_graph_array_terms_compare(void *data, term_t t1, term_t t2) {
  plugin_context_t* ctx = (plugin_context_t*) data;

  variable_t v1 = variable_db_get_variable_if_exists(ctx->var_db, t1);
  variable_t v2 = variable_db_get_variable_if_exists(ctx->var_db, t2);

  if (v1 != variable_null && v2 != variable_null) {
    return ctx->cmp_variables(ctx, v1, v2) > 0;
  } else {
    return t1 > t2;
  }
}

static
void copy_uniques(ivector_t *to, ivector_t *from) {
  int_hset_t seen;
  init_int_hset(&seen, 0);

  term_t t = NULL_TERM;
  uint32_t i;
  for (i = 0; i < from->size; ++i) {
    t = from->data[i];
    if (!int_hset_member(&seen, t)) {
      ivector_push(to, t);
      int_hset_add(&seen, t);
    }
  }
}


/* The main method to check array conflicts. The conflict vector will
 * contain conflicting terms if an array conflict is found. It assumes
 * that all terms (assignable) present in the array_terms and
 * select_terms have been assigned values.
 */
void weq_graph_check_array_conflict(weq_graph_t* weq, ivector_t* conflict) {

  if (weq->array_terms.size == 0) {
    return;
  }

  bool ok = true;
  ivector_t array_eq_terms, array_terms, select_terms;

  init_ivector(&array_eq_terms, 0);
  copy_uniques(&array_eq_terms, &weq->array_eq_terms); 

  init_ivector(&array_terms, 0);
  copy_uniques(&array_terms, &weq->array_terms);
  // store array terms according to heuristic score
  int_array_sort2(array_terms.data, array_terms.size, weq->ctx, weq_graph_array_terms_compare);
  
  init_ivector(&select_terms, 0);
  copy_uniques(&select_terms, &weq->select_terms);
  // store select terms according to heuristic score
  int_array_sort2(select_terms.data, select_terms.size, weq->ctx, weq_graph_array_terms_compare);

  //ok = weq_graph_array_idx_check(weq, conflict, &array_terms);

  // check if updates are present.
  // also make sure that relevant array terms have been assinged values
  bool updates_present = false;
  uint32_t i;
  term_table_t* terms = weq->ctx->terms;
  composite_term_t* t_desc = NULL;
  for (i = 0; ok && i < array_terms.size; ++i) {
    if (!eq_graph_term_has_value(weq->eq_graph, array_terms.data[i])) {
       ok = false;
    }
    if (term_kind(terms, array_terms.data[i]) == UPDATE_TERM) {
      updates_present = true;
    }
  }
  for (i = 0; ok && i < select_terms.size; ++i) {
    t_desc = app_term_desc(terms, select_terms.data[i]);
    if (!eq_graph_term_has_value(weq->eq_graph, select_terms.data[i]) ||
	!eq_graph_term_has_value(weq->eq_graph, t_desc->arg[0]) ||
	!eq_graph_term_has_value(weq->eq_graph, t_desc->arg[1])) {
      ok = false;
    }
  }

  (*weq->stats.array_terms) = array_terms.size;
  (*weq->stats.select_terms) = select_terms.size;

  if (updates_present) {
    if (ok) {
      (*weq->stats.array_check_calls) ++;

      if (USE_ARRAY_DIFF) {
	ok = weq_graph_array_ext_diff_check(weq, conflict, &array_eq_terms, NULL);
      }
    }

    if (ok) {
      weq_graph_array_build_weak_eq_graph(weq, &array_terms);
      ok = weq_graph_array_read_over_write_check(weq, conflict, &select_terms); 
    }

    if (ok) {
      if (USE_ARRAY_DIFF) {
        ok = weq_graph_array_ext_diff_check(weq, conflict, NULL, &array_terms);
      } else {
        ok = weq_graph_array_ext_check(weq, conflict, &array_eq_terms, &array_terms, &select_terms);
      }
    }
  }
  
  delete_ivector(&select_terms);
  delete_ivector(&array_terms);
  delete_ivector(&array_eq_terms);
}

