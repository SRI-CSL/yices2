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

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include "mcsat/preprocessor.h"
#include "mcsat/tracing.h"

#include "terms/term_explorer.h"
#include "terms/term_substitution.h"
#include "terms/bvarith64_buffer_terms.h"
#include "terms/bvarith_buffer_terms.h"

#include "model/models.h"
#include "model/model_queries.h"
#include "model/concrete_values.h"

#include "context/context_types.h"

#include "yices.h"
#include "api/yices_api_lock_free.h"

void preprocessor_construct(preprocessor_t* pre, term_table_t* terms, jmp_buf* handler, const mcsat_options_t* options) {
  pre->terms = terms;
  init_term_manager(&pre->tm, terms);
  init_int_hmap(&pre->preprocess_map, 0);
  init_ivector(&pre->preprocess_map_list, 0);
  init_int_hmap(&pre->tuple_blast_map, 0);
  init_ivector(&pre->tuple_blast_data, 0);
  init_ivector(&pre->tuple_blast_list, 0);
  init_ivector(&pre->tuple_blast_atoms, 0);
  init_int_hmap(&pre->type_is_tuple_free_cache, 0);
  init_int_hmap(&pre->type_leaf_count_cache, 0);
  init_int_hmap(&pre->term_has_tuples_cache, 0);
  init_int_hmap(&pre->purification_map, 0);
  init_ivector(&pre->purification_map_list, 0);
  init_ivector(&pre->preprocessing_stack, 0);
  init_int_hmap(&pre->equalities, 0);
  init_ivector(&pre->equalities_list, 0);
  pre->tracer = NULL;
  pre->exception = handler;
  pre->options = options;
  scope_holder_construct(&pre->scope);
}

void preprocessor_set_tracer(preprocessor_t* pre, tracer_t* tracer) {
  pre->tracer = tracer;
}

void preprocessor_destruct(preprocessor_t* pre) {
  delete_int_hmap(&pre->purification_map);
  delete_ivector(&pre->purification_map_list);
  delete_int_hmap(&pre->tuple_blast_map);
  delete_ivector(&pre->tuple_blast_data);
  delete_ivector(&pre->tuple_blast_list);
  delete_ivector(&pre->tuple_blast_atoms);
  delete_int_hmap(&pre->type_is_tuple_free_cache);
  delete_int_hmap(&pre->type_leaf_count_cache);
  delete_int_hmap(&pre->term_has_tuples_cache);
  delete_int_hmap(&pre->preprocess_map);
  delete_ivector(&pre->preprocess_map_list);
  delete_ivector(&pre->preprocessing_stack);
  delete_int_hmap(&pre->equalities);
  delete_ivector(&pre->equalities_list);
  delete_term_manager(&pre->tm);
  scope_holder_destruct(&pre->scope);
}

static
term_t preprocessor_get(preprocessor_t* pre, term_t t) {
  int_hmap_pair_t* find = int_hmap_find(&pre->preprocess_map, t);
  if (find == NULL) {
    return NULL_TERM;
  } else {
    return find->val;
  }
}

static
void preprocessor_set(preprocessor_t* pre, term_t t, term_t t_pre) {
  assert(preprocessor_get(pre, t) == NULL_TERM);
  int_hmap_add(&pre->preprocess_map, t, t_pre);
  ivector_push(&pre->preprocess_map_list, t);
}

static
bool type_is_tuple_free(preprocessor_t* pre, type_t tau) {
  int_hmap_pair_t* rec = int_hmap_find(&pre->type_is_tuple_free_cache, tau);
  if (rec != NULL) {
    return rec->val != 0;
  }

  type_table_t* types = pre->terms->types;
  type_kind_t kind = type_kind(types, tau);
  uint32_t i;
  bool result;
  switch (kind) {
  case BOOL_TYPE:
  case INT_TYPE:
  case REAL_TYPE:
  case BITVECTOR_TYPE:
  case SCALAR_TYPE:
  case UNINTERPRETED_TYPE:
  case FF_TYPE:
    result = true;
    break;
  case TUPLE_TYPE:
    result = false;
    break;
  case FUNCTION_TYPE: {
    function_type_t* fun = function_type_desc(types, tau);
    result = type_is_tuple_free(pre, fun->range);
    for (i = 0; result && i < fun->ndom; ++i) {
      if (!type_is_tuple_free(pre, fun->domain[i])) {
        result = false;
      }
    }
    break;
  }
  default:
    result = false;
    break;
  }

  int_hmap_add(&pre->type_is_tuple_free_cache, tau, result ? 1 : 0);
  return result;
}

static
uint32_t type_leaf_count(preprocessor_t* pre, type_t tau) {
  int_hmap_pair_t* rec = int_hmap_find(&pre->type_leaf_count_cache, tau);
  if (rec != NULL) {
    return (uint32_t) rec->val;
  }

  type_table_t* types = pre->terms->types;
  tuple_type_t* tuple;
  uint32_t i, count;
  switch (type_kind(types, tau)) {
  case TUPLE_TYPE:
    tuple = tuple_type_desc(types, tau);
    count = 0;
    for (i = 0; i < tuple->nelem; ++i) {
      count += type_leaf_count(pre, tuple->elem[i]);
    }
    break;
  case FUNCTION_TYPE:
    count = type_leaf_count(pre, function_type_desc(types, tau)->range);
    break;
  default:
    count = 1;
    break;
  }

  int_hmap_add(&pre->type_leaf_count_cache, tau, (int32_t) count);
  return count;
}

static void function_type_collect_blasted(type_table_t* types, type_t tau, ivector_t* out);

static
void type_collect_flat(type_table_t* types, type_t tau, ivector_t* flat) {
  tuple_type_t* tuple;
  uint32_t i;

  switch (type_kind(types, tau)) {
  case TUPLE_TYPE:
    tuple = tuple_type_desc(types, tau);
    for (i = 0; i < tuple->nelem; ++i) {
      type_collect_flat(types, tuple->elem[i], flat);
    }
    break;

  case FUNCTION_TYPE:
    function_type_collect_blasted(types, tau, flat);
    break;

  default:
    ivector_push(flat, tau);
    break;
  }
}

static
void function_type_collect_blasted(type_table_t* types, type_t tau, ivector_t* out) {
  function_type_t* fun;
  ivector_t dom_flat;
  ivector_t codom_leaf;
  uint32_t i;

  assert(type_kind(types, tau) == FUNCTION_TYPE);
  fun = function_type_desc(types, tau);

  init_ivector(&dom_flat, 0);
  for (i = 0; i < fun->ndom; ++i) {
    type_collect_flat(types, fun->domain[i], &dom_flat);
  }

  init_ivector(&codom_leaf, 0);
  type_collect_flat(types, fun->range, &codom_leaf);
  for (i = 0; i < codom_leaf.size; ++i) {
    type_t ft = function_type(types, codom_leaf.data[i], dom_flat.size, (type_t*) dom_flat.data);
    ivector_push(out, ft);
  }

  delete_ivector(&codom_leaf);
  delete_ivector(&dom_flat);
}

static
void type_collect_blasted_atom_types(type_table_t* types, type_t tau, ivector_t* out) {
  switch (type_kind(types, tau)) {
  case TUPLE_TYPE:
    type_collect_flat(types, tau, out);
    break;
  case FUNCTION_TYPE:
    function_type_collect_blasted(types, tau, out);
    break;
  default:
    ivector_push(out, tau);
    break;
  }
}

static
int_hmap_pair_t* tuple_blast_find(preprocessor_t* pre, term_t t) {
  return int_hmap_find(&pre->tuple_blast_map, t);
}

static
bool tuple_blast_done(preprocessor_t* pre, term_t t) {
  return tuple_blast_find(pre, t) != NULL;
}

static
void tuple_blast_set(preprocessor_t* pre, term_t t, const ivector_t* terms) {
  int_hmap_pair_t* rec = int_hmap_get(&pre->tuple_blast_map, t);
  assert(rec->val < 0);
  rec->val = pre->tuple_blast_data.size;
  ivector_push(&pre->tuple_blast_data, terms->size);
  ivector_add(&pre->tuple_blast_data, terms->data, terms->size);
  ivector_push(&pre->tuple_blast_list, t);
}

static
void tuple_blast_get(preprocessor_t* pre, term_t t, ivector_t* out) {
  int_hmap_pair_t* rec = tuple_blast_find(pre, t);
  assert(rec != NULL);
  uint32_t offset = rec->val;
  uint32_t n = pre->tuple_blast_data.data[offset];
  ivector_reset(out);
  ivector_add(out, pre->tuple_blast_data.data + offset + 1, n);
}

/*
 * Zero-copy read of the blasted leaves for t. Returns pointers directly
 * into tuple_blast_data, so the caller MUST NOT hold the returned pointer
 * across any operation that can grow tuple_blast_data -- most notably a
 * subsequent tuple_blast_term call. Intended for read-only hot paths
 * (ITE / DISTINCT / EQ / tuple_blast_collect_arg) where the current
 * ivector-based tuple_blast_get pays a malloc + memcpy per sub-term.
 */
static
void tuple_blast_peek(preprocessor_t* pre, term_t t, const term_t** data_out, uint32_t* n_out) {
  int_hmap_pair_t* rec = tuple_blast_find(pre, t);
  assert(rec != NULL);
  uint32_t offset = rec->val;
  *n_out = pre->tuple_blast_data.data[offset];
  *data_out = (const term_t*) (pre->tuple_blast_data.data + offset + 1);
}

static
void tuple_blast_term(preprocessor_t* pre, term_t t);
static
void tuple_blast_term_body(preprocessor_t* pre, term_t t);
static composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t);
static term_t mk_composite(preprocessor_t* pre, term_kind_t kind, uint32_t n, term_t* children);

/**
 * Collect the direct sub-terms of t that must be blasted before t can be
 * combined. The set returned here MUST cover every sub-term that
 * tuple_blast_term_body recursively blasts for kind(t); otherwise the
 * iterative driver tuple_blast_term will deadlock (children never blasted)
 * or compute a wrong combine.
 */
static
void tuple_blast_children(preprocessor_t* pre, term_t t, ivector_t* out) {
  if (is_neg_term(t)) {
    ivector_push(out, unsigned_term(t));
    return;
  }

  term_table_t* terms = pre->terms;
  term_kind_t kind = term_kind(terms, t);
  uint32_t i;
  switch (kind) {
  case TUPLE_TERM: {
    composite_term_t* c = tuple_term_desc(terms, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case SELECT_TERM:
    ivector_push(out, select_term_desc(terms, t)->arg);
    break;
  case EQ_TERM: {
    composite_term_t* c = eq_term_desc(terms, t);
    ivector_push(out, c->arg[0]);
    ivector_push(out, c->arg[1]);
    break;
  }
  case DISTINCT_TERM: {
    composite_term_t* c = distinct_term_desc(terms, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case ITE_TERM:
  case ITE_SPECIAL: {
    composite_term_t* c = ite_term_desc(terms, t);
    for (i = 0; i < 3; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case APP_TERM: {
    composite_term_t* c = app_term_desc(terms, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case UPDATE_TERM: {
    composite_term_t* c = update_term_desc(terms, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case OR_TERM: {
    composite_term_t* c = or_term_desc(terms, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case XOR_TERM: {
    composite_term_t* c = xor_term_desc(terms, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* pp = pprod_term_desc(terms, t);
    for (i = 0; i < pp->len; ++i) ivector_push(out, pp->prod[i].var);
    break;
  }
  case ARITH_POLY: {
    polynomial_t* p = poly_term_desc(terms, t);
    for (i = 0; i < p->nterms; ++i) {
      if (p->mono[i].var != const_idx) ivector_push(out, p->mono[i].var);
    }
    break;
  }
  case ARITH_FF_POLY: {
    polynomial_t* p = finitefield_poly_term_desc(terms, t);
    for (i = 0; i < p->nterms; ++i) {
      if (p->mono[i].var != const_idx) ivector_push(out, p->mono[i].var);
    }
    break;
  }
  case BV64_POLY: {
    bvpoly64_t* p = bvpoly64_term_desc(terms, t);
    for (i = 0; i < p->nterms; ++i) {
      if (p->mono[i].var != const_idx) ivector_push(out, p->mono[i].var);
    }
    break;
  }
  case BV_POLY: {
    bvpoly_t* p = bvpoly_term_desc(terms, t);
    for (i = 0; i < p->nterms; ++i) {
      if (p->mono[i].var != const_idx) ivector_push(out, p->mono[i].var);
    }
    break;
  }
  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
  case ARITH_BINEQ_ATOM:
  case ARITH_RDIV:
  case ARITH_IDIV:
  case ARITH_MOD:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    composite_term_t* c = get_composite(terms, kind, t);
    for (i = 0; i < c->arity; ++i) ivector_push(out, c->arg[i]);
    break;
  }
  default:
    /* Atomic kinds (CONSTANT_TERM, UNINTERPRETED_TERM, VARIABLE, BIT_TERM,
     * arithmetic/BV constants, etc.) have no children to blast first. */
    break;
  }
}

/**
 * Memoized: does the DAG rooted at t contain any tuple type?
 * Walks the DAG iteratively so deep DAGs don't blow the C stack. The
 * answer is polarity-insensitive (cached per index_of(t)) and covers
 * t's own type plus the types of every reachable sub-term.
 */
static
bool term_has_tuples_in_subdag(preprocessor_t* pre, term_t t) {
  int32_t t_idx = index_of(t);
  int_hmap_pair_t* rec = int_hmap_find(&pre->term_has_tuples_cache, t_idx);
  if (rec != NULL) {
    return rec->val != 0;
  }

  term_table_t* terms = pre->terms;
  ivector_t stack;
  init_ivector(&stack, 0);
  ivector_push(&stack, t);

  uint64_t safety = 0;
  while (stack.size > 0) {
    /* Hard upper bound: 2 * (term-table size) is a generous loose bound on
     * the number of distinct (term, polarity) revisits we should ever see
     * here. Aborting on overflow is far better than hanging a debug build. */
    assert(++safety < ((uint64_t) 1 << 28));
    (void) safety;

    term_t current = stack.data[stack.size - 1];
    int32_t cur_idx = index_of(current);
    int_hmap_pair_t* crec = int_hmap_find(&pre->term_has_tuples_cache, cur_idx);
    if (crec != NULL) {
      ivector_pop(&stack);
      continue;
    }

    if (!type_is_tuple_free(pre, term_type(terms, current))) {
      int_hmap_add(&pre->term_has_tuples_cache, cur_idx, 1);
      ivector_pop(&stack);
      continue;
    }

    ivector_t children;
    init_ivector(&children, 0);
    tuple_blast_children(pre, current, &children);
    bool any_true = false;
    bool all_done = true;
    for (uint32_t i = 0; i < children.size; ++i) {
      int32_t c_idx = index_of(children.data[i]);
      int_hmap_pair_t* crec2 = int_hmap_find(&pre->term_has_tuples_cache, c_idx);
      if (crec2 == NULL) {
        ivector_push(&stack, children.data[i]);
        all_done = false;
      } else if (crec2->val != 0) {
        any_true = true;
      }
    }
    delete_ivector(&children);
    if (!all_done) continue;

    int_hmap_add(&pre->term_has_tuples_cache, cur_idx, any_true ? 1 : 0);
    ivector_pop(&stack);
  }

  delete_ivector(&stack);

  rec = int_hmap_find(&pre->term_has_tuples_cache, t_idx);
  assert(rec != NULL);
  return rec->val != 0;
}

static
void tuple_blast_collect_arg(preprocessor_t* pre, term_t t, ivector_t* out) {
  const term_t* data;
  uint32_t n;
  tuple_blast_term(pre, t);
  /* Peek is safe here: we do not call tuple_blast_term between the peek
   * and the ivector_add below, so the backing tuple_blast_data cannot be
   * grown (and therefore cannot be reallocated) while `data` is live. */
  tuple_blast_peek(pre, t, &data, &n);
  ivector_add(out, (int32_t*) data, n);
}

static
term_t tuple_blast_eq_vector(term_manager_t* tm, const term_t* a, const term_t* b, uint32_t n) {
  assert(n > 0);
  if (n == 1) {
    return mk_eq(tm, a[0], b[0]);
  } else {
    ivector_t eqs;
    uint32_t i;
    init_ivector(&eqs, n);
    for (i = 0; i < n; ++i) {
      ivector_push(&eqs, mk_eq(tm, a[i], b[i]));
    }
    term_t result = mk_and(tm, eqs.size, eqs.data);
    delete_ivector(&eqs);
    return result;
  }
}

/*
 * Per-term combine. Computes blast(t) assuming the iterative driver
 * tuple_blast_term has already blasted every direct child returned by
 * tuple_blast_children. The recursive tuple_blast_term(pre, child) calls in
 * the body therefore bottom out at the early-return in the driver and do
 * not grow the C stack.
 */
static
void tuple_blast_term_body(preprocessor_t* pre, term_t t) {
  term_table_t* terms = pre->terms;
  type_table_t* types = terms->types;
  term_manager_t* tm = &pre->tm;

  if (tuple_blast_done(pre, t)) {
    return;
  }

  ivector_t result;
  init_ivector(&result, 0);

  if (is_neg_term(t)) {
    term_t c = unsigned_term(t);
    ivector_t c_blast;
    tuple_blast_term(pre, c);
    init_ivector(&c_blast, 0);
    tuple_blast_get(pre, c, &c_blast);
    if (c_blast.size != 1) {
      delete_ivector(&c_blast);
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    ivector_push(&result, opposite_term(c_blast.data[0]));
    delete_ivector(&c_blast);
    tuple_blast_set(pre, t, &result);
    delete_ivector(&result);
    return;
  }

  term_kind_t kind = term_kind(terms, t);
  type_t tau = term_type(terms, t);
  switch (kind) {
  case CONSTANT_TERM:
  case ARITH_CONSTANT:
  case ARITH_FF_CONSTANT:
  case BV64_CONSTANT:
  case BV_CONSTANT:
  case BIT_TERM:
    ivector_push(&result, t);
    break;

  case UNINTERPRETED_TERM:
  case VARIABLE: {
    if (type_is_tuple_free(pre, tau)) {
      ivector_push(&result, t);
    } else {
      ivector_t atom_types;
      uint32_t i;
      init_ivector(&atom_types, 0);
      type_collect_blasted_atom_types(types, tau, &atom_types);
      for (i = 0; i < atom_types.size; ++i) {
        term_t v = new_uninterpreted_term(terms, atom_types.data[i]);
        ivector_push(&result, v);
      }
      ivector_push(&pre->tuple_blast_atoms, t);
      delete_ivector(&atom_types);
    }
    break;
  }

  case TUPLE_TERM: {
    composite_term_t* tuple = tuple_term_desc(terms, t);
    uint32_t i;
    for (i = 0; i < tuple->arity; ++i) {
      tuple_blast_collect_arg(pre, tuple->arg[i], &result);
    }
    break;
  }

  case SELECT_TERM: {
    select_term_t* sel = select_term_desc(terms, t);
    ivector_t arg_blast;
    tuple_type_t* tuple_type;
    uint32_t i, start, len;
    type_t arg_type = term_type(terms, sel->arg);
    if (type_kind(types, arg_type) != TUPLE_TYPE) {
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    tuple_blast_term(pre, sel->arg);
    init_ivector(&arg_blast, 0);
    tuple_blast_get(pre, sel->arg, &arg_blast);
    tuple_type = tuple_type_desc(types, arg_type);
    start = 0;
    for (i = 0; i < sel->idx; ++i) {
      start += type_leaf_count(pre, tuple_type->elem[i]);
    }
    len = type_leaf_count(pre, tuple_type->elem[sel->idx]);
    if (start + len > arg_blast.size) {
      delete_ivector(&arg_blast);
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    ivector_add(&result, arg_blast.data + start, len);
    delete_ivector(&arg_blast);
    break;
  }

  case EQ_TERM: {
    composite_term_t* eq = eq_term_desc(terms, t);
    const term_t *lhs, *rhs;
    uint32_t lhs_n, rhs_n;
    /* Both tuple_blast_term calls precede both peeks; tuple_blast_eq_vector
     * and ivector_push do not grow tuple_blast_data, so the peeked
     * pointers stay live for the duration of this block. */
    tuple_blast_term(pre, eq->arg[0]);
    tuple_blast_term(pre, eq->arg[1]);
    tuple_blast_peek(pre, eq->arg[0], &lhs, &lhs_n);
    tuple_blast_peek(pre, eq->arg[1], &rhs, &rhs_n);
    if (lhs_n != rhs_n || lhs_n == 0) {
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    ivector_push(&result, tuple_blast_eq_vector(tm, lhs, rhs, lhs_n));
    break;
  }

  case DISTINCT_TERM: {
    composite_term_t* d = distinct_term_desc(terms, t);
    ivector_t conjuncts;
    uint32_t i, j;
    init_ivector(&conjuncts, 0);
    for (i = 0; i < d->arity; ++i) {
      for (j = i + 1; j < d->arity; ++j) {
        const term_t *ti_data, *tj_data;
        uint32_t ti_n, tj_n;
        ivector_t disj;
        uint32_t k;
        /* Both tuple_blast_term calls complete before the peeks; after
         * the peeks we only call mk_eq / opposite_term / mk_or and push
         * into local ivectors, none of which grow tuple_blast_data. */
        tuple_blast_term(pre, d->arg[i]);
        tuple_blast_term(pre, d->arg[j]);
        tuple_blast_peek(pre, d->arg[i], &ti_data, &ti_n);
        tuple_blast_peek(pre, d->arg[j], &tj_data, &tj_n);
        if (ti_n != tj_n || ti_n == 0) {
          delete_ivector(&conjuncts);
          delete_ivector(&result);
          longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
        }
        init_ivector(&disj, ti_n);
        for (k = 0; k < ti_n; ++k) {
          ivector_push(&disj, opposite_term(mk_eq(tm, ti_data[k], tj_data[k])));
        }
        ivector_push(&conjuncts, mk_or(tm, disj.size, disj.data));
        delete_ivector(&disj);
      }
    }
    ivector_push(&result, mk_and(tm, conjuncts.size, conjuncts.data));
    delete_ivector(&conjuncts);
    break;
  }

  case ITE_TERM:
  case ITE_SPECIAL: {
    composite_term_t* ite = ite_term_desc(terms, t);
    const term_t *c_data, *t_data, *e_data;
    uint32_t c_n, t_n, e_n;
    uint32_t i;
    /* All three tuple_blast_term calls complete before any peek, so the
     * peeked pointers remain valid for the rest of this block: the only
     * calls after the peeks are term-manager operations (super_type,
     * term_type, mk_ite) plus ivector_push(&result, ...), none of which
     * grow tuple_blast_data. */
    tuple_blast_term(pre, ite->arg[0]);
    tuple_blast_term(pre, ite->arg[1]);
    tuple_blast_term(pre, ite->arg[2]);
    tuple_blast_peek(pre, ite->arg[0], &c_data, &c_n);
    tuple_blast_peek(pre, ite->arg[1], &t_data, &t_n);
    tuple_blast_peek(pre, ite->arg[2], &e_data, &e_n);
    if (c_n != 1 || t_n != e_n || t_n == 0) {
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    for (i = 0; i < t_n; ++i) {
      type_t ty = super_type(types, term_type(terms, t_data[i]), term_type(terms, e_data[i]));
      if (ty == NULL_TYPE) {
        delete_ivector(&result);
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      ivector_push(&result, mk_ite(tm, c_data[0], t_data[i], e_data[i], ty));
    }
    if (result.size == 1 &&
        c_data[0] == ite->arg[0] &&
        t_data[0] == ite->arg[1] &&
        e_data[0] == ite->arg[2]) {
      ivector_reset(&result);
      ivector_push(&result, t);
    }
    break;
  }

  case APP_TERM: {
    composite_term_t* app = app_term_desc(terms, t);
    ivector_t f_blast;
    ivector_t args_flat;
    uint32_t i;
    bool changed;
    tuple_blast_term(pre, app->arg[0]);
    init_ivector(&f_blast, 0);
    tuple_blast_get(pre, app->arg[0], &f_blast);
    init_ivector(&args_flat, 0);
    for (i = 1; i < app->arity; ++i) {
      tuple_blast_collect_arg(pre, app->arg[i], &args_flat);
    }
    changed = f_blast.size != 1 || f_blast.data[0] != app->arg[0] || args_flat.size != app->arity - 1;
    for (i = 1; !changed && i < app->arity; ++i) {
      changed = args_flat.data[i - 1] != app->arg[i];
    }
    if (!changed) {
      ivector_push(&result, t);
      delete_ivector(&args_flat);
      delete_ivector(&f_blast);
      break;
    }
    for (i = 0; i < f_blast.size; ++i) {
      term_t app_i = mk_application(tm, f_blast.data[i], args_flat.size, args_flat.data);
      if (app_i == NULL_TERM) {
        delete_ivector(&args_flat);
        delete_ivector(&f_blast);
        delete_ivector(&result);
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      ivector_push(&result, app_i);
    }
    delete_ivector(&args_flat);
    delete_ivector(&f_blast);
    break;
  }

  case UPDATE_TERM: {
    composite_term_t* upd = update_term_desc(terms, t);
    ivector_t f_blast;
    ivector_t idx_flat;
    ivector_t v_blast;
    uint32_t i;
    bool changed;
    tuple_blast_term(pre, upd->arg[0]);
    init_ivector(&f_blast, 0);
    tuple_blast_get(pre, upd->arg[0], &f_blast);
    init_ivector(&idx_flat, 0);
    for (i = 1; i + 1 < upd->arity; ++i) {
      tuple_blast_collect_arg(pre, upd->arg[i], &idx_flat);
    }
    tuple_blast_term(pre, upd->arg[upd->arity - 1]);
    init_ivector(&v_blast, 0);
    tuple_blast_get(pre, upd->arg[upd->arity - 1], &v_blast);
    if (v_blast.size != 1 && v_blast.size != f_blast.size) {
      delete_ivector(&f_blast);
      delete_ivector(&idx_flat);
      delete_ivector(&v_blast);
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    changed = f_blast.size != 1 || f_blast.data[0] != upd->arg[0] || idx_flat.size != upd->arity - 2 ||
              v_blast.size != 1 || v_blast.data[0] != upd->arg[upd->arity - 1];
    for (i = 1; !changed && i + 1 < upd->arity; ++i) {
      changed = idx_flat.data[i - 1] != upd->arg[i];
    }
    if (!changed) {
      ivector_push(&result, t);
      delete_ivector(&f_blast);
      delete_ivector(&idx_flat);
      delete_ivector(&v_blast);
      break;
    }
    for (i = 0; i < f_blast.size; ++i) {
      term_t vi = v_blast.size == 1 ? v_blast.data[0] : v_blast.data[i];
      term_t upd_i = mk_update(tm, f_blast.data[i], idx_flat.size, idx_flat.data, vi);
      if (upd_i == NULL_TERM) {
        delete_ivector(&f_blast);
        delete_ivector(&idx_flat);
        delete_ivector(&v_blast);
        delete_ivector(&result);
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      ivector_push(&result, upd_i);
    }
    delete_ivector(&f_blast);
    delete_ivector(&idx_flat);
    delete_ivector(&v_blast);
    break;
  }

  case OR_TERM:
  case XOR_TERM: {
    composite_term_t* c = (kind == OR_TERM) ? or_term_desc(terms, t) : xor_term_desc(terms, t);
    ivector_t args;
    uint32_t i;
    init_ivector(&args, c->arity);
    for (i = 0; i < c->arity; ++i) {
      ivector_t child;
      tuple_blast_term(pre, c->arg[i]);
      init_ivector(&child, 0);
      tuple_blast_get(pre, c->arg[i], &child);
      if (child.size != 1) {
        delete_ivector(&child);
        delete_ivector(&args);
        delete_ivector(&result);
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      ivector_push(&args, child.data[0]);
      delete_ivector(&child);
    }
    ivector_push(&result, kind == OR_TERM ? mk_or(tm, args.size, args.data) : mk_xor(tm, args.size, args.data));
    delete_ivector(&args);
    break;
  }

  case POWER_PRODUCT: {
    pprod_t* pp = pprod_term_desc(terms, t);
    term_t args[pp->len];
    uint32_t i;
    bool changed = false;

    for (i = 0; i < pp->len; ++i) {
      ivector_t child;
      tuple_blast_term(pre, pp->prod[i].var);
      init_ivector(&child, 0);
      tuple_blast_get(pre, pp->prod[i].var, &child);
      if (child.size != 1) {
        delete_ivector(&child);
        delete_ivector(&result);
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      args[i] = child.data[0];
      changed |= args[i] != pp->prod[i].var;
      delete_ivector(&child);
    }
    ivector_push(&result, changed ? mk_pprod(tm, pp, pp->len, args) : t);
    break;
  }

  case ARITH_POLY: {
    polynomial_t* p = poly_term_desc(terms, t);
    term_t args[p->nterms];
    uint32_t i;
    bool changed = false;

    for (i = 0; i < p->nterms; ++i) {
      term_t x = p->mono[i].var;
      if (x == const_idx) {
        args[i] = const_idx;
      } else {
        ivector_t child;
        tuple_blast_term(pre, x);
        init_ivector(&child, 0);
        tuple_blast_get(pre, x, &child);
        if (child.size != 1) {
          delete_ivector(&child);
          delete_ivector(&result);
          longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
        }
        args[i] = child.data[0];
        changed |= args[i] != x;
        delete_ivector(&child);
      }
    }
    ivector_push(&result, changed ? mk_arith_poly(tm, p, p->nterms, args) : t);
    break;
  }

  case ARITH_FF_POLY: {
    polynomial_t* p = finitefield_poly_term_desc(terms, t);
    const rational_t* mod = finitefield_term_order(terms, t);
    term_t args[p->nterms];
    uint32_t i;
    bool changed = false;

    for (i = 0; i < p->nterms; ++i) {
      term_t x = p->mono[i].var;
      if (x == const_idx) {
        args[i] = const_idx;
      } else {
        ivector_t child;
        tuple_blast_term(pre, x);
        init_ivector(&child, 0);
        tuple_blast_get(pre, x, &child);
        if (child.size != 1) {
          delete_ivector(&child);
          delete_ivector(&result);
          longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
        }
        args[i] = child.data[0];
        changed |= args[i] != x;
        delete_ivector(&child);
      }
    }
    ivector_push(&result, changed ? mk_arith_ff_poly(tm, p, p->nterms, args, mod) : t);
    break;
  }

  case BV64_POLY: {
    bvpoly64_t* p = bvpoly64_term_desc(terms, t);
    term_t args[p->nterms];
    uint32_t i;
    bool changed = false;

    for (i = 0; i < p->nterms; ++i) {
      term_t x = p->mono[i].var;
      if (x == const_idx) {
        args[i] = const_idx;
      } else {
        ivector_t child;
        tuple_blast_term(pre, x);
        init_ivector(&child, 0);
        tuple_blast_get(pre, x, &child);
        if (child.size != 1) {
          delete_ivector(&child);
          delete_ivector(&result);
          longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
        }
        args[i] = child.data[0];
        changed |= args[i] != x;
        delete_ivector(&child);
      }
    }
    ivector_push(&result, changed ? mk_bvarith64_poly(tm, p, p->nterms, args) : t);
    break;
  }

  case BV_POLY: {
    bvpoly_t* p = bvpoly_term_desc(terms, t);
    term_t args[p->nterms];
    uint32_t i;
    bool changed = false;

    for (i = 0; i < p->nterms; ++i) {
      term_t x = p->mono[i].var;
      if (x == const_idx) {
        args[i] = const_idx;
      } else {
        ivector_t child;
        tuple_blast_term(pre, x);
        init_ivector(&child, 0);
        tuple_blast_get(pre, x, &child);
        if (child.size != 1) {
          delete_ivector(&child);
          delete_ivector(&result);
          longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
        }
        args[i] = child.data[0];
        changed |= args[i] != x;
        delete_ivector(&child);
      }
    }
    ivector_push(&result, changed ? mk_bvarith_poly(tm, p, p->nterms, args) : t);
    break;
  }

  case ARITH_EQ_ATOM:
  case ARITH_GE_ATOM:
  case ARITH_BINEQ_ATOM:
  case ARITH_RDIV:
  case ARITH_IDIV:
  case ARITH_MOD:
  case BV_ARRAY:
  case BV_DIV:
  case BV_REM:
  case BV_SDIV:
  case BV_SREM:
  case BV_SMOD:
  case BV_SHL:
  case BV_LSHR:
  case BV_ASHR:
  case BV_EQ_ATOM:
  case BV_GE_ATOM:
  case BV_SGE_ATOM: {
    composite_term_t* c = get_composite(terms, kind, t);
    term_t args[c->arity];
    uint32_t i;
    bool changed = false;

    for (i = 0; i < c->arity; ++i) {
      ivector_t child;
      tuple_blast_term(pre, c->arg[i]);
      init_ivector(&child, 0);
      tuple_blast_get(pre, c->arg[i], &child);
      if (child.size != 1) {
        delete_ivector(&child);
        delete_ivector(&result);
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }
      args[i] = child.data[0];
      changed |= args[i] != c->arg[i];
      delete_ivector(&child);
    }

    term_t rebuilt = changed ? mk_composite(pre, kind, c->arity, args) : t;
    if (rebuilt == NULL_TERM) {
      delete_ivector(&result);
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }
    ivector_push(&result, rebuilt);
    break;
  }

  default:
    ivector_push(&result, t);
    break;
  }

  tuple_blast_set(pre, t, &result);
  delete_ivector(&result);
}

/*
 * Iterative bottom-up driver for tuple-blasting.
 *  - C stack depth is O(1) regardless of input DAG depth (M4).
 *  - Sub-DAGs that contain no tuple type anywhere are identity-blasted in
 *    one step without descending into them, using the memoized
 *    term_has_tuples_in_subdag (M3).
 *  - For each not-yet-blasted term on the work stack we either (a) push
 *    its un-blasted children, or (b) all children are blasted and we run
 *    tuple_blast_term_body once. Children come from tuple_blast_children
 *    which mirrors exactly the recursive descent in tuple_blast_term_body.
 */
static
void tuple_blast_term(preprocessor_t* pre, term_t t) {
  if (tuple_blast_done(pre, t)) {
    return;
  }

  if (!term_has_tuples_in_subdag(pre, t)) {
    ivector_t result;
    init_ivector(&result, 0);
    ivector_push(&result, t);
    tuple_blast_set(pre, t, &result);
    delete_ivector(&result);
    return;
  }

  ivector_t stack;
  init_ivector(&stack, 0);
  ivector_push(&stack, t);

  uint64_t safety = 0;
  while (stack.size > 0) {
    /* Defensive bound. Real workloads visit each term O(1) times; 2^28
     * iterations is far more than any reachable DAG should ever need. */
    assert(++safety < ((uint64_t) 1 << 28));
    (void) safety;

    term_t current = stack.data[stack.size - 1];

    if (tuple_blast_done(pre, current)) {
      ivector_pop(&stack);
      continue;
    }

    if (!term_has_tuples_in_subdag(pre, current)) {
      ivector_t result;
      init_ivector(&result, 0);
      ivector_push(&result, current);
      tuple_blast_set(pre, current, &result);
      delete_ivector(&result);
      ivector_pop(&stack);
      continue;
    }

    ivector_t children;
    init_ivector(&children, 0);
    tuple_blast_children(pre, current, &children);
    bool all_done = true;
    for (uint32_t i = 0; i < children.size; ++i) {
      if (!tuple_blast_done(pre, children.data[i])) {
        ivector_push(&stack, children.data[i]);
        all_done = false;
      }
    }
    delete_ivector(&children);
    if (!all_done) continue;

    tuple_blast_term_body(pre, current);
    ivector_pop(&stack);
  }

  delete_ivector(&stack);
}

typedef struct composite_term1_s {
  uint32_t arity;  // number of subterms
  term_t arg[1];  // real size = arity
} composite_term1_t;

static
composite_term1_t composite_for_noncomposite;

static
composite_term_t* get_composite(term_table_t* terms, term_kind_t kind, term_t t) {
  assert(term_is_composite(terms, t));
  assert(term_kind(terms, t) == kind);
  assert(is_pos_term(t));

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    return ite_term_desc(terms, t);
  case EQ_TERM:            // equality
    return eq_term_desc(terms, t);
  case OR_TERM:            // n-ary OR
    return or_term_desc(terms, t);
  case XOR_TERM:           // n-ary XOR
    return xor_term_desc(terms, t);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    return arith_bineq_atom_desc(terms, t);
  case ARITH_EQ_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_eq_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case ARITH_GE_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_ge_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case ARITH_FF_BINEQ_ATOM:
    return arith_ff_bineq_atom_desc(terms, t);
  case ARITH_FF_EQ_ATOM: {
    composite_for_noncomposite.arity = 1;
    composite_for_noncomposite.arg[0] = arith_ff_eq_arg(terms, t);
    return (composite_term_t*)&composite_for_noncomposite;
  }
  case APP_TERM:           // application of an uninterpreted function
    return app_term_desc(terms, t);
  case ARITH_RDIV:          // division: (/ x y)
    return arith_rdiv_term_desc(terms, t);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    return arith_idiv_term_desc(terms, t);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    return arith_mod_term_desc(terms, t);
  case UPDATE_TERM:
    return update_term_desc(terms, t);
  case DISTINCT_TERM:
    return distinct_term_desc(terms, t);
  case BV_ARRAY:
    return bvarray_term_desc(terms, t);
  case BV_DIV:
    return bvdiv_term_desc(terms, t);
  case BV_REM:
    return bvrem_term_desc(terms, t);
  case BV_SDIV:
    return bvsdiv_term_desc(terms, t);
  case BV_SREM:
    return bvsrem_term_desc(terms, t);
  case BV_SMOD:
    return bvsmod_term_desc(terms, t);
  case BV_SHL:
    return bvshl_term_desc(terms, t);
  case BV_LSHR:
    return bvlshr_term_desc(terms, t);
  case BV_ASHR:
    return bvashr_term_desc(terms, t);
  case BV_EQ_ATOM:
    return bveq_atom_desc(terms, t);
  case BV_GE_ATOM:
    return bvge_atom_desc(terms, t);
  case BV_SGE_ATOM:
    return bvsge_atom_desc(terms, t);
  default:
    assert(false);
    return NULL;
  }
}

static bool type_needs_function_diseq_guard(type_table_t* types, type_t tau) {
  uint32_t i, n;

  switch (type_kind(types, tau)) {
  case FUNCTION_TYPE:
    if (type_has_finite_domain(types, tau) ||
        is_unit_type(types, function_type_range(types, tau))) {
      return true;
    }

    n = function_type_arity(types, tau);
    for (i = 0; i < n; ++ i) {
      if (type_needs_function_diseq_guard(types, function_type_domain(types, tau, i))) {
        return true;
      }
    }

    return type_needs_function_diseq_guard(types, function_type_range(types, tau));

  case TUPLE_TYPE:
    n = tuple_type_arity(types, tau);
    for (i = 0; i < n; ++ i) {
      if (type_needs_function_diseq_guard(types, tuple_type_component(types, tau, i))) {
        return true;
      }
    }
    return false;

  case INSTANCE_TYPE:
    n = instance_type_arity(types, tau);
    for (i = 0; i < n; ++ i) {
      if (type_needs_function_diseq_guard(types, instance_type_param(types, tau, i))) {
        return true;
      }
    }
    return false;

  default:
    return false;
  }
}

static bool term_needs_function_diseq_guard(term_table_t* terms, term_t t) {
  return type_needs_function_diseq_guard(terms->types, term_type(terms, t));
}

static
term_t mk_composite(preprocessor_t* pre, term_kind_t kind, uint32_t n, term_t* children) {
  term_manager_t* tm = &pre->tm;
  term_table_t* terms = pre->terms;

  switch (kind) {
  case ITE_TERM:           // if-then-else
  case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
  {
    assert(n == 3);
    term_t type = super_type(pre->terms->types, term_type(terms, children[1]), term_type(terms, children[2]));
    assert(type != NULL_TYPE);
    return mk_ite(tm, children[0], children[1], children[2], type);
  }
  case EQ_TERM:            // equality
    assert(n == 2);
    return mk_eq(tm, children[0], children[1]);
  case OR_TERM:            // n-ary OR
    assert(n > 1);
    return mk_or(tm, n, children);
  case XOR_TERM:           // n-ary XOR
    return mk_xor(tm, n, children);
  case ARITH_EQ_ATOM:
    assert(n == 1);
    return mk_arith_eq(tm, children[0], zero_term);
  case ARITH_GE_ATOM:
    assert(n == 1);
    return mk_arith_geq(tm, children[0], zero_term);
  case ARITH_BINEQ_ATOM:   // equality: (t1 == t2)  (between two arithmetic terms)
    assert(n == 2);
    return mk_arith_eq(tm, children[0], children[1]);
  case APP_TERM:           // application of an uninterpreted function
    assert(n > 1);
    return mk_application(tm, children[0], n-1, children + 1);
  case ARITH_RDIV:
    assert(n == 2);
    return mk_arith_rdiv(tm, children[0], children[1]);
  case ARITH_IDIV:          // division: (div x y) as defined in SMT-LIB 2
    assert(n == 2);
    return mk_arith_idiv(tm, children[0], children[1]);
  case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    assert(n == 2);
    return mk_arith_mod(tm, children[0], children[1]);
  case UPDATE_TERM:
    assert(n > 2);
    return mk_update(tm, children[0], n-2, children + 1, children[n-1]);
  case BV_ARRAY:
    assert(n >= 1);
    return mk_bvarray(tm, n, children);
  case BV_DIV:
    assert(n == 2);
    return mk_bvdiv(tm, children[0], children[1]);
  case BV_REM:
    assert(n == 2);
    return mk_bvrem(tm, children[0], children[1]);
  case BV_SDIV:
    assert(n == 2);
    return mk_bvsdiv(tm, children[0], children[1]);
  case BV_SREM:
    assert(n == 2);
    return mk_bvsrem(tm, children[0], children[1]);
  case BV_SMOD:
    assert(n == 2);
    return mk_bvsmod(tm, children[0], children[1]);
  case BV_SHL:
    assert(n == 2);
    return mk_bvshl(tm, children[0], children[1]);
  case BV_LSHR:
    assert(n == 2);
    return mk_bvlshr(tm, children[0], children[1]);
  case BV_ASHR:
    assert(n == 2);
    return mk_bvashr(tm, children[0], children[1]);
  case BV_EQ_ATOM:
    assert(n == 2);
    return mk_bveq(tm, children[0], children[1]);
  case BV_GE_ATOM:
    assert(n == 2);
    return mk_bvge(tm, children[0], children[1]);
  case BV_SGE_ATOM:
    assert(n == 2);
    return mk_bvsge(tm, children[0], children[1]);
  default:
    assert(false);
    return NULL_TERM;
  }
}

/**
 * Returns purified version of t if we should purify t as an argument of a function.
 * Any new equalities are added to output.
 */
static inline
term_t preprocessor_purify(preprocessor_t* pre, term_t t, ivector_t* out) {

  term_table_t* terms = pre->terms;

  // Negated terms must be purified
  if (is_pos_term(t)) {
    // We don't purify variables
    switch (term_kind(terms, t)) {
    case UNINTERPRETED_TERM:
      // Variables are already pure
      return t;
    case CONSTANT_TERM:
      return t;
    case ARITH_CONSTANT:
    case ARITH_FF_CONSTANT:
    case BV64_CONSTANT:
    case BV_CONSTANT:
      // Constants are also pure (except for false)
      return t;
    case APP_TERM:
      // Uninterpreted functions are also already purified
      return t;
    case UPDATE_TERM:
      return t;
    default:
      break;
    }
  }

  // Everything else gets purified. Check if in the cache
  int_hmap_pair_t* find = int_hmap_find(&pre->purification_map, t);
  if (find != NULL) {
    return find->val;
  } else {
    // Make the variable
    type_t t_type = term_type(terms, t);
    term_t x = new_uninterpreted_term(terms, t_type);
    // Remember for later
    int_hmap_add(&pre->purification_map, t, x);
    ivector_push(&pre->purification_map_list, t);
    // Also add the variable to the pre-processor
    preprocessor_set(pre, x, x);
    // Add equality to output
    term_t eq = mk_eq(&pre->tm, x, t);
    ivector_push(out, eq);

    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      mcsat_trace_printf(pre->tracer, "adding lemma = ");
      trace_term_ln(pre->tracer, terms, eq);
    }

    // Return the purified version
    return x;
  }
}

static inline
term_t mk_bvneg(term_manager_t* tm, term_t t) {
  term_table_t* terms = tm->terms;
  if (term_bitsize(terms,t) <= 64) {
    bvarith64_buffer_t *buffer = term_manager_get_bvarith64_buffer(tm);
    bvarith64_buffer_set_term(buffer, terms, t);
    bvarith64_buffer_negate(buffer);
    return mk_bvarith64_term(tm, buffer);
  } else {
    bvarith_buffer_t *buffer = term_manager_get_bvarith_buffer(tm);
    bvarith_buffer_set_term(buffer, terms, t);
    bvarith_buffer_negate(buffer);
    return mk_bvarith_term(tm, buffer);
  }
}

// Mark equality eq: (var = t) for solving
static
void preprocessor_mark_eq(preprocessor_t* pre, term_t eq, term_t var) {
  assert(is_pos_term(eq));
  assert(is_pos_term(var));
  assert(term_kind(pre->terms, var) == UNINTERPRETED_TERM);

  // Mark the equality
  int_hmap_pair_t* find = int_hmap_get(&pre->equalities, eq);
  assert(find->val == -1);
  find->val = var;
  ivector_push(&pre->equalities_list, eq);
}

static
term_t preprocessor_get_eq_solved_var(const preprocessor_t* pre, term_t eq) {
  assert(is_pos_term(eq));
  int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &pre->equalities, eq);
  if (find != NULL) {
    return find->val;
  } else {
    return NULL_TERM;
  }
}

term_t preprocessor_apply(preprocessor_t* pre, term_t t, ivector_t* out, bool is_assertion) {

  term_table_t* terms = pre->terms;
  term_manager_t* tm = &pre->tm;

  uint32_t i, j, n;
  ivector_t t_blast;

  tuple_blast_term(pre, t);
  init_ivector(&t_blast, 0);
  tuple_blast_get(pre, t, &t_blast);
  if (t_blast.size != 1) {
    delete_ivector(&t_blast);
    longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
  }
  t = t_blast.data[0];
  delete_ivector(&t_blast);

  // Check if already preprocessed;
  term_t t_pre = preprocessor_get(pre, t);
  if (t_pre != NULL_TERM) {
    return t_pre;
  }

// Note: negative affect on general performance due to solved/substituted
//       terms being to complex for explainers.
//
//  // First, if the assertion is a conjunction, just expand
//  if (is_assertion && is_neg_term(t) && term_kind(terms, t) == OR_TERM) {
//    // !(or t1 ... tn) -> !t1 && ... && !tn
//    composite_term_t* t_desc = composite_term_desc(terms, t);
//    for (i = 0; i < t_desc->arity; ++ i) {
//      ivector_push(out, opposite_term(t_desc->arg[i]));
//    }
//    return true_term;
//  }
//
  // Start
  ivector_t* pre_stack = &pre->preprocessing_stack;
  ivector_reset(pre_stack);
  ivector_push(pre_stack, t);

  // Preprocess
  while (pre_stack->size) {
    // Current term
    term_t current = ivector_last(pre_stack);

    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      mcsat_trace_printf(pre->tracer, "current = ");
      trace_term_ln(pre->tracer, terms, current);
    }

    // If preprocessed already, done
    term_t current_pre = preprocessor_get(pre, current);
    if (current_pre != NULL_TERM) {
      ivector_pop(pre_stack);
      continue;
    }

    // Negation
    if (is_neg_term(current)) {
      term_t child = unsigned_term(current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre == NULL_TERM) {
        ivector_push(pre_stack, child);
        continue;
      } else {
        ivector_pop(pre_stack);
        current_pre = opposite_term(child_pre);
        preprocessor_set(pre, current, current_pre);
        continue;
      }
    }

    // Check for supported types
    type_kind_t type = term_type_kind(terms, current);
    switch (type) {
    case BOOL_TYPE:
    case INT_TYPE:
    case REAL_TYPE:
    case FF_TYPE:
    case UNINTERPRETED_TYPE:
    case FUNCTION_TYPE:
    case BITVECTOR_TYPE:
    case SCALAR_TYPE:
      break;
    default:
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
    }

    // Kind of term
    term_kind_t current_kind = term_kind(terms, current);

    switch(current_kind) {
    case CONSTANT_TERM:    // constant of uninterpreted/scalar/boolean types
    case BV64_CONSTANT:    // compact bitvector constant (64 bits at most)
    case BV_CONSTANT:      // generic bitvector constant (more than 64 bits)
    case ARITH_CONSTANT:   // rational constant
    case ARITH_FF_CONSTANT:   // finite field constant
      current_pre = current;
      break;

    case UNINTERPRETED_TERM:  // (i.e., global variables, can't be bound).
      current_pre = current;
      // Unless we want special slicing
      if (type == BITVECTOR_TYPE) {
        if (pre->options->bv_var_size > 0) {
          uint32_t size = term_bitsize(terms, current);
          uint32_t var_size = pre->options->bv_var_size;
          if (size > var_size) {
            uint32_t n_vars = (size - 1) / var_size + 1;
            term_t vars[n_vars];
            for (i = n_vars - 1; size > 0; i--) {
              if (size >= var_size) {
                vars[i] = new_uninterpreted_term(terms, bv_type(terms->types, var_size));
                size -= var_size;
              } else {
                vars[i] = new_uninterpreted_term(terms, bv_type(terms->types, size));
                size = 0;
              }
            }
            current_pre = _o_yices_bvconcat(n_vars, vars);
            term_t eq = _o_yices_eq(current, current_pre);
            preprocessor_mark_eq(pre, eq, current);
          }
        }
      }
      break;

    case ITE_TERM:           // if-then-else
    case ITE_SPECIAL:        // special if-then-else term (NEW: EXPERIMENTAL)
    case EQ_TERM:            // equality
    case OR_TERM:            // n-ary OR
    case XOR_TERM:           // n-ary XOR
    case ARITH_EQ_ATOM:      // equality (t == 0)
    case ARITH_BINEQ_ATOM:   // equality (t1 == t2)  (between two arithmetic terms)
    case ARITH_GE_ATOM:      // inequality (t >= 0)
    case ARITH_FF_EQ_ATOM:   // finite field equality (t == 0)
    case ARITH_FF_BINEQ_ATOM: // finite field equality (t1 == t2)  (between two arithmetic terms)
    case BV_DIV:
    case BV_REM:
    case BV_SMOD:
    case BV_SHL:
    case BV_LSHR:
    case BV_ASHR:
    case BV_EQ_ATOM:
    case BV_GE_ATOM:
    case BV_SGE_ATOM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      // MCSAT does not yet enforce all extensionality/cardinality constraints
      // for function-sort disequalities. Reject equality atoms whose type needs
      // that monitoring; the Boolean abstraction may assert them either way.
      if (current_kind == EQ_TERM && term_needs_function_diseq_guard(terms, desc->arg[0])) {
        longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      }

      // Is this a top-level equality assertion
      bool is_equality =
          current_kind == EQ_TERM ||
          current_kind == BV_EQ_ATOM ||
          current_kind == ARITH_EQ_ATOM ||
          current_kind == ARITH_BINEQ_ATOM ||
          current_kind == ARITH_FF_EQ_ATOM ||
          current_kind == ARITH_FF_BINEQ_ATOM;
      // don't rewrite if the equality is between Boolean terms
      bool is_boolean = is_boolean_type(term_type(pre->terms, desc->arg[0]));

      term_t eq_solve_var = NULL_TERM;
      if (is_assertion && is_equality && !is_boolean) {
	bool is_lhs_rhs_mixed = desc->arity > 1 &&
	  term_type_kind(pre->terms, desc->arg[0]) != term_type_kind(pre->terms, desc->arg[1]);
	// don't rewrite if equality is between mixed terms, e.g. between int and real terms
	if (!is_lhs_rhs_mixed && current == t) {
          eq_solve_var = preprocessor_get_eq_solved_var(pre, t);
          if (eq_solve_var == NULL_TERM) {
            term_t lhs = desc->arg[0];
            term_kind_t lhs_kind = term_kind(terms, lhs);
            // If lhs/rhs is a first-time seen variable, we can solve it
            bool lhs_is_var = lhs_kind == UNINTERPRETED_TERM && is_pos_term(lhs);
            if (lhs_is_var && preprocessor_get(pre, lhs) == NULL_TERM) {
              // First time variable, let's solve
              preprocessor_mark_eq(pre, t, lhs);
              eq_solve_var = lhs;
            } else if (desc->arity > 1) {
              term_t rhs = desc->arg[1];
              term_kind_t rhs_kind = term_kind(terms, rhs);
              bool rhs_is_var = rhs_kind == UNINTERPRETED_TERM && is_pos_term(rhs);
              if (rhs_is_var && preprocessor_get(pre, rhs) == NULL_TERM) {
                // First time variable, let's solve
                preprocessor_mark_eq(pre, t, rhs);
                eq_solve_var = rhs;
              }
            }
          } else {
            // Check that we it's not there already
            if (preprocessor_get(pre, eq_solve_var) != NULL_TERM) {
              eq_solve_var = NULL_TERM;
            }
          }
        }
      }

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        if (child != eq_solve_var) {
          term_t child_pre = preprocessor_get(pre, child);
          if (child_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, child);
          } else if (child_pre != child) {
            children_same = false;
          }
          if (children_done) {
            ivector_push(&children, child_pre);
          }
        }
      }

      if (eq_solve_var != NULL_TERM) {
        // Check again to make sure we don't have something like x = x + 1
        if (preprocessor_get(pre, eq_solve_var) != NULL_TERM) {
          // Do it again
          children_done = false;
        }
      }

      if (children_done) {
        if (eq_solve_var != NULL_TERM) {
          term_t eq_solve_term = zero_term;
          if (children.size > 0) {
            eq_solve_term = children.data[0];
          }
          preprocessor_set(pre, eq_solve_var, eq_solve_term);
          current_pre = true_term;
        } else {
          if (children_same) {
            current_pre = current;
          } else {
            current_pre = mk_composite(pre, current_kind, n, children.data);
          }
        }
      }

      delete_ivector(&children);

      break;
    }

    case BV_ARRAY:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);
        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, child);
        } else {
          if (is_arithmetic_literal(terms, child_pre) || child_pre == false_term) {
            // purify if arithmetic literal, i.e. a = 0 where a is of integer type
            child_pre = preprocessor_purify(pre, child_pre, out);
          }
          if (child_pre != child) {
            children_same = false;
          }
        }
        if (children_done) {
          ivector_push(&children, child_pre);
        }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_composite(pre, current_kind, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_ABS:
    {
      term_t arg = arith_abs_arg(terms, current);
      term_t arg_pre = preprocessor_get(pre, arg);
      if (arg_pre == NULL_TERM) {
        ivector_push(pre_stack, arg);
      } else {
        type_t arg_pre_type = term_type(pre->terms, arg_pre);
        term_t arg_pre_is_positive = mk_arith_term_geq0(&pre->tm, arg_pre);
        term_t arg_negative = _o_yices_neg(arg_pre);
        current_pre = mk_ite(&pre->tm, arg_pre_is_positive, arg_pre, arg_negative, arg_pre_type);
      }
      break;
    }

    case BV_SDIV:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      assert(desc->arity == 2);
      term_t s = desc->arg[0];
      term_t s_pre = preprocessor_get(pre, s);
      if (s_pre == NULL_TERM) {
        ivector_push(pre_stack, s);
      }
      term_t t = desc->arg[1];
      term_t t_pre = preprocessor_get(pre, t);
      if (t_pre == NULL_TERM) {
        ivector_push(pre_stack, t);
      }
      if (s_pre != NULL_TERM && t_pre != NULL_TERM) {
        type_t tau = term_type(terms, s_pre);
        uint32_t n = term_bitsize(terms, s_pre);
        term_t msb_s = mk_bitextract(tm, s_pre, n-1);
        term_t msb_t = mk_bitextract(tm, t_pre, n-1);
        // if (msb_s) {
        //   if (msb_t) {
        //     t1: udiv(-s, -t)
        //   } else {
        //     t2: -udiv(-s, t)
        //   }
        // } else {
        //   if (msb_t) {
        //     t3: -udiv(s, -t)
        //   } else {
        //     t4: udiv(s, t)
        //   }
        // }
        term_t neg_s = mk_bvneg(tm, s_pre);
        term_t neg_t = mk_bvneg(tm, t_pre);

        term_t t1 = mk_bvdiv(tm, neg_s, neg_t);
        term_t t2 = mk_bvdiv(tm, neg_s, t_pre);
        t2 = mk_bvneg(&pre->tm, t2);
        term_t t3 = mk_bvdiv(tm, s_pre, neg_t);
        t3 = mk_bvneg(&pre->tm, t3);
        term_t t4 = mk_bvdiv(tm, s_pre, t_pre);

        term_t b1 = mk_ite(tm, msb_t, t1, t2, tau);
        term_t b2 = mk_ite(tm, msb_t, t3, t4, tau);

        current_pre = mk_ite(tm, msb_s, b1, b2, tau);
      }
      break;
    }
    case BV_SREM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      assert(desc->arity == 2);
      term_t s = desc->arg[0];
      term_t s_pre = preprocessor_get(pre, s);
      if (s_pre == NULL_TERM) {
        ivector_push(pre_stack, s);
      }
      term_t t = desc->arg[1];
      term_t t_pre = preprocessor_get(pre, t);
      if (t_pre == NULL_TERM) {
        ivector_push(pre_stack, t);
      }
      if (s_pre != NULL_TERM && t_pre != NULL_TERM) {
        type_t tau = term_type(terms, s_pre);
        uint32_t n = term_bitsize(terms, s_pre);
        term_t msb_s = mk_bitextract(tm, s_pre, n-1);
        term_t msb_t = mk_bitextract(tm, t_pre, n-1);
        // if (msb_s) {
        //   if (msb_t) {
        //     t1: -urem(-s, -t)
        //   } else {
        //     t2: -urem(-s, t)
        //   }
        // } else {
        //   if (msb_t) {
        //     t3: -urem(s, -t)
        //   } else {
        //     t4: urem(s, t)
        //   }
        // }
        term_t neg_s = mk_bvneg(tm, s_pre);
        term_t neg_t = mk_bvneg(tm, t_pre);

        term_t t1 = mk_bvrem(tm, neg_s, neg_t);
        t1 = mk_bvneg(tm, t1);
        term_t t2 = mk_bvrem(tm, neg_s, t_pre);
        t2 = mk_bvneg(tm, t2);
        term_t t3 = mk_bvrem(tm, s_pre, neg_t);
        term_t t4 = mk_bvrem(tm, s_pre, t_pre);

        term_t b1 = mk_ite(tm, msb_t, t1, t2, tau);
        term_t b2 = mk_ite(tm, msb_t, t3, t4, tau);

        current_pre = mk_ite(tm, msb_s, b1, b2, tau);
      }
      break;
    }
    case BIT_TERM: // bit-select current = child[i]
    {
      uint32_t index = bit_term_index(terms, current);
      term_t arg = bit_term_arg(terms, current);
      term_t arg_pre = preprocessor_get(pre, arg);
      if (arg_pre == NULL_TERM) {
        ivector_push(pre_stack, arg);
      } else {
        if (arg_pre == arg) {
          current_pre = current;
        } else {
          if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
            mcsat_trace_printf(pre->tracer, "arg_pre = ");
            trace_term_ln(pre->tracer, terms, arg_pre);
          }
          // For simplification purposes use API
          current_pre = _o_yices_bitextract(arg_pre, index);
          assert(current_pre != NULL_TERM);
        }
      }
      break;
    }
    case BV_POLY:  // polynomial with generic bitvector coefficients
    {
      bvpoly_t* p = bvpoly_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_bvarith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }
    case BV64_POLY: // polynomial with 64bit coefficients
    {
      bvpoly64_t* p = bvpoly64_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_bvarith64_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case POWER_PRODUCT:    // power products: (t1^d1 * ... * t_n^d_n)
    {
      pprod_t* pp = pprod_term_desc(terms, current);
      bool children_done = true;
      bool children_same = true;

      n = pp->len;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = pp->prod[i].var;
        term_t x_pre = preprocessor_get(pre, x);

        if (x_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, x);
        } else if (x_pre != x) {
          children_same = false;
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          // NOTE: it doens't change pp, it just uses it as a frame
          current_pre = mk_pprod(tm, pp, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_POLY:       // polynomial with rational coefficients
    {
      polynomial_t* p = poly_term_desc(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_arith_poly(tm, p, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_FF_POLY:    // polynomial with finite field coefficients
    {
      polynomial_t* p = finitefield_poly_term_desc(terms, current);
      const rational_t *mod = finitefield_term_order(terms, current);

      bool children_done = true;
      bool children_same = true;

      n = p->nterms;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t x = p->mono[i].var;
        term_t x_pre = (x == const_idx ? const_idx : preprocessor_get(pre, x));

        if (x_pre != const_idx) {
          if (x_pre == NULL_TERM) {
            children_done = false;
            ivector_push(pre_stack, x);
          } else if (x_pre != x) {
            children_same = false;
          }
        }

        if (children_done) { ivector_push(&children, x_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_arith_ff_poly(tm, p, n, children.data, mod);
        }
      }

      delete_ivector(&children);

      break;
    }

    // FOLLOWING ARE UNINTEPRETED, SO WE PURIFY THE ARGUMENTS

    case APP_TERM:           // application of an uninterpreted function
    case ARITH_RDIV:         // regular division (/ x y)
    case ARITH_IDIV:         // division: (div x y) as defined in SMT-LIB 2
    case ARITH_MOD:          // remainder: (mod x y) is y - x * (div x y)
    case UPDATE_TERM:        // update array
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);
      bool children_done = true;
      bool children_same = true;

      n = desc->arity;

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, child);
        } else {
          // Purify if needed
          child_pre = preprocessor_purify(pre, child_pre, out);
          // If interpreted terms, we need to purify non-variables
          if (child_pre != child) { children_same = false; }
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        if (children_same) {
          current_pre = current;
        } else {
          current_pre = mk_composite(pre, current_kind, n, children.data);
        }
      }

      delete_ivector(&children);

      break;
    }

    case ARITH_IS_INT_ATOM:
    {
      // replace with t <= floor(t)
      term_t child = arith_is_int_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);
      if (child_pre != NULL_TERM) {
        child_pre = preprocessor_purify(pre, child_pre, out);
        current_pre = arith_floor(terms, child_pre);
        current_pre = mk_arith_leq(tm, child_pre, current_pre);
      } else {
        ivector_push(pre_stack, child);
      }
      break;
    }

    case ARITH_FLOOR:        // floor: purify, but its interpreted
    {
      term_t child = arith_floor_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);

      if (child_pre != NULL_TERM) {
        if (term_kind(terms, child_pre) == ARITH_CONSTANT) {
          rational_t floor;
          q_init(&floor);
          q_set(&floor, rational_term_desc(terms, child_pre));
          q_floor(&floor);
          current_pre = arith_constant(terms, &floor);
          q_clear(&floor);
        } else {
          child_pre = preprocessor_purify(pre, child_pre, out);
          if (child_pre != child) {
            current_pre = arith_floor(terms, child_pre);
          } else {
            current_pre = current;
          }
        }
      } else {
        ivector_push(pre_stack, child);
      }

      break;
    }

    case ARITH_CEIL:        // floor: purify, but its interpreted
    {
      term_t child = arith_ceil_arg(terms, current);
      term_t child_pre = preprocessor_get(pre, child);

      if (child_pre != NULL_TERM) {
        child_pre = preprocessor_purify(pre, child_pre, out);
        if (child_pre != child) {
          current_pre = arith_floor(terms, child_pre);
        } else {
          current_pre = current;
        }
      } else {
        ivector_push(pre_stack, child);
      }

      break;
    }

    case DISTINCT_TERM:
    {
      composite_term_t* desc = get_composite(terms, current_kind, current);

      bool children_done = true;
      n = desc->arity;

      // DISTINCT_TERM is lowered below into pairwise disequalities. Apply the
      // same function-sort guard before that expansion.
      for (i = 0; i < n; ++ i) {
        if (term_needs_function_diseq_guard(terms, desc->arg[i])) {
          longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
        }
      }

      ivector_t children;
      init_ivector(&children, n);

      for (i = 0; i < n; ++ i) {
        term_t child = desc->arg[i];
        term_t child_pre = preprocessor_get(pre, child);

        if (child_pre == NULL_TERM) {
          children_done = false;
          ivector_push(pre_stack, child);
        }

        if (children_done) { ivector_push(&children, child_pre); }
      }

      if (children_done) {
        ivector_t distinct;
        init_ivector(&distinct, 0);

        for (i = 0; i < n; ++ i) {
          for (j = i + 1; j < n; ++ j) {
            term_t neq = mk_eq(&pre->tm, children.data[i], children.data[j]);
            neq = opposite_term(neq);
            ivector_push(&distinct, neq);
          }
        }
        current_pre = mk_and(&pre->tm, distinct.size, distinct.data);

        delete_ivector(&distinct);
      }

      delete_ivector(&children);

      break;
    }

    case LAMBDA_TERM:
      longjmp(*pre->exception, LAMBDAS_NOT_SUPPORTED);
      break;

    default:
      // UNSUPPORTED TERM/THEORY
      longjmp(*pre->exception, MCSAT_EXCEPTION_UNSUPPORTED_THEORY);
      break;
    }

    if (current_pre != NULL_TERM) {
      preprocessor_set(pre, current, current_pre);
      ivector_pop(pre_stack);
      if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
        mcsat_trace_printf(pre->tracer, "current_pre = ");
        trace_term_ln(pre->tracer, terms, current_pre);
      }
    }

  }

  // Return the result
  t_pre = preprocessor_get(pre, t);
  if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
    mcsat_trace_printf(pre->tracer, "t_pre = ");
    trace_term_ln(pre->tracer, terms, t_pre);
  }

  ivector_reset(pre_stack);

  assert(t_pre != NULL_TERM);
  return t_pre;
}

void preprocessor_set_exception_handler(preprocessor_t* pre, jmp_buf* handler) {
  pre->exception = handler;
}

void preprocessor_push(preprocessor_t* pre) {
  scope_holder_push(&pre->scope,
      &pre->preprocess_map_list.size,
      &pre->tuple_blast_list.size,
      &pre->tuple_blast_data.size,
      &pre->tuple_blast_atoms.size,
      &pre->purification_map_list.size,
      &pre->equalities_list.size,
      NULL);
}

void preprocessor_pop(preprocessor_t* pre) {

  uint32_t preprocess_map_list_size = 0;
  uint32_t tuple_blast_list_size = 0;
  uint32_t tuple_blast_data_size = 0;
  uint32_t tuple_blast_atoms_size = 0;
  uint32_t purification_map_list_size = 0;
  uint32_t equalities_list_size = 0;

  scope_holder_pop(&pre->scope,
      &preprocess_map_list_size,
      &tuple_blast_list_size,
      &tuple_blast_data_size,
      &tuple_blast_atoms_size,
      &purification_map_list_size,
      &equalities_list_size,
      NULL);

  while (pre->preprocess_map_list.size > preprocess_map_list_size) {
    term_t t = ivector_last(&pre->preprocess_map_list);
    ivector_pop(&pre->preprocess_map_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->preprocess_map, t);
    assert(find != NULL);
    int_hmap_erase(&pre->preprocess_map, find);
  }

  while (pre->tuple_blast_list.size > tuple_blast_list_size) {
    term_t t = ivector_last(&pre->tuple_blast_list);
    ivector_pop(&pre->tuple_blast_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->tuple_blast_map, t);
    assert(find != NULL);
    int_hmap_erase(&pre->tuple_blast_map, find);
  }
  ivector_shrink(&pre->tuple_blast_data, tuple_blast_data_size);
  ivector_shrink(&pre->tuple_blast_atoms, tuple_blast_atoms_size);

  while (pre->purification_map_list.size > purification_map_list_size) {
    term_t t = ivector_last(&pre->purification_map_list);
    ivector_pop(&pre->purification_map_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->purification_map, t);
    assert(find != NULL);
    int_hmap_erase(&pre->purification_map, find);
  }

  while (pre->equalities_list.size > equalities_list_size) {
    term_t eq = ivector_last(&pre->equalities_list);
    ivector_pop(&pre->equalities_list);
    int_hmap_pair_t* find = int_hmap_find(&pre->equalities, eq);
    assert(find != NULL);
    int_hmap_erase(&pre->equalities, find);
  }
}

static value_t merge_blasted_function_value(preprocessor_t* pre, value_table_t* vtbl, type_t tau, const value_t* leaves, uint32_t nleaves);

static
value_t build_value_from_flat(preprocessor_t* pre, value_table_t* vtbl, type_t tau, const value_t* flat, uint32_t* idx) {
  type_table_t* types = pre->terms->types;

  if (type_kind(types, tau) == TUPLE_TYPE) {
    tuple_type_t* tuple = tuple_type_desc(types, tau);
    uint32_t i, n = tuple->nelem;
    value_t elem[n];
    for (i = 0; i < n; ++i) {
      elem[i] = build_value_from_flat(pre, vtbl, tuple->elem[i], flat, idx);
      if (elem[i] == null_value) {
        return null_value;
      }
    }
    return vtbl_mk_tuple(vtbl, n, elem);
  } else if (type_kind(types, tau) == FUNCTION_TYPE) {
    uint32_t n = type_leaf_count(pre, tau);
    value_t v = merge_blasted_function_value(pre, vtbl, tau, flat + *idx, n);
    *idx += n;
    return v;
  } else {
    value_t v = flat[*idx];
    (*idx)++;
    return v;
  }
}

static
bool map_args_match(value_table_t* vtbl, value_t map, const value_t* args, uint32_t n) {
  value_map_t* m = vtbl_map(vtbl, map);
  uint32_t i;
  if (m->arity != n) {
    return false;
  }
  for (i = 0; i < n; ++i) {
    if (m->arg[i] != args[i]) {
      return false;
    }
  }
  return true;
}

static
value_t find_map_result(value_table_t* vtbl, const ivector_t* maps, const value_t* args, uint32_t n, value_t def) {
  uint32_t i;
  for (i = 0; i < maps->size; ++i) {
    value_t map = maps->data[i];
    if (map_args_match(vtbl, map, args, n)) {
      return vtbl_map(vtbl, map)->val;
    }
  }
  return def;
}

static
void add_unique_flat_args(ivector_t* offsets, ivector_t* data, const value_t* args, uint32_t n) {
  uint32_t i, j;
  for (i = 0; i < offsets->size; ++i) {
    uint32_t off = offsets->data[i];
    bool same = true;
    for (j = 0; j < n; ++j) {
      if (data->data[off + j] != args[j]) {
        same = false;
        break;
      }
    }
    if (same) {
      return;
    }
  }
  ivector_push(offsets, data->size);
  ivector_add(data, args, n);
}

static
value_t merge_blasted_function_value(preprocessor_t* pre, value_table_t* vtbl, type_t tau, const value_t* leaves, uint32_t nleaves) {
  type_table_t* types = pre->terms->types;
  function_type_t* fun = function_type_desc(types, tau);
  type_t codom = fun->range;
  uint32_t i, j;
  ivector_t flat_dom;
  ivector_t unique_offsets;
  ivector_t unique_args;
  ivector_t orig_maps;
  value_t result = null_value;
  value_t leaf_defaults[nleaves];
  ivector_t leaf_maps[nleaves];
  uint32_t flat_n;
  uint32_t maps_init = 0;
  /* Short tag describing why we bailed, so the caller (or a user
   * investigating a missing model entry) can see the cause through a
   * single line of trace output. Set immediately before each `goto done`
   * error exit; the successful path leaves it NULL. */
  const char* fail_reason = NULL;

  /* All heap-backed scratch vectors are initialized up-front so that every
   * exit through the `done:` label has the same cleanup responsibilities.
   * In particular orig_maps is deliberately initialized here rather than
   * just before the loop that populates it: if its init moves, `goto done`
   * paths that run before the init would otherwise silently leak the
   * vector. Keeping the init paired with the other unconditional inits
   * makes that invariant self-evident. */
  init_ivector(&flat_dom, 0);
  init_ivector(&unique_offsets, 0);
  init_ivector(&unique_args, 0);
  init_ivector(&orig_maps, 0);

  for (i = 0; i < fun->ndom; ++i) {
    type_collect_flat(types, fun->domain[i], &flat_dom);
  }
  flat_n = flat_dom.size;

  for (i = 0; i < nleaves; ++i) {
    value_t def = null_value;
    type_t leaf_tau = NULL_TYPE;
    init_ivector(&leaf_maps[i], 0);
    maps_init = i + 1;
    if (!object_is_function(vtbl, leaves[i]) && !object_is_update(vtbl, leaves[i])) {
      fail_reason = "leaf value is neither a function nor an update object";
      goto done;
    }
    if (object_is_update(vtbl, leaves[i])) {
      vtbl_expand_update(vtbl, leaves[i], &def, &leaf_tau);
      leaf_defaults[i] = def;
      if (vtbl->hset1 != NULL) {
        ivector_add(&leaf_maps[i], (int32_t*) vtbl->hset1->data, vtbl->hset1->nelems);
        for (j = 0; j < vtbl->hset1->nelems; ++j) {
          value_map_t* map = vtbl_map(vtbl, vtbl->hset1->data[j]);
          if (map->arity != flat_n) {
            fail_reason = "update leaf map arity does not match flattened domain";
            goto done;
          }
          add_unique_flat_args(&unique_offsets, &unique_args, map->arg, flat_n);
        }
      }
      continue;
    }
    value_fun_t* fun_value = vtbl_function(vtbl, leaves[i]);
    def = fun_value->def;
    leaf_tau = fun_value->type;
    leaf_defaults[i] = def;
    ivector_add(&leaf_maps[i], (int32_t*) fun_value->map, fun_value->map_size);
    for (j = 0; j < fun_value->map_size; ++j) {
      value_map_t* map = vtbl_map(vtbl, fun_value->map[j]);
      if (map->arity != flat_n) {
        fail_reason = "function leaf map arity does not match flattened domain";
        goto done;
      }
      add_unique_flat_args(&unique_offsets, &unique_args, map->arg, flat_n);
    }
  }

  for (i = 0; i < unique_offsets.size; ++i) {
    uint32_t flat_idx = unique_offsets.data[i];
    const value_t* flat_args = (value_t*) (unique_args.data + flat_idx);
    value_t leaf_values[nleaves];
    uint32_t idx;
    value_t mapv;

    for (j = 0; j < nleaves; ++j) {
      leaf_values[j] = find_map_result(vtbl, &leaf_maps[j], flat_args, flat_n, leaf_defaults[j]);
    }

    idx = 0;
    value_t out_val = build_value_from_flat(pre, vtbl, codom, leaf_values, &idx);
    if (out_val == null_value) {
      fail_reason = "could not build codomain value from flat leaf values";
      goto done;
    }

    value_t args_orig[fun->ndom];
    idx = 0;
    for (j = 0; j < fun->ndom; ++j) {
      args_orig[j] = build_value_from_flat(pre, vtbl, fun->domain[j], flat_args, &idx);
      if (args_orig[j] == null_value) {
        fail_reason = "could not rebuild a domain argument from flat leaf values";
        goto done;
      }
    }
    mapv = vtbl_mk_map(vtbl, fun->ndom, args_orig, out_val);
    ivector_push(&orig_maps, mapv);
  }

  {
    uint32_t idx = 0;
    value_t def_val = build_value_from_flat(pre, vtbl, codom, leaf_defaults, &idx);
    if (def_val == null_value) {
      fail_reason = "could not rebuild the function default value";
      goto done;
    }
    result = vtbl_mk_function(vtbl, tau, orig_maps.size, (value_t*) orig_maps.data, def_val);
  }

 done:
  if (fail_reason != NULL && trace_enabled(pre->tracer, "mcsat::preprocess")) {
    mcsat_trace_printf(pre->tracer,
                       "merge_blasted_function_value: %s\n", fail_reason);
  }
  /* Single cleanup path for every error exit. All ivectors above are
   * unconditionally initialized before any `goto done`, so unconditional
   * deletes here are correct and stay correct if new error branches are
   * added. leaf_maps is the only exception: its initialization is
   * interleaved with error checks in the first loop, so we still only
   * delete the prefix recorded by maps_init. */
  for (i = 0; i < maps_init; ++i) {
    delete_ivector(&leaf_maps[i]);
  }
  delete_ivector(&orig_maps);
  delete_ivector(&unique_offsets);
  delete_ivector(&unique_args);
  delete_ivector(&flat_dom);
  return result;
}

static
void preprocessor_build_tuple_model(preprocessor_t* pre, model_t* model) {
  value_table_t* vtbl = model_get_vtbl(model);
  type_table_t* types = pre->terms->types;
  uint32_t i;

  for (i = 0; i < pre->tuple_blast_atoms.size; ++i) {
    term_t atom = pre->tuple_blast_atoms.data[i];
    ivector_t leaves;
    type_t tau = term_type(pre->terms, atom);
    uint32_t n, j;

    if (model_find_term_value(model, atom) != null_value) {
      continue;
    }

    init_ivector(&leaves, 0);
    tuple_blast_get(pre, atom, &leaves);
    n = leaves.size;
    if (n == 0) {
      delete_ivector(&leaves);
      continue;
    }

    value_t leaf_vals[n];
    bool ok = true;
    for (j = 0; j < n; ++j) {
      value_t v = model_get_term_value(model, leaves.data[j]);
      if (v < 0) {
        ok = false;
        break;
      }
      leaf_vals[j] = v;
    }
    if (!ok) {
      /* A blasted leaf was never assigned a value by the mcsat search.
       * We cannot reconstruct a value for the original atom, so it will
       * be absent from the returned model. Log which atom and which leaf
       * index so a user investigating a missing (show-model) entry can
       * pin the gap. */
      if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
        mcsat_trace_printf(pre->tracer,
                           "preprocessor_build_tuple_model: dropping atom ");
        trace_term_ln(pre->tracer, pre->terms, atom);
        mcsat_trace_printf(pre->tracer,
                           "  (blasted leaf %u has no value in the trail model)\n", j);
      }
      delete_ivector(&leaves);
      continue;
    }

    if (type_kind(types, tau) == FUNCTION_TYPE) {
      value_t f = merge_blasted_function_value(pre, vtbl, tau, leaf_vals, n);
      if (f >= 0) {
        model_map_term(model, atom, f);
      } else if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
        /* merge_blasted_function_value has already traced a reason code;
         * complete the message here with the concrete atom identity. */
        mcsat_trace_printf(pre->tracer,
                           "preprocessor_build_tuple_model: dropping function atom ");
        trace_term_ln(pre->tracer, pre->terms, atom);
      }
    } else {
      uint32_t idx = 0;
      value_t v = build_value_from_flat(pre, vtbl, tau, leaf_vals, &idx);
      if (v >= 0) {
        model_map_term(model, atom, v);
      } else if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
        mcsat_trace_printf(pre->tracer,
                           "preprocessor_build_tuple_model: dropping tuple atom ");
        trace_term_ln(pre->tracer, pre->terms, atom);
        mcsat_trace_printf(pre->tracer,
                           "  (leaf values did not decompose into a tuple value)\n");
      }
    }

    delete_ivector(&leaves);
  }
}

static term_t build_term_from_flat(preprocessor_t* pre, type_t tau, const term_t* flat, uint32_t* idx);
static void collect_flat_leaf_terms(preprocessor_t* pre, term_t base, type_t tau, ivector_t* out);

static
term_t merge_blasted_function_term(preprocessor_t* pre, type_t tau, const term_t* leaves, uint32_t nleaves) {
  term_table_t* terms = pre->terms;
  type_table_t* types = terms->types;
  function_type_t* fun = function_type_desc(types, tau);
  uint32_t i, idx;
  term_t result = NULL_TERM;
  term_t vars[fun->ndom];
  ivector_t flat_args;

  assert(type_kind(types, tau) == FUNCTION_TYPE);
  assert(nleaves == type_leaf_count(pre, tau));

  for (i = 0; i < fun->ndom; ++i) {
    vars[i] = new_variable(terms, fun->domain[i]);
  }

  init_ivector(&flat_args, 0);
  for (i = 0; i < fun->ndom; ++i) {
    collect_flat_leaf_terms(pre, vars[i], fun->domain[i], &flat_args);
  }

  term_t leaf_apps[nleaves];
  for (i = 0; i < nleaves; ++i) {
    leaf_apps[i] = mk_application(&pre->tm, leaves[i], flat_args.size, (term_t*) flat_args.data);
    if (leaf_apps[i] == NULL_TERM) {
      goto done;
    }
  }

  idx = 0;
  term_t body = build_term_from_flat(pre, fun->range, leaf_apps, &idx);
  if (body == NULL_TERM || idx != nleaves) {
    goto done;
  }

  result = mk_lambda(&pre->tm, fun->ndom, vars, body);

 done:
  delete_ivector(&flat_args);
  return result;
}

static
term_t build_term_from_flat(preprocessor_t* pre, type_t tau, const term_t* flat, uint32_t* idx) {
  type_table_t* types = pre->terms->types;
  switch (type_kind(types, tau)) {
  case TUPLE_TYPE: {
    tuple_type_t* tuple = tuple_type_desc(types, tau);
    uint32_t i, n = tuple->nelem;
    term_t elem[n];
    for (i = 0; i < n; ++i) {
      elem[i] = build_term_from_flat(pre, tuple->elem[i], flat, idx);
      if (elem[i] == NULL_TERM) {
        return NULL_TERM;
      }
    }
    return mk_tuple(&pre->tm, n, elem);
  }

  case FUNCTION_TYPE: {
    uint32_t n = type_leaf_count(pre, tau);
    term_t f = merge_blasted_function_term(pre, tau, flat + *idx, n);
    *idx += n;
    return f;
  }

  default: {
    term_t t = flat[*idx];
    (*idx)++;
    return t;
  }
  }
}

static
term_t mk_unblasted_function_leaf_lambda(preprocessor_t* pre, term_t atom, uint32_t leaf_i, type_t leaf_type) {
  term_table_t* terms = pre->terms;
  type_table_t* types = terms->types;
  function_type_t* atom_fun = function_type_desc(types, term_type(terms, atom));
  function_type_t* leaf_fun = function_type_desc(types, leaf_type);
  uint32_t flat_n = leaf_fun->ndom;
  uint32_t i, idx;
  term_t flat_vars[flat_n];
  term_t orig_args[atom_fun->ndom];
  term_t app;
  term_t body = NULL_TERM;
  term_t result = NULL_TERM;
  ivector_t codom_leaves;

  for (i = 0; i < flat_n; ++i) {
    flat_vars[i] = new_variable(terms, leaf_fun->domain[i]);
  }

  idx = 0;
  for (i = 0; i < atom_fun->ndom; ++i) {
    orig_args[i] = build_term_from_flat(pre, atom_fun->domain[i], flat_vars, &idx);
    if (orig_args[i] == NULL_TERM) {
      return NULL_TERM;
    }
  }
  assert(idx == flat_n);

  app = mk_application(&pre->tm, atom, atom_fun->ndom, orig_args);
  if (app == NULL_TERM) {
    return NULL_TERM;
  }

  init_ivector(&codom_leaves, 0);
  collect_flat_leaf_terms(pre, app, atom_fun->range, &codom_leaves);
  if (leaf_i < codom_leaves.size) {
    body = codom_leaves.data[leaf_i];
  }
  if (body != NULL_TERM) {
    result = mk_lambda(&pre->tm, flat_n, flat_vars, body);
  }
  delete_ivector(&codom_leaves);

  return result;
}

static
void collect_function_leaf_terms(preprocessor_t* pre, term_t base, type_t tau, ivector_t* out) {
  type_table_t* types = pre->terms->types;
  ivector_t leaf_types;
  uint32_t i;

  assert(type_kind(types, tau) == FUNCTION_TYPE);

  init_ivector(&leaf_types, 0);
  function_type_collect_blasted(types, tau, &leaf_types);
  for (i = 0; i < leaf_types.size; ++i) {
    term_t leaf = mk_unblasted_function_leaf_lambda(pre, base, i, leaf_types.data[i]);
    if (leaf != NULL_TERM) {
      ivector_push(out, leaf);
    }
  }
  delete_ivector(&leaf_types);
}

static
void collect_flat_leaf_terms(preprocessor_t* pre, term_t base, type_t tau, ivector_t* out) {
  type_table_t* types = pre->terms->types;

  switch (type_kind(types, tau)) {
  case TUPLE_TYPE: {
    tuple_type_t* tuple = tuple_type_desc(types, tau);
    uint32_t i;
    for (i = 0; i < tuple->nelem; ++i) {
      term_t child = mk_select(&pre->tm, i, base);
      collect_flat_leaf_terms(pre, child, tuple->elem[i], out);
    }
    break;
  }

  case FUNCTION_TYPE:
    collect_function_leaf_terms(pre, base, tau, out);
    break;

  default:
    ivector_push(out, base);
    break;
  }
}

static
bool substitution_has_var(const ivector_t* vars, term_t x) {
  uint32_t i;
  for (i = 0; i < vars->size; ++i) {
    if (vars->data[i] == x) {
      return true;
    }
  }
  return false;
}

term_t preprocessor_unblast_term(preprocessor_t* pre, term_t t) {
  term_table_t* terms = pre->terms;
  ivector_t vars, maps;
  ivector_t leaves, accessors;
  uint32_t i, j;
  term_t out;

  if (pre->tuple_blast_atoms.size == 0) {
    return t;
  }

  init_ivector(&vars, 0);
  init_ivector(&maps, 0);
  init_ivector(&leaves, 0);
  init_ivector(&accessors, 0);

  for (i = 0; i < pre->tuple_blast_atoms.size; ++i) {
    term_t atom = pre->tuple_blast_atoms.data[i];
    type_t atom_type = term_type(terms, atom);
    tuple_blast_get(pre, atom, &leaves);
    ivector_reset(&accessors);
    collect_flat_leaf_terms(pre, atom, atom_type, &accessors);
    if (leaves.size != accessors.size) {
      continue;
    }
    for (j = 0; j < leaves.size; ++j) {
      term_t x = leaves.data[j];
      term_t u = accessors.data[j];
      term_kind_t k = term_kind(terms, x);
      bool is_var = (k == UNINTERPRETED_TERM || k == VARIABLE);
      if (x != u && is_var && !substitution_has_var(&vars, x)) {
        ivector_push(&vars, x);
        ivector_push(&maps, u);
      }
    }
  }

  if (vars.size == 0) {
    out = t;
  } else {
    term_subst_t subst;
    init_term_subst(&subst, &pre->tm, vars.size, (term_t*) vars.data, (term_t*) maps.data);
    out = apply_term_subst(&subst, t);
    delete_term_subst(&subst);
  }

  delete_ivector(&accessors);
  delete_ivector(&leaves);
  delete_ivector(&maps);
  delete_ivector(&vars);

  return out;
}

void preprocessor_build_model(preprocessor_t* pre, model_t* model) {
  uint32_t i = 0;
  for (i = 0; i < pre->equalities_list.size; ++ i) {
    term_t eq = pre->equalities_list.data[i];
    term_t eq_var = preprocessor_get_eq_solved_var(pre, eq);
    if (trace_enabled(pre->tracer, "mcsat::preprocess")) {
      mcsat_trace_printf(pre->tracer, "eq = ");
      trace_term_ln(pre->tracer, pre->terms, eq);
      mcsat_trace_printf(pre->tracer, "\neq_var = ");
      trace_term_ln(pre->tracer, pre->terms, eq_var);
      mcsat_trace_printf(pre->tracer, "\n");
    }
    // Some equalities are solved, but then reasserted in the solver
    // these already have a model
    if (model_find_term_value(model, eq_var) != null_value) {
      continue;
    }
    // Some equalities are marked, but not solved. These we skip as they
    // are already set in the model
    if (preprocessor_get(pre, eq_var) == eq_var) {
      continue;
    }
    term_kind_t eq_kind = term_kind(pre->terms, eq);
    composite_term_t* eq_desc = get_composite(pre->terms, eq_kind, eq);
    if (eq_desc->arity > 1) {
      term_t eq_subst = eq_desc->arg[0] == eq_var ? eq_desc->arg[1] : eq_desc->arg[0];
      model_add_substitution(model, eq_var, eq_subst);
    } else {
      model_add_substitution(model, eq_var, zero_term);
    }
  }

  preprocessor_build_tuple_model(pre, model);
}


static inline
void preprocessor_gc_mark_term(preprocessor_t* pre, term_t t) {
  term_table_set_gc_mark(pre->terms, index_of(t));
  type_table_set_gc_mark(pre->terms->types, term_type(pre->terms, t));
}

void preprocessor_gc_mark(preprocessor_t* pre) {
  uint32_t i;

  for (i = 0; i < pre->preprocess_map_list.size; ++ i) {
    term_t t = pre->preprocess_map_list.data[i];
    preprocessor_gc_mark_term(pre, t);
    term_t t_pre = preprocessor_get(pre, t);
    preprocessor_gc_mark_term(pre, t_pre);
  }

  for (i = 0; i < pre->equalities_list.size; ++ i) {
    term_t t = pre->equalities_list.data[i];
    preprocessor_gc_mark_term(pre, t);
  }

  for (i = 0; i < pre->tuple_blast_list.size; ++i) {
    term_t t = pre->tuple_blast_list.data[i];
    int_hmap_pair_t* rec = int_hmap_find(&pre->tuple_blast_map, t);
    uint32_t j, n, offset;
    assert(rec != NULL);
    preprocessor_gc_mark_term(pre, t);
    offset = rec->val;
    n = pre->tuple_blast_data.data[offset];
    for (j = 0; j < n; ++j) {
      preprocessor_gc_mark_term(pre, pre->tuple_blast_data.data[offset + 1 + j]);
    }
  }

  for (i = 0; i < pre->purification_map_list.size; ++ i) {
    term_t t = pre->purification_map_list.data[i];
    preprocessor_gc_mark_term(pre, t);
    term_t t_pure = int_hmap_find(&pre->purification_map, t)->val;
    preprocessor_gc_mark_term(pre, t_pure);
  }
}
