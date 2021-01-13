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
 
#include "nra_plugin_explain.h"
#include "nra_plugin_internal.h"
#include "poly_constraint.h"
#include "libpoly_utils.h"

#include "utils/int_hash_map.h"
#include "utils/pointer_vectors.h"
#include "utils/int_hash_sets.h"
#include "mcsat/tracing.h"
#include "terms/term_manager.h"
#include "terms/rba_buffer_terms.h"
#include "terms/terms.h"
#include "model/model_queries.h"

#include <stdlib.h>
#include <stdio.h>

#include <poly/poly.h>
#include <poly/polynomial_hash_set.h>
#include <poly/polynomial_vector.h>
#include <poly/variable_db.h>
#include <poly/variable_list.h>
#include <poly/variable_order.h>
#include <poly/polynomial.h>
#include <poly/interval.h>

static
void polynomial_buffer_ensure_size(lp_polynomial_t*** buffer, uint32_t* buffer_size, uint32_t size, const lp_polynomial_context_t* ctx) {
  if (*buffer_size < size) {
    uint32_t new_size = *buffer_size;
    while (new_size < size) {
      new_size = new_size + new_size / 2 + 10;
    }
    *buffer = safe_realloc(*buffer, new_size*sizeof(lp_polynomial_t*));
    uint32_t i;
    for (i = *buffer_size; i < new_size; ++ i) {
      (*buffer)[i] = lp_polynomial_new(ctx);
    }
    *buffer_size = new_size;
  }
}

static
void psc_buffer_delete(lp_polynomial_t** psc_buffer, uint32_t psc_buffer_size) {
  uint32_t i;
  for (i = 0; i < psc_buffer_size; ++ i) {
    lp_polynomial_delete(psc_buffer[i]);
  }
  safe_free(psc_buffer);
}


struct lp_projection_map_struct {

  /** All polynomials added already */
  lp_polynomial_hash_set_t all_polynomials;

  /** The sets we're maintaining */
  lp_polynomial_hash_set_t* data;

  /** Size of the data */
  size_t data_size;

  /** Size of the data */
  size_t data_capacity;

  /** Map from indices to the projection sets where it is the top variable */
  int_hmap_t var_to_index_map;

  /** List of all variables added */
  lp_variable_list_t all_vars;

  /** List of all yet unprojected variables */
  lp_variable_list_t unprojected_vars;

  /** The polynomial context */
  const lp_polynomial_context_t* ctx;

  /** The assignment */
  const lp_assignment_t* m;

  /** Whether to use root constraints for cell description */
  bool use_root_constraints_for_cells;

  /** Term manager to use */
  term_manager_t* tm;

  /** Plugin context (if available) */
  plugin_context_t* plugin_ctx;

  /** NRA (if available) */
  nra_plugin_t* nra;

  /** Tmp buffer (if available) */
  rba_buffer_t buffer;

  /** Map from lp variables to terms (if available) */
  int_hmap_t* lp_to_term_map;

  /// Projection options

  /** Whether to use model-based GCD */
  bool use_mgcd;

  /** WHether to use the default NLSAT projection */
  bool use_nlsat;

};

typedef struct lp_projection_map_struct lp_projection_map_t;

#define LP_PROJECTION_MAP_DEFAULT_SIZE 10

void lp_projection_map_construct(lp_projection_map_t* map,
    const lp_polynomial_context_t* lp_ctx,
    const lp_assignment_t* lp_asignment,
    term_manager_t* tm,
    nra_plugin_t* nra, /** Can be NULL */
    int_hmap_t* lp_to_term_map, /** Can be NULL */
    bool use_mgcd,
    bool use_nlsat
)
{
  map->data_size = 0;
  map->data_capacity = LP_PROJECTION_MAP_DEFAULT_SIZE;
  map->data = safe_malloc(sizeof(lp_polynomial_hash_set_t)*map->data_capacity);
  map->ctx = lp_ctx;
  map->m = lp_asignment;
  map->use_root_constraints_for_cells = true;
  map->tm = tm;
  map->nra = nra;
  map->lp_to_term_map = lp_to_term_map;
  map->plugin_ctx = (nra == NULL ? NULL : nra->ctx);
  map->use_mgcd = use_mgcd;
  map->use_nlsat = use_nlsat;

  if (nra == NULL) {
    init_rba_buffer(&map->buffer, tm->pprods);
  }

  lp_polynomial_hash_set_construct(&map->all_polynomials);
  init_int_hmap(&map->var_to_index_map, 0);
  lp_variable_list_construct(&map->all_vars);
  lp_variable_list_construct(&map->unprojected_vars);
}

void lp_projection_map_construct_from_nra(lp_projection_map_t* map, nra_plugin_t* nra) {
  lp_projection_map_construct(map,
      nra->lp_data.lp_ctx, nra->lp_data.lp_assignment,
      nra->ctx->tm, nra,
      NULL,
      nra->ctx->options->nra_mgcd, nra->ctx->options->nra_nlsat);
}

void lp_projection_map_destruct(lp_projection_map_t* map) {
  size_t i;
  for (i = 0; i < map->data_size; ++ i) {
    lp_polynomial_hash_set_destruct(map->data + i);
  }
  free(map->data);
  lp_polynomial_hash_set_destruct(&map->all_polynomials);
  delete_int_hmap(&map->var_to_index_map);
  lp_variable_list_destruct(&map->all_vars);
  lp_variable_list_destruct(&map->unprojected_vars);
  if (map->nra == NULL) {
    delete_rba_buffer(&map->buffer);
  }
}

static inline
term_t lp_projection_map_polynomial_to_term(lp_projection_map_t* map, const lp_polynomial_t* p) {
  if (map->nra) {
    return lp_polynomial_to_yices_term_nra(p, map->nra);
  } else {
    return lp_polynomial_to_yices_term(p, map->tm->terms, &map->buffer, map->lp_to_term_map);
  }
}

static inline
term_t lp_projection_map_var_to_term(lp_projection_map_t* map, lp_variable_t x_lp) {
  if (map->nra) {
    variable_t x_var = nra_plugin_get_variable_from_lp_variable(map->nra, x_lp);
    term_t x_term = variable_db_get_term(map->nra->ctx->var_db, x_var);
    return x_term;
  } else {
    assert(false);
    return NULL_TERM;
  }
}

lp_polynomial_hash_set_t* lp_projection_map_get_set_of(lp_projection_map_t* map, lp_variable_t var) {

  assert(var != variable_null);

  size_t var_index = 0;

  // Check if already in the map
  int_hmap_pair_t* find = int_hmap_find(&map->var_to_index_map, var);
  if (find == NULL) {
    // Ensure we can add new
    if (map->data_size == map->data_capacity) {
      map->data_capacity = map->data_capacity + map->data_capacity/2 + 10;
      map->data = safe_realloc(map->data, sizeof(lp_polynomial_hash_set_t)*map->data_capacity);
    }
    // Add new
    var_index = map->data_size;
    lp_polynomial_hash_set_construct(map->data + var_index);
    map->data_size ++;
    assert(map->data_size <= map->data_capacity);
    int_hmap_add(&map->var_to_index_map, var, var_index);
    // Add to the list of variables
    if (!lp_variable_list_contains(&map->all_vars, var)) {
      lp_variable_list_push(&map->all_vars, var);
    }
    if (!lp_variable_list_contains(&map->unprojected_vars, var)) {
      lp_variable_list_push(&map->unprojected_vars, var);
    }
  } else {
    // Already have it
    var_index = find->val;
  }

  return map->data + var_index;
}

void lp_projection_map_reduce(lp_projection_map_t* map, lp_variable_t x, const lp_polynomial_t* p, lp_polynomial_t* p_r);

void lp_projection_map_add_if_not_there(lp_projection_map_t* map, const lp_polynomial_t* p) {
  if (!lp_polynomial_hash_set_contains(&map->all_polynomials, p)) {
    lp_variable_t x = lp_polynomial_top_variable(p);
    lp_polynomial_hash_set_t* x_set = lp_projection_map_get_set_of(map, x);
    assert(!lp_polynomial_hash_set_contains(x_set, p));
    lp_polynomial_hash_set_insert(x_set, p);
    lp_polynomial_hash_set_insert(&map->all_polynomials, p);
  }
}

void lp_projection_map_add(lp_projection_map_t* map, const lp_polynomial_t* p) {

  // Don't add constants or things already there
  if (lp_polynomial_is_constant(p) || lp_polynomial_hash_set_contains(&map->all_polynomials, p)) {
    return;
  }

  // Reduce the polynomials and add all the vanishing coefficients
  lp_variable_t x = lp_polynomial_top_variable(p);
  lp_polynomial_t* p_r = lp_polynomial_new(map->ctx);
  lp_projection_map_reduce(map, x, p, p_r);

  // Don't add constants or things already there
  if (lp_polynomial_is_constant(p_r) || lp_polynomial_hash_set_contains(&map->all_polynomials, p_r)) {
    lp_polynomial_delete(p_r);
    return;
  }

  // If the variable has changed, it was added in reduce
  if (lp_polynomial_top_variable(p_r) != x) {
    lp_polynomial_delete(p_r);
    return;
  }

  // p_r leading coefficient doesn't vanish and it is primitive
  // all the assumptions of this are put in the map

  // Factor the polynomial. Since it's primitive, all factors are in x,
  // their leading coefficients don't vanish
  lp_polynomial_t** p_r_factors = 0;
  size_t* p_r_factors_multiplicities = 0;
  size_t p_r_factors_size = 0;
  lp_polynomial_factor_square_free(p_r, &p_r_factors, &p_r_factors_multiplicities, &p_r_factors_size);

  uint32_t i;

  lp_polynomial_t* p_r_zero = NULL;
  // If x is assigned, check if any of the factors evaluates to 0
  if (lp_assignment_get_value(map->m, x)->type != LP_VALUE_NONE) {
    for (i = 0; i < p_r_factors_size; ++ i) {
      // Get the sign of the polynomials
      int sgn = lp_polynomial_sgn(p_r_factors[i], map->m);
      if (sgn == 0) {
        if (p_r_zero == NULL) {
          p_r_zero = p_r_factors[i];
        } else {
          int cmp = lp_polynomial_cmp(p_r_factors[i], p_r_zero);
          if (cmp < 0) {
            p_r_zero = p_r_factors[i];
          }
        }
      }
    }
  }

  // If we have a 0 factor, we just add that one
  if (p_r_zero != NULL) {
    assert(!lp_polynomial_is_constant(p_r_zero));
    assert(x == lp_polynomial_top_variable(p_r_zero));
    lp_projection_map_add_if_not_there(map, p_r_zero);
  }

  // Add factors, if not zero, and delete them
  for (i = 0; i < p_r_factors_size; ++i) {
    if (p_r_zero == NULL && !lp_polynomial_is_constant(p_r_factors[i])) {
      assert(x == lp_polynomial_top_variable(p_r_factors[i]));
      lp_projection_map_add_if_not_there(map, p_r_factors[i]);
    }
    lp_polynomial_delete(p_r_factors[i]);
  }

  // Hash the inputs
  lp_polynomial_hash_set_insert(&map->all_polynomials, p);
  lp_polynomial_hash_set_insert(&map->all_polynomials, p_r);

  // Remove other temps
  free(p_r_factors);
  free(p_r_factors_multiplicities);
  lp_polynomial_delete(p_r);
}

static
const lp_variable_order_t* lp_projection_map_variable_cmp_order = 0;

int lp_projection_map_variable_cmp(const void* x, const void* y) {
  lp_variable_t x_var = *(lp_variable_t*)x;
  lp_variable_t y_var = *(lp_variable_t*)y;
  return lp_variable_order_cmp(lp_projection_map_variable_cmp_order, x_var, y_var);
}

void lp_projection_map_order_vars(lp_projection_map_t* map) {
  lp_variable_list_order(&map->all_vars, map->ctx->var_order);
  lp_variable_list_order(&map->unprojected_vars, map->ctx->var_order);
}

lp_variable_t lp_projection_map_pop_top_unprojected_var(lp_projection_map_t* map) {
  if (lp_variable_list_size(&map->unprojected_vars) > 0) {
    // Sort all unprojected variable based on order
    lp_variable_list_order(&map->unprojected_vars, map->ctx->var_order);
    lp_variable_t top = lp_variable_list_top(&map->unprojected_vars);
    lp_variable_list_pop(&map->unprojected_vars);
    return top;
  } else {
    return lp_variable_null;
  }
}

int lp_projection_map_print(const lp_projection_map_t* map, FILE* out) {
  int ret = 0;
  size_t i = 0;
  for (i = 0; i < map->all_vars.list_size; ++ i) {
    lp_variable_t x = map->all_vars.list[i];
    ret += fprintf(out, "%s : ", lp_variable_db_get_name(map->ctx->var_db, x));
    int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &map->var_to_index_map, x);
    assert(find != NULL);
    const lp_polynomial_hash_set_t* x_set = map->data + find->val;
    ret += lp_polynomial_hash_set_print(x_set, out);
    ret += fprintf(out, "\n");
  }
  return ret;
}

/**
 * Describe a part of a (or the whole) cell. If map->use_root_constraints_for_cells is true root constraints
 * will be used for full precision (unless not needed). If map->use_root_constraints_for_cells is false
 * then the cell part will be described using polynomial constraints only. The output is pushed
 * into the given vector as terms.
 */
void lp_projection_map_describe_cell_part(lp_projection_map_t* map, lp_variable_t x, size_t root_index, const lp_polynomial_t* p, root_atom_rel_t r, ivector_t* out) {
  assert(lp_polynomial_top_variable(p) == x);
  assert(lp_polynomial_lc_sgn(p) > 0);

  term_t root_atom = NULL_TERM;
  term_manager_t* tm = map->tm;

  size_t p_deg = lp_polynomial_degree(p);
  if (p_deg == 1 && lp_polynomial_lc_is_constant(p)) {
    // Linear
    // x r root(ax + b)
    // x r -b/a  [ a is positive ]
    // ax + b r 0

    term_t p_term = lp_projection_map_polynomial_to_term(map, p);

    if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::projection")) {
      ctx_trace_printf(map->plugin_ctx, "p_term = "); ctx_trace_term(map->plugin_ctx, p_term);
    }

    switch (r) {
    case ROOT_ATOM_LT:
      root_atom = mk_arith_term_lt0(tm, p_term);
      break;
    case ROOT_ATOM_LEQ:
      root_atom = mk_arith_term_leq0(tm, p_term);
      break;
    case ROOT_ATOM_EQ: {
      root_atom = mk_arith_term_eq0(tm, p_term);
      break;
    }
    case ROOT_ATOM_NEQ:
      root_atom = mk_arith_term_neq0(tm, p_term);
      break;
    case ROOT_ATOM_GEQ:
      root_atom = mk_arith_term_geq0(tm, p_term);
      break;
    case ROOT_ATOM_GT:
      root_atom = mk_arith_term_gt0(tm, p_term);
      break;
    default:
      assert(false);
    }
  } else {
    // Regular root atom
    if (map->use_root_constraints_for_cells) {
      term_t x_term = lp_projection_map_var_to_term(map, x);
      term_t p_term = lp_projection_map_polynomial_to_term(map, p);
      root_atom = mk_arith_root_atom(tm, root_index, x_term, p_term, r);
    } else {
      // Add all the derivatives according to the sign in the current model, disregard the root type
      lp_polynomial_t* current = lp_polynomial_new_copy(p);
      lp_polynomial_t* current_d = lp_polynomial_new(map->ctx);
      while (!lp_polynomial_is_constant(current)) {
        int current_sgn = lp_polynomial_sgn(current, map->m);
        term_t current_term = lp_projection_map_polynomial_to_term(map, current);
        term_t current_literal;
        if (current_sgn < 0) {
          current_literal = mk_arith_term_lt0(tm, current_term);
        } else if (current_sgn > 0) {
          current_literal = mk_arith_term_gt0(tm, current_term);
        } else {
          current_literal = mk_arith_term_eq0(tm, current_term);
        }
        // Add to output
        ivector_push(out, current_literal);
        // If the top variable is not x anymore, we're done (we added it already)
        if (lp_polynomial_top_variable(current) != x)
          break;
        // Compute derivative and continue
        lp_polynomial_derivative(current_d, current);
        lp_polynomial_swap(current_d, current);
      }
      // Remove temps
      lp_polynomial_delete(current);
      lp_polynomial_delete(current_d);
      // Done
      return;
    }
  }

  assert(term_kind(tm->terms, root_atom) != CONSTANT_TERM);

  ivector_push(out, root_atom);
}

/**
 * Compare two polynomials by degree. Otherwise, go for the leading coefficients
 */
int polynomial_cmp(const void* p1_void, const void* p2_void) {
  const lp_polynomial_t* p1 = *((const lp_polynomial_t**) p1_void);
  const lp_polynomial_t* p2 = *((const lp_polynomial_t**) p2_void);
  return lp_polynomial_cmp(p1, p2);
}

/**
 * Simplify 0-polynomials with the GCD.
 */
void gcd_simplify_zero(const lp_polynomial_context_t* ctx, lp_polynomial_t** polys, size_t* size, const lp_assignment_t* m) {
  // Temp for GCD computation
  lp_polynomial_t* gcd = lp_polynomial_new(ctx);

  uint32_t i, j, to_keep = 0;
  for (i = 0; i < *size; ++ i) {
    const lp_polynomial_t* p = polys[i];
    if (lp_polynomial_sgn(p, m) == 0) {
      for (j = 0; j < to_keep; ++ j) {
        const lp_polynomial_t* q = polys[j];
        if (lp_polynomial_sgn(q, m) == 0) {
          lp_polynomial_gcd(gcd, p, q);
          if (!lp_polynomial_is_constant(gcd)) {
            lp_polynomial_swap(polys[j], gcd);
            break;
          }
        }
      }
      if (j >= to_keep) {
        // Didn't embed it in any previous ones, keep it
        polys[to_keep++] = polys[i];
      } else {
        // Not keeping it, have to remove it
        lp_polynomial_delete(polys[i]);
      }
    } else {
      // Keep it, it's non-zero
      polys[to_keep++] = polys[i];
    }
  }

  // Resized
  *size = to_keep;

  // Delete temp
  lp_polynomial_delete(gcd);
}

/**
 * Isolate the roots of the projection polynomials of x. Then construct a cell
 * assertions and add to out. Return the bound polynomials in x_cell_a_p and x_cell_b_p.
 */
void lp_projection_map_construct_cell(lp_projection_map_t* map, lp_variable_t x, ivector_t* out,
    const lp_polynomial_t** x_cell_a_p,
    const lp_polynomial_t** x_cell_b_p
) {

  plugin_context_t* ctx = map->plugin_ctx;

  // Get the set to make sign invariant
  lp_polynomial_hash_set_t* x_set = lp_projection_map_get_set_of(map, x);
  lp_polynomial_hash_set_close(x_set);

  if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
    ctx_trace_printf(ctx, "x_set = "); lp_polynomial_hash_set_print(x_set, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
  }

  // Simplify the polynomials based on gcd:
  //   * If two polynomials evaluate to 0, they should be mutually prime
  //   * We just check: if both 0 and gcd, then we keep the gcd reducing the size
  gcd_simplify_zero(map->ctx, x_set->data, &x_set->size, map->m);

  // Sort the polynomials by degree
  qsort(x_set->data, x_set->size, sizeof(lp_polynomial_t*), polynomial_cmp);

  // The cell we're constructing
  lp_interval_t x_cell;
  lp_interval_construct_full(&x_cell);

  // Lower bound polynomial and root index
  (*x_cell_a_p) = NULL;
  size_t x_cell_a_root_index = 0;

  // Upper bound polynomial and root index
  (*x_cell_b_p) = NULL;
  size_t x_cell_b_root_index = 0;

  size_t p_i;
  bool done = false;
  for (p_i = 0; !done && p_i < x_set->size; ++ p_i) {

    assert(x_cell.a_open && x_cell.b_open);

    // Polynomial and it's degree
    const lp_polynomial_t* p = x_set->data[p_i];
    assert(lp_polynomial_top_variable(p) == x);
    size_t p_deg = lp_polynomial_degree(p);

    if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
      ctx_trace_printf(ctx, "x_cell = "); lp_interval_print(&x_cell, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "x_cell_a_p = "); if (*x_cell_a_p != NULL) lp_polynomial_print((*x_cell_a_p), ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "x_cell_a_root_index = %zu\n", x_cell_a_root_index);
      ctx_trace_printf(ctx, "x_cell_b_p = "); if (*x_cell_b_p != NULL) lp_polynomial_print((*x_cell_b_p), ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "x_cell_b_root_index = %zu\n", x_cell_b_root_index);
      ctx_trace_printf(ctx, "p = "); lp_polynomial_print(p, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "p_deg = %zu\n", p_deg);
    }

    // Isolate the roots
    assert(p_deg > 0);
    lp_value_t* p_roots = safe_malloc(sizeof(lp_value_t)*p_deg);
    size_t p_roots_size = 0;
    lp_polynomial_roots_isolate(p, map->m, p_roots, &p_roots_size);

    if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
      ctx_trace_printf(ctx, "roots = ");
      size_t p_roots_i;
      for (p_roots_i = 0; p_roots_i < p_roots_size; ++ p_roots_i) {
        if (p_roots_i) {
          ctx_trace_printf(ctx, ", ");
        }
        lp_value_print(p_roots + p_roots_i, ctx_trace_out(ctx));
      }
      ctx_trace_printf(ctx, "\n");
    }

    // Binary search for the current value x_v
    const lp_value_t* x_v = lp_assignment_get_value(map->m, x);
    if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
      ctx_trace_printf(ctx, "x_v = ");
      lp_value_print(x_v, ctx_trace_out(ctx));
      ctx_trace_printf(ctx, "\n");
    }
    if (p_roots_size > 0) {
      int m; // midpoint and where to insert
      int m_cmp;
      int lb = 0;
      int ub = p_roots_size - 1;

      for(;;) {
        m = (lb + ub) / 2;
        m_cmp = lp_value_cmp(p_roots + m, x_v);

        if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
          ctx_trace_printf(ctx, "m = %d\n", m);
          ctx_trace_printf(ctx, "m_cmp = %d\n", m_cmp);
          ctx_trace_printf(ctx, "lb = %d\n", lb);
          ctx_trace_printf(ctx, "ub = %d\n", ub);
        }

        if (m_cmp == 0) {
          // found
          break;
        } else if (m_cmp < 0) {
          lb = m + 1;
          if (lb > ub) {
            // it's in m, m+1
            break;
          }
        } else  {
          ub = m - 1;
          if (lb > ub) {
            // it's in m-1, m
            m --;
            break;
          }
        }
      }

      if (m_cmp == 0) {
        // found it at m, so we take [roots[m], roots[m]] as the final one
        // no need for more cell division
        lp_interval_collapse_to(&x_cell, x_v);
        (*x_cell_a_p) = p;
        (*x_cell_b_p) = NULL;
        x_cell_a_root_index = m;
        // We use the first one, sort should do it
        done = true;
      } else {
        // Divide cells
        if (m < 0) {
          // in (-inf, p_roots[0]) so
          if (lp_interval_contains(&x_cell, p_roots)) {
            lp_interval_set_b(&x_cell, p_roots, 1);
            (*x_cell_b_p) = p;
            x_cell_b_root_index = 0;
          }
        } else if (m + 1 == p_roots_size) {
          // in (p_roots[m], +inf)
          if (lp_interval_contains(&x_cell, p_roots + m)) {
            lp_interval_set_a(&x_cell, p_roots + m, 1);
            (*x_cell_a_p) = p;
            x_cell_a_root_index = m;
          }
        } else {
          // in (p_roots[m], p_roots[m+1])
          if (lp_interval_contains(&x_cell, p_roots + m)) {
            lp_interval_set_a(&x_cell, p_roots + m, 1);
            (*x_cell_a_p) = p;
            x_cell_a_root_index = m;
          }
          if (lp_interval_contains(&x_cell, p_roots + m + 1)) {
            lp_interval_set_b(&x_cell, p_roots + m + 1, 1);
            (*x_cell_b_p) = p;
            x_cell_b_root_index = m + 1;
          }
        }
      }
    }

    if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
      ctx_trace_printf(ctx, "roots = ");
      size_t p_roots_i;
      for (p_roots_i = 0; p_roots_i < p_roots_size; ++ p_roots_i) {
        if (p_roots_i) {
          ctx_trace_printf(ctx, ", ");
        }
        lp_value_print(p_roots + p_roots_i, ctx_trace_out(ctx));
      }
      ctx_trace_printf(ctx, "\n");
    }

    // Remove the roots
    size_t p_roots_i;
    for (p_roots_i = 0; p_roots_i < p_roots_size; ++ p_roots_i) {
      lp_value_destruct(p_roots + p_roots_i);
    }
    safe_free(p_roots);
  }

  if (ctx_trace_enabled(ctx, "nra::explain::projection")) {
    ctx_trace_printf(ctx, "x_cell = "); lp_interval_print(&x_cell, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
    ctx_trace_printf(ctx, "x_cell_a_p = "); if (*x_cell_a_p != NULL) lp_polynomial_print((*x_cell_a_p), ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
    ctx_trace_printf(ctx, "x_cell_a_root_index = %zu\n", x_cell_a_root_index);
    ctx_trace_printf(ctx, "x_cell_b_p = "); if (*x_cell_b_p != NULL) lp_polynomial_print((*x_cell_b_p), ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
    ctx_trace_printf(ctx, "x_cell_b_root_index = %zu\n", x_cell_b_root_index);
  }

  // Add the cell constraint
  if (lp_interval_is_point(&x_cell)) {
    lp_projection_map_describe_cell_part(map, x, x_cell_a_root_index, (*x_cell_a_p), ROOT_ATOM_EQ, out);
  } else {
    const lp_value_t* x_cell_lb = lp_interval_get_lower_bound(&x_cell);
    const lp_value_t* x_cell_ub = lp_interval_get_upper_bound(&x_cell);
    assert(lp_value_cmp(x_cell_lb, x_cell_ub) < 0);
    if (x_cell_lb->type != LP_VALUE_MINUS_INFINITY) {
      lp_projection_map_describe_cell_part(map, x, x_cell_a_root_index, (*x_cell_a_p), ROOT_ATOM_GT, out);
    }
    if (x_cell_ub->type != LP_VALUE_PLUS_INFINITY) {
     lp_projection_map_describe_cell_part(map, x, x_cell_b_root_index, (*x_cell_b_p), ROOT_ATOM_LT, out);
    }
  }

  // Destruct the cell
  lp_interval_destruct(&x_cell);
}

/** Add the model based PSC of the two polynomials to the projection map */
void lp_projection_map_add_psc(lp_projection_map_t* map, lp_polynomial_t*** polynomial_buffer, uint32_t* polynomial_buffer_size, lp_variable_t x, const lp_polynomial_t* p, const lp_polynomial_t* q) {
  // Ensure buffer size min(deg(p_r_d), deg(p_r)) + 1 = p_r_deg
  assert(lp_polynomial_top_variable(p) == x);
  assert(lp_polynomial_top_variable(q) == x);

  size_t p_deg = lp_polynomial_degree(p);
  size_t q_deg = lp_polynomial_degree(q);

  uint32_t psc_size = p_deg > q_deg ? q_deg + 1 : p_deg + 1;
  polynomial_buffer_ensure_size(polynomial_buffer, polynomial_buffer_size, psc_size, map->ctx);

  // Get the psc
  lp_polynomial_psc(*polynomial_buffer, p, q);
  // Add the initial sequence of the psc
  uint32_t psc_i;
  for (psc_i = 0; psc_i < psc_size; ++ psc_i) {
    // Add it
    lp_projection_map_add(map, (*polynomial_buffer)[psc_i]);
    // If it doesn't vanish we're done
    if (lp_polynomial_sgn((*polynomial_buffer)[psc_i], map->m)) {
      break;
    }
  }
}

/** Add the model-based gcd of the two polynomials to the projection map */
void lp_projection_map_add_mgcd(lp_projection_map_t* map, lp_variable_t x, const lp_polynomial_t* p, const lp_polynomial_t* q) {
  // Ensure buffer size min(deg(p_r_d), deg(p_r)) + 1 = p_r_deg
  assert(lp_polynomial_top_variable(p) == x);
  assert(lp_polynomial_top_variable(q) == x);

  // Compute the gcd
  if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::mgcd")) {
    ctx_trace_printf(map->plugin_ctx, "p = "); lp_polynomial_print(p, ctx_trace_out(map->plugin_ctx)); ctx_trace_printf(map->plugin_ctx, "\n");
    ctx_trace_printf(map->plugin_ctx, "q = "); lp_polynomial_print(q, ctx_trace_out(map->plugin_ctx)); ctx_trace_printf(map->plugin_ctx, "\n");

    lp_variable_list_t vars;
    lp_variable_list_construct(&vars);
    lp_polynomial_get_variables(p, &vars);
    lp_polynomial_get_variables(q, &vars);
    lp_variable_list_order(&vars, map->ctx->var_order);

    uint32_t i;
    for (i = 0; i < vars.list_size; ++ i) {
      lp_variable_t var = vars.list[i];
      const lp_value_t* v = lp_assignment_get_value(map->m, var);
      if (v->type != LP_VALUE_NONE) {
        ctx_trace_printf(map->plugin_ctx, "%s -> ", lp_variable_db_get_name(map->ctx->var_db, var));
        lp_value_print(v, ctx_trace_out(map->plugin_ctx));
        ctx_trace_printf(map->plugin_ctx, "\n");
      }
    }

    lp_variable_list_destruct(&vars);
  }

  lp_polynomial_vector_t* assumptions = lp_polynomial_mgcd(p, q, map->m);

  if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::mgcd")) {
    ctx_trace_printf(map->plugin_ctx, "mgcd done: \n");
  }

  // Add the initial sequence of the psc
  uint32_t assumptions_i;
  uint32_t assumptions_size = lp_polynomial_vector_size(assumptions);
  for (assumptions_i = 0; assumptions_i < assumptions_size; ++ assumptions_i) {
    // Add it
    lp_polynomial_t* assumption = lp_polynomial_vector_at(assumptions, assumptions_i);
    lp_projection_map_add(map, assumption);
    lp_polynomial_delete(assumption);
  }

  lp_polynomial_vector_delete(assumptions);
}

void lp_projection_map_reduce(lp_projection_map_t* map, lp_variable_t x, const lp_polynomial_t* p, lp_polynomial_t* p_r) {

  assert(p != p_r);
  assert(lp_polynomial_top_variable(p) == x);

  lp_polynomial_t* p_coeff = lp_polynomial_new(map->ctx);

  uint32_t p_deg = lp_polynomial_degree(p);

  lp_polynomial_reductum_m(p_r, p, map->m);
  uint32_t p_r_deg = lp_polynomial_top_variable(p_r) == x ? lp_polynomial_degree(p_r) : 0;

  // Add the vanishing initial coefficients (this includes the top reduced, hence the content)
  uint32_t deg;
  for (deg = p_r_deg; deg <= p_deg; ++ deg) {
    // Add the coefficient
    lp_polynomial_get_coefficient(p_coeff, p,  deg);
    lp_projection_map_add(map, p_coeff);
  }

  // Get the primitive part
  lp_polynomial_pp(p_r, p_r);

  lp_polynomial_delete(p_coeff);
}

/**
 * Project the content of the map downwards until done. All the projection
 * sets will be closed, so that iteration is possible.
 */
void lp_projection_map_project(lp_projection_map_t* map, ivector_t* out, int_hset_t* cell_variables) {

  // Temps
  const lp_polynomial_t* p = 0;
  const lp_polynomial_t* q = 0;
  lp_polynomial_t* p_r = lp_polynomial_new(map->ctx);
  lp_polynomial_t* q_r = lp_polynomial_new(map->ctx);
  lp_polynomial_t* p_r_d = lp_polynomial_new(map->ctx);

  // PSC buffer
  lp_polynomial_t** polynomial_buffer = 0;
  uint32_t polynomial_buffer_size = 0;

  const lp_polynomial_t* x_cell_a_p = NULL;
  const lp_polynomial_t* x_cell_b_p = NULL;
  lp_polynomial_t* x_cell_a_p_r = lp_polynomial_new(map->ctx);
  lp_polynomial_t* x_cell_b_p_r = lp_polynomial_new(map->ctx);

  // Order the variables 
  lp_projection_map_order_vars(map);

  // Project
  for (;;) {

    if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::projection")) {
      ctx_trace_printf(map->plugin_ctx, "current projection:\n");
      lp_projection_map_print(map, ctx_trace_out(map->plugin_ctx));
    }

    // Get the top variable not projected yet
    lp_variable_t x = lp_projection_map_pop_top_unprojected_var(map);
    // If all projected, we're done
    if (x == lp_variable_null) {
      break;
    }

    if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::projection")) {
      ctx_trace_printf(map->plugin_ctx, "x = %s\n", lp_variable_db_get_name(map->ctx->var_db, x));
    }

    // Get the set of polynomials to project
    lp_polynomial_hash_set_close(lp_projection_map_get_set_of(map, x)); // We don't add again

    // If we are at the top variable we project all polynomials.
    // At the lower levels we:
    // * Isolate the roots, find the two (or one) roots that enclose the current
    //   model (the cell, polynomials l, u).
    // * L: polynomials that have roots below the cell
    // * U: polynomials that have roots above the cell
    // * The projection is then
    //   - all p: fix degree, and number of roots, i.e. red(p), and psc/gcd(p,p')
    //   - relationship between p in L, and l
    //   - relationship between p in U, and u
    //   - relationship between l and u
    bool top = lp_assignment_get_value(map->m, x)->type == LP_VALUE_NONE;

    if (!top || (cell_variables != NULL && int_hset_member(cell_variables, x))) {
      // Generate the cell, and get the bounding polynomials
      x_cell_a_p = NULL;
      x_cell_b_p = NULL;
      lp_projection_map_construct_cell(map, x, out, &x_cell_a_p, &x_cell_b_p);
      // Reduce the polynomials
      if (x_cell_a_p != NULL) {
        lp_projection_map_reduce(map, x, x_cell_a_p, x_cell_a_p_r);
      }
      if (x_cell_b_p != NULL) {
        lp_projection_map_reduce(map, x, x_cell_b_p, x_cell_b_p_r);
      }
    }

    // Go through the polynomials and project
    uint32_t x_set_i;
    for (x_set_i = 0; x_set_i < lp_projection_map_get_set_of(map, x)->size; ++ x_set_i) {

      // Current polynomial
      p = lp_projection_map_get_set_of(map, x)->data[x_set_i];
      assert(lp_polynomial_top_variable(p) == x);
      uint32_t p_deg = lp_polynomial_degree(p);

      if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::projection")) {
        ctx_trace_printf(map->plugin_ctx, "p = "); lp_polynomial_print(p, ctx_trace_out(map->plugin_ctx)); ctx_trace_printf(map->plugin_ctx, "\n");
        ctx_trace_printf(map->plugin_ctx, "p_deg = %u\n", p_deg);
      }

      // Reduce p modulo the model, and add assumptions
      lp_projection_map_reduce(map, x, p, p_r);
      uint32_t p_r_deg = lp_polynomial_top_variable(p_r) == x ? lp_polynomial_degree(p_r) : 0;

      // Is p_r univariate?
      bool p_r_univariate = lp_polynomial_is_univariate(p_r);

      // Add the vanishing psc of p_r, p_r' (don't do univariate, they go to constants)
      if (p_r_deg > 1 && !p_r_univariate) {
        // Get the derivative
        lp_polynomial_derivative(p_r_d, p_r);
        // p_r is reduced, but the derivative might not be (the numberical constants)
        lp_polynomial_pp(p_r_d, p_r_d);
        // Add the projection
        if (map->use_mgcd) {
          lp_projection_map_add_mgcd(map, x, p_r, p_r_d);
        } else {
          lp_projection_map_add_psc(map, &polynomial_buffer, &polynomial_buffer_size, x, p_r, p_r_d);
        }
      }

      if (p_r_deg > 0) {
        // Now combine with other reductums
        if (!map->use_nlsat && !top) {
          // Compare with lower bound polynomial
          if (p != x_cell_a_p && x_cell_b_p_r != NULL) {
            uint32_t x_cell_a_p_deg = lp_polynomial_top_variable(x_cell_a_p_r) == x ? lp_polynomial_degree(x_cell_a_p_r) : 0;
            if ((!p_r_univariate || !lp_polynomial_is_univariate(x_cell_a_p_r)) && x_cell_a_p_deg > 0) {
              // Add the psc
              if (map->use_mgcd) {
                lp_projection_map_add_mgcd(map, x, p_r, x_cell_a_p_r);
              } else {
                lp_projection_map_add_psc(map, &polynomial_buffer, &polynomial_buffer_size, x, p_r, x_cell_a_p_r);
              }
            }
          }
          // Compare with upper bound polynomial
          if (p != x_cell_b_p_r && x_cell_b_p_r != NULL) {
            uint32_t x_cell_b_p_r_deg = lp_polynomial_top_variable(x_cell_b_p_r) == x ? lp_polynomial_degree(x_cell_b_p_r) : 0;
            if ((!p_r_univariate || !lp_polynomial_is_univariate(x_cell_b_p_r)) && x_cell_b_p_r_deg > 0) {
              // Add the psc
              if (map->use_mgcd) {
                lp_projection_map_add_mgcd(map, x, p_r, x_cell_b_p_r);
              } else {
                lp_projection_map_add_psc(map, &polynomial_buffer, &polynomial_buffer_size, x, p_r, x_cell_b_p_r);
              }
            }
          }
        } else {
          // Top level, project with all
          uint32_t x_set_j;
          for (x_set_j = x_set_i + 1; x_set_j < lp_projection_map_get_set_of(map, x)->size; ++ x_set_j) {

            // The other polynomial
            q = lp_projection_map_get_set_of(map, x)->data[x_set_j];
            assert(lp_polynomial_top_variable(p) == x);

            if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::projection")) {
              ctx_trace_printf(map->plugin_ctx, "q = "); lp_polynomial_print(q, ctx_trace_out(map->plugin_ctx)); ctx_trace_printf(map->plugin_ctx, "\n");
            }

            // Reductum
            lp_polynomial_reductum_m(q_r, q, map->m);
            uint32_t q_r_deg = lp_polynomial_top_variable(q_r) == x ? lp_polynomial_degree(q_r) : 0;

            // No need to work on univariate ones
            if (p_r_univariate && lp_polynomial_is_univariate(q_r)) {
               continue;
            }

            if (ctx_trace_enabled(map->plugin_ctx, "nra::explain::projection")) {
              ctx_trace_printf(map->plugin_ctx, "q_r = "); lp_polynomial_print(q_r, ctx_trace_out(map->plugin_ctx)); ctx_trace_printf(map->plugin_ctx, "\n");
              ctx_trace_printf(map->plugin_ctx, "q_r_deg = %u\n", q_r_deg);
            }

            if (q_r_deg > 0) {
              // Add the psc
              if (map->use_mgcd) {
                lp_projection_map_add_mgcd(map, x, p_r, q_r);
              } else {
                lp_projection_map_add_psc(map, &polynomial_buffer, &polynomial_buffer_size, x, p_r, q_r);
              }
            }
          }
        }
      }
    }
  }

  // Free the temps
  lp_polynomial_delete(p_r);
  lp_polynomial_delete(q_r);
  lp_polynomial_delete(p_r_d);
  if (x_cell_a_p_r != NULL) {
    lp_polynomial_delete(x_cell_a_p_r);
  }
  if (x_cell_b_p_r != NULL) {
    lp_polynomial_delete(x_cell_b_p_r);
  }
  psc_buffer_delete(polynomial_buffer, polynomial_buffer_size);
}

#ifndef NDEBUG
static
bool constraint_has_value(const mcsat_trail_t* trail, const int_mset_t* pos, const int_mset_t* neg, variable_t constraint) {
  if (trail_has_value(trail, constraint)) {
    return true;
  }
  if (int_mset_contains(pos, constraint)) {
    return true;
  }
  if (int_mset_contains(neg, constraint)) {
    return true;
  }
  return false;
}
#endif

static
bool constraint_get_value(const mcsat_trail_t* trail, const int_mset_t* pos, const int_mset_t* neg, variable_t constraint) {
  if (trail_has_value(trail, constraint)) {
    return trail_get_boolean_value(trail, constraint);
  }
  if (int_mset_contains(pos, constraint)) {
    return true;
  }
  if (int_mset_contains(neg, constraint)) {
    return false;
  }
  assert(false);
  return false;
}

void nra_plugin_explain_conflict(nra_plugin_t* nra, const int_mset_t* pos, const int_mset_t* neg,
    const ivector_t* core, const ivector_t* lemma_reasons, ivector_t* conflict) {

  if (ctx_trace_enabled(nra->ctx, "nra::explain")) {
    ctx_trace_printf(nra->ctx, "nra_plugin_explain_conflict()\n");
    uint32_t i;
    int_mset_t variables;
    int_mset_construct(&variables, variable_null);
    for (i = 0; i < core->size; ++ i) {
      term_t core_i_t = variable_db_get_term(nra->ctx->var_db, core->data[i]);
      nra_plugin_get_constraint_variables(nra, core_i_t, &variables);
      ctx_trace_printf(nra->ctx, "core[%u] = ", i);
      ctx_trace_term(nra->ctx, core_i_t);
    }
    trail_print(nra->ctx->trail, ctx_trace_out(nra->ctx));
    ivector_t* variables_list = int_mset_get_list(&variables);
    for (i = 0; i < variables_list->size; ++ i) {
      variable_t var = variables_list->data[i];
      if (trail_has_value(nra->ctx->trail, var)) {
        const mcsat_value_t* v = trail_get_value(nra->ctx->trail, var);
        variable_db_print_variable(nra->ctx->var_db, var, ctx_trace_out(nra->ctx));
        ctx_trace_printf(nra->ctx, " -> ");
        mcsat_value_print(v, ctx_trace_out(nra->ctx));
        ctx_trace_printf(nra->ctx, "\n");
      }
    }
    int_mset_destruct(&variables);
  }

  // Check if there is a simple Fourier-Motzkin explanation
  if (false && core->size == 2 && lemma_reasons->size == 0) {
    variable_t c0_var = core->data[0];
    variable_t c1_var = core->data[1];
    bool c0_negated = !constraint_get_value(nra->ctx->trail, pos, neg, c0_var);
    bool c1_negated = !constraint_get_value(nra->ctx->trail, pos, neg, c1_var);
    const poly_constraint_t* c0 = poly_constraint_db_get(nra->constraint_db, c0_var);
    const poly_constraint_t* c1 = poly_constraint_db_get(nra->constraint_db, c1_var);
    bool resolved = poly_constraint_resolve_fm(c0, c0_negated, c1, c1_negated, nra, conflict);
    if (resolved) {
      term_t c0_term = variable_db_get_term(nra->ctx->var_db, c0_var);
      if (c0_negated) c0_term = opposite_term(c0_term);
      term_t c1_term = variable_db_get_term(nra->ctx->var_db, c1_var);
      if (c1_negated) c1_term = opposite_term(c1_term);
      ivector_push(conflict, c0_term);
      ivector_push(conflict, c1_term);
      return;
    }
  }

  // Create the map from variables to
  lp_projection_map_t projection_map;
  lp_projection_map_construct_from_nra(&projection_map, nra);

  // Add all the polynomials
  uint32_t core_i;
  for (core_i = 0; core_i < core->size; ++ core_i) {
    variable_t constraint_var = core->data[core_i];
    assert(constraint_has_value(nra->ctx->trail, pos, neg, constraint_var));
    const poly_constraint_t* constraint = poly_constraint_db_get(nra->constraint_db, constraint_var);
    // If the polynomial isn't unit, it is a global inference, so we explain with a different polynomial
    bool is_unit = poly_constraint_is_unit(constraint, nra->lp_data.lp_assignment);
    bool is_speculation = int_mset_contains(pos, constraint_var) || int_mset_contains(neg, constraint_var);
    bool is_inference = false;
    if (!is_unit && !is_speculation) {
      const lp_polynomial_t* p = poly_constraint_get_polynomial(constraint);
      lp_sign_condition_t sgn_condition = poly_constraint_get_sign_condition(constraint);
      bool negated = !trail_get_boolean_value(nra->ctx->trail, constraint_var);
      variable_t conflict_var = nra->conflict_variable;
      if (conflict_var == variable_null) conflict_var = nra->conflict_variable_int;
      lp_variable_t x = nra_plugin_get_lp_variable(nra, conflict_var);
      lp_polynomial_t* p_inference_reason = lp_polynomial_constraint_explain_infer_bounds(p, sgn_condition, negated, x);
      if (p_inference_reason != NULL) {
        is_inference = true;
        lp_projection_map_add(&projection_map, p_inference_reason);
        lp_polynomial_delete(p_inference_reason);
      }
    }
    if (!is_inference) {
      const lp_polynomial_t* p = poly_constraint_get_polynomial(constraint);
      lp_projection_map_add(&projection_map, p);
    }

  }

  // Add all the top-level reasons for the conflict variable
  uint32_t lemma_reasons_i;
  for (lemma_reasons_i = 0; lemma_reasons_i < lemma_reasons->size; ++ lemma_reasons_i) {
    variable_t constraint_var = lemma_reasons->data[lemma_reasons_i];
    const poly_constraint_t* constraint = poly_constraint_db_get(nra->constraint_db, constraint_var);
    const lp_polynomial_t* p = poly_constraint_get_polynomial(constraint);
    lp_projection_map_add(&projection_map, p);
  }

  // Project
  lp_projection_map_project(&projection_map, conflict, NULL);

  // Add the core to the conflict
  for (core_i = 0; core_i < core->size; ++ core_i) {
    variable_t constraint_var = core->data[core_i];
    term_t constraint_term = variable_db_get_term(nra->ctx->var_db, constraint_var);
    assert(constraint_has_value(nra->ctx->trail, pos, neg, constraint_var));
    bool constraint_value = constraint_get_value(nra->ctx->trail, pos, neg, constraint_var);
    if (!constraint_value) {
      constraint_term = opposite_term(constraint_term);
    }
    ivector_push(conflict, constraint_term);
  }

  // Remove the projection map
  lp_projection_map_destruct(&projection_map);
}

void nra_plugin_describe_cell(nra_plugin_t* nra, term_t p, ivector_t* out_literals) {

  // Create the projection map
  lp_projection_map_t projection_map;
  lp_projection_map_construct_from_nra(&projection_map, nra);
  projection_map.use_root_constraints_for_cells = false;

  if (ctx_trace_enabled(nra->ctx, "nra::simplify_conflict")) {
    ctx_trace_printf(nra->ctx, "p = "); ctx_trace_term(nra->ctx, p);
  }

  // Add the polynomial
  lp_polynomial_t* p_poly = lp_polynomial_from_term_nra(nra, p, NULL);
  lp_projection_map_add(&projection_map, p_poly);
  lp_polynomial_delete(p_poly);

  // Project
  lp_projection_map_project(&projection_map, out_literals, NULL);

  // Remove the projection map
  lp_projection_map_destruct(&projection_map);
}

/**
 * Add the polynomial from the constraint to the projection map.
 * - We don't care about polarity, we just care about the polynomial.
 */
void lp_projection_map_add_constraint(lp_projection_map_t* map, term_t cstr, int_hmap_t* term_to_lp_map) {

  term_t t1, t2;

  term_table_t* terms = map->tm->terms;
  lp_polynomial_t* cstr_polynomial = NULL;

  // Depending on the kind, make the constraints
  term_kind_t cstr_kind = term_kind(terms, cstr);
  switch (cstr_kind) {
  case ARITH_EQ_ATOM: {
    // p == 0
    t1 = arith_atom_arg(terms, cstr);
    cstr_polynomial = lp_polynomial_from_term(t1, terms, term_to_lp_map, map->ctx, NULL);
    break;
  }
  case ARITH_GE_ATOM:
    // p >= 0
    t1 = arith_atom_arg(terms, cstr);
    cstr_polynomial = lp_polynomial_from_term(t1, terms, term_to_lp_map, map->ctx, NULL);
    break;
  case EQ_TERM:
  case ARITH_BINEQ_ATOM: {
    // LHS = RHS
    t1 = composite_term_arg(terms, cstr, 0);
    t2 = composite_term_arg(terms, cstr, 1);
    // Get the polynomials
    lp_integer_t t1_c, t2_c;
    lp_integer_construct(&t1_c);
    lp_integer_construct(&t2_c);
    lp_polynomial_t* t1_p = lp_polynomial_from_term(t1, terms, term_to_lp_map, map->ctx, &t1_c);
    lp_polynomial_t* t2_p = lp_polynomial_from_term(t2, terms, term_to_lp_map, map->ctx, &t2_c);
    //  t1_p/t1_c = t2_p/t2_c
    //  t1_p*t2_c - t2_p*t1_c
    lp_integer_neg(lp_Z, &t1_c, &t1_c);
    lp_polynomial_mul_integer(t1_p, t1_p, &t2_c);
    lp_polynomial_mul_integer(t2_p, t2_p, &t1_c);
    // Add them
    cstr_polynomial = lp_polynomial_new(map->ctx);
    lp_polynomial_add(cstr_polynomial, t1_p, t2_p);
    // Remove temps
    lp_polynomial_delete(t1_p);
    lp_polynomial_delete(t2_p);
    lp_integer_destruct(&t1_c);
    lp_integer_destruct(&t2_c);
    break;
  }
  default:
    assert(false);
  }

  // Add to map
  lp_projection_map_add(map, cstr_polynomial);

  // Remove temp
  lp_polynomial_delete(cstr_polynomial);
}

#define TRACE 1

#if TRACE
#include <inttypes.h>
#include "io/term_printer.h"
#endif

int32_t nra_project_arith_literals(ivector_t* literals, model_t* mdl, term_manager_t* tm,
    uint32_t n_vars_to_elim, const term_t *vars_to_elim,
    uint32_t n_vars_to_keep, const term_t *vars_to_keep) {

  uint32_t i;

  // Mapping from terms to libpoly variables and back
  int_hmap_t lp_var_to_term_map;
  int_hmap_t term_to_lp_var_map;
  init_int_hmap(&lp_var_to_term_map, 0);
  init_int_hmap(&term_to_lp_var_map, 0);

  // Variable database
  lp_variable_db_t* lp_var_db = lp_variable_db_new();

  // The variable order
  lp_variable_order_t* lp_var_order = lp_variable_order_new();

  // Libpoly context
  lp_polynomial_context_t* lp_ctx = lp_polynomial_context_new(lp_Z, lp_var_db, lp_var_order);

  // Assignment
  lp_assignment_t lp_assignment;
  lp_assignment_construct(&lp_assignment, lp_var_db);

  // Set of variables we're keeping
  int_hset_t vars_to_keep_set;
  init_int_hset(&vars_to_keep_set, 0);

  // Add all the variables we're keeping
  for (i = 0; i < n_vars_to_keep; ++ i) {

    term_t x = vars_to_keep[i];
    type_kind_t x_type = term_type_kind(tm->terms, x);
    if (x_type != REAL_TYPE && x_type != INT_TYPE) {
      continue;
    }

    lp_variable_t x_lp = lp_variable_from_term(x, tm->terms, lp_var_db);

    // We're keeping this var
    int_hset_add(&vars_to_keep_set, x_lp);

#if TRACE
    fprintf(stderr, "Adding variable to keep: %s\n", lp_variable_db_get_name(lp_var_db, x_lp));
#endif

    // Add variables to map
    int_hmap_add(&lp_var_to_term_map, x_lp, x);
    int_hmap_add(&term_to_lp_var_map, x, x_lp);

    // Get the value in the model
    value_t x_value = model_get_term_value(mdl, x);
    assert(x_value >= 0);
    mcsat_value_t x_value_mcsat, x_value_tmp;
    mcsat_value_construct_from_value(&x_value_mcsat, &mdl->vtbl, x_value);
    const mcsat_value_t *x_value_lp = ensure_lp_value(&x_value_mcsat, &x_value_tmp);

    // Set the model value
    lp_assignment_set_value(&lp_assignment, x_lp, &x_value_lp->lp_value);

    // Delete the temps
    mcsat_value_destruct(&x_value_mcsat);
    if (x_value_lp == &x_value_tmp) {
      mcsat_value_destruct(&x_value_tmp);
    }

    // Also add to the order
    lp_variable_order_push(lp_var_order, x_lp);
  }

  // Add all the variables we're eliminating
  for (i = 0; i < n_vars_to_elim; ++ i) {

    term_t x = vars_to_elim[i];
    type_kind_t x_type = term_type_kind(tm->terms, x);
    if (x_type != REAL_TYPE && x_type != INT_TYPE) {
      continue;
    }

    lp_variable_t x_lp = lp_variable_from_term(x, tm->terms, lp_var_db);

#if TRACE
    fprintf(stderr, "Adding variable to eliminate: %s\n", lp_variable_db_get_name(lp_var_db, x_lp));
#endif

    // Add variables to map
    int_hmap_add(&lp_var_to_term_map, x_lp, x);
    int_hmap_add(&term_to_lp_var_map, x, x_lp);

    // Get the value in the model
    value_t x_value = model_get_term_value(mdl, x);
    assert(x_value >= 0);
    mcsat_value_t x_value_mcsat, x_value_tmp;
    mcsat_value_construct_from_value(&x_value_mcsat, &mdl->vtbl, x_value);
    const mcsat_value_t *x_value_lp = ensure_lp_value(&x_value_mcsat, &x_value_tmp);

    // Set the model value
    lp_assignment_set_value(&lp_assignment, x_lp, &x_value_lp->lp_value);

    // Delete the temps
    mcsat_value_destruct(&x_value_mcsat);
    if (x_value_lp == &x_value_tmp) {
      mcsat_value_destruct(&x_value_tmp);
    }

    // Also add to the order
    lp_variable_order_push(lp_var_order, x_lp);
  }

  // Setup the projection
  lp_projection_map_t projector;
  lp_projection_map_construct(&projector, lp_ctx, &lp_assignment, tm, NULL, &lp_var_to_term_map, false, false);
  projector.use_root_constraints_for_cells = false;

  // Add all the literals
  for (i = 0; i < literals->size; ++ i) {
    term_t l = literals->data[i];
#if TRACE
    fprintf(stderr, "Adding constraints: ");
    print_term(stderr, tm->terms, l);
    fprintf(stderr, "\n");
#endif
    lp_projection_map_add_constraint(&projector, l, &term_to_lp_var_map);
  }

  // Project
  ivector_reset(literals);
  lp_projection_map_project(&projector, literals, &vars_to_keep_set);

#if TRACE
  fprintf(stderr, "Projection:\n");
  for (i = 0; i < literals->size; ++ i) {
    fprintf(stderr, "P[%i] = ", i);
    print_term(stderr, tm->terms, literals->data[i]);
    fprintf(stderr, "\n");
  }
#endif

  // Delete temps
  lp_projection_map_destruct(&projector);
  delete_int_hset(&vars_to_keep_set);
  lp_variable_db_detach(lp_var_db);
  lp_assignment_destruct(&lp_assignment);
  delete_int_hmap(&term_to_lp_var_map);
  delete_int_hmap(&lp_var_to_term_map);

  return 0;
}


