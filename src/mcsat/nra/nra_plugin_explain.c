/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "nra_plugin_explain.h"
#include "nra_plugin_internal.h"
#include "poly_constraint.h"
#include "libpoly_utils.h"

#include "utils/int_hash_map.h"
#include "utils/pointer_vectors.h"
#include "mcsat/tracing.h"
#include "terms/term_manager.h"
#include "terms/rba_buffer_terms.h"
#include "terms/terms.h"

#include <stdlib.h>
#include <stdio.h>

#include <poly/poly.h>
#include <poly/polynomial_hash_set.h>
#include <poly/variable_db.h>
#include <poly/variable_list.h>
#include <poly/variable_order.h>
#include <poly/polynomial.h>
#include <poly/interval.h>

static
void psc_buffer_ensure_size(lp_polynomial_t*** psc_buffer, uint32_t* psc_buffer_size, uint32_t size, const lp_polynomial_context_t* ctx) {
  if (*psc_buffer_size < size) {
    uint32_t new_size = *psc_buffer_size;
    while (new_size < size) {
      new_size = new_size + new_size / 2 + 10;
    }
    *psc_buffer = safe_realloc(*psc_buffer, new_size*sizeof(lp_polynomial_t*));
    uint32_t i;
    for (i = *psc_buffer_size; i < new_size; ++ i) {
      (*psc_buffer)[i] = lp_polynomial_new(ctx);
    }
    *psc_buffer_size = new_size;
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

  /** All polynomials added alrady */
  lp_polynomial_hash_set_t all_polynomails;

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

  /** The variable database */
  const lp_variable_db_t* var_db;

  /** The variable order */
  const lp_variable_order_t* order;

  /** The assignment */
  const lp_assignment_t* m;

  /** The nra plugin */
  nra_plugin_t* nra;
};

typedef struct lp_projection_map_struct lp_projection_map_t;

#define LP_PROJECTION_MAP_DEFAULT_SIZE 10

void lp_projection_map_construct(lp_projection_map_t* map, nra_plugin_t* nra) {
  map->data_size = 0;
  map->data_capacity = LP_PROJECTION_MAP_DEFAULT_SIZE;
  map->data = safe_malloc(sizeof(lp_polynomial_hash_set_t)*map->data_capacity);
  map->ctx = nra->lp_data.lp_ctx;
  map->var_db = nra->lp_data.lp_var_db;
  map->order = nra->lp_data.lp_var_order;
  map->m = nra->lp_data.lp_assignment;
  map->nra = nra;

  lp_polynomial_hash_set_construct(&map->all_polynomails);
  init_int_hmap(&map->var_to_index_map, 0);
  lp_variable_list_construct(&map->all_vars);
  lp_variable_list_construct(&map->unprojected_vars);
}

void lp_projection_map_destruct(lp_projection_map_t* map) {
  size_t i;
  for (i = 0; i < map->data_size; ++ i) {
    lp_polynomial_hash_set_destruct(map->data + i);
  }
  free(map->data);
  lp_polynomial_hash_set_destruct(&map->all_polynomails);
  delete_int_hmap(&map->var_to_index_map);
  lp_variable_list_destruct(&map->all_vars);
  lp_variable_list_destruct(&map->unprojected_vars);
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

void lp_projection_map_add(lp_projection_map_t* map, const lp_polynomial_t* p) {

  assert(!lp_polynomial_is_constant(p));

  if (lp_polynomial_hash_set_contains(&map->all_polynomails, p)) {
    return;
  }

  // Factor the polynomial and add the factors
  lp_polynomial_t** p_factors = 0;
  size_t* p_factors_multiplicities = 0;
  size_t p_factors_size = 0;
  lp_polynomial_factor_square_free(p, &p_factors, &p_factors_multiplicities, &p_factors_size);

  uint32_t i;
  for (i = 0; i < p_factors_size; ++i) {
    if (!lp_polynomial_is_constant(p_factors[i])) {
      lp_variable_t x = lp_polynomial_top_variable(p_factors[i]);
      lp_polynomial_hash_set_t* x_set = lp_projection_map_get_set_of(map, x);
      lp_polynomial_hash_set_insert(x_set, p_factors[i]);
      lp_polynomial_hash_set_insert(&map->all_polynomails, p_factors[i]);
    }
    lp_polynomial_delete(p_factors[i]);
  }

  lp_polynomial_hash_set_insert(&map->all_polynomails, p);

  free(p_factors);
  free(p_factors_multiplicities);
}

static
const lp_variable_order_t* lp_projection_map_variable_cmp_order = 0;

int lp_projection_map_variable_cmp(const void* x, const void* y) {
  lp_variable_t x_var = *(lp_variable_t*)x;
  lp_variable_t y_var = *(lp_variable_t*)y;
  return lp_variable_order_cmp(lp_projection_map_variable_cmp_order, x_var, y_var);
}

void lp_projection_map_order_vars(lp_projection_map_t* map) {
  lp_variable_list_order(&map->all_vars, map->order);
  lp_variable_list_order(&map->unprojected_vars, map->order);
}

lp_variable_t lp_projection_map_pop_top_unprojected_var(lp_projection_map_t* map) {
  if (lp_variable_list_size(&map->unprojected_vars) > 0) {
    // Sort all unprojected variable based on order
    lp_variable_list_order(&map->unprojected_vars, map->order);
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
    ret += fprintf(out, "%s : ", lp_variable_db_get_name(map->var_db, x));
    int_hmap_pair_t* find = int_hmap_find((int_hmap_t*) &map->var_to_index_map, x);
    assert(find != NULL);
    const lp_polynomial_hash_set_t* x_set = map->data + find->val;
    ret += lp_polynomial_hash_set_print(x_set, out);
    ret += fprintf(out, "\n");
  }
  return ret;
}

/**
 * Project the content of the map downwards until done. All the projection
 * sets will be closes, so that iteration is possible.
 */
void lp_projection_map_project(lp_projection_map_t* map) {

  // Temps
  uint32_t psc_i;
  const lp_polynomial_t* p = 0;
  const lp_polynomial_t* q = 0;
  lp_polynomial_t* p_r = lp_polynomial_new(map->ctx);
  lp_polynomial_t* q_r = lp_polynomial_new(map->ctx);
  lp_polynomial_t* p_r_d = lp_polynomial_new(map->ctx);
  lp_polynomial_t* p_coeff = lp_polynomial_new(map->ctx);

  // PSC buffer
  lp_polynomial_t** psc_buffer = 0;
  uint32_t psc_buffer_size = 0;

  // Project
  for (;;) {

    if (ctx_trace_enabled(map->nra->ctx, "nra::explain")) {
      ctx_trace_printf(map->nra->ctx, "current projection:\n");
      lp_projection_map_print(map, ctx_trace_out(map->nra->ctx));
    }

    // Get the top variable not projected yet
    lp_variable_t x = lp_projection_map_pop_top_unprojected_var(map);
    // If all projected, we're done
    if (x == lp_variable_null) {
      break;
    }

    if (ctx_trace_enabled(map->nra->ctx, "nra::explain")) {
      ctx_trace_printf(map->nra->ctx, "x = %s\n", lp_variable_db_get_name(map->var_db, x));
    }

    // Get the set of polynomials to project
    lp_polynomial_hash_set_close(lp_projection_map_get_set_of(map, x)); // We don't add again

    // Go through the polynomials and project
    uint32_t x_set_i;
    for (x_set_i = 0; x_set_i < lp_projection_map_get_set_of(map, x)->size; ++ x_set_i) {

      // Current polynomial
      p = lp_projection_map_get_set_of(map, x)->data[x_set_i];
      assert(lp_polynomial_top_variable(p) == x);
      uint32_t p_deg = lp_polynomial_degree(p);

      if (ctx_trace_enabled(map->nra->ctx, "nra::explain")) {
        ctx_trace_printf(map->nra->ctx, "p = "); lp_polynomial_print(p, ctx_trace_out(map->nra->ctx)); ctx_trace_printf(map->nra->ctx, "\n");
        ctx_trace_printf(map->nra->ctx, "p_deg = %u\n", p_deg);
      }

      // The reductum of p
      lp_polynomial_reductum_m(p_r, p, map->m);
      uint32_t p_r_deg = lp_polynomial_top_variable(p_r) == x ? lp_polynomial_degree(p_r) : 0;

      if (ctx_trace_enabled(map->nra->ctx, "nra::explain")) {
        ctx_trace_printf(map->nra->ctx, "p_r = "); lp_polynomial_print(p_r, ctx_trace_out(map->nra->ctx)); ctx_trace_printf(map->nra->ctx, "\n");
        ctx_trace_printf(map->nra->ctx, "p_r_deg = %u\n", p_deg);
      }

      // Add the vanishing initial coefficients
      uint32_t deg;
      for (deg = p_r_deg; deg <= p_deg; ++ deg) {
        // Add the coefficient
        lp_polynomial_get_coefficient(p_coeff, p,  deg);
        if (!lp_polynomial_is_constant(p_coeff)) {
          lp_projection_map_add(map, p_coeff);
        }
      }

      // Is p_r univariate?
      bool p_r_univariate = lp_polynomial_is_univariate(p_r);

      // Add the vanishing psc of p_r, p_r' (don't do univariate, they go to constants)
      if (p_r_deg > 1 && !p_r_univariate) {
        // Get the derivative
        lp_polynomial_derivative(p_r_d, p_r);
        // Ensure buffer size min(deg(p_r_d), deg(p_r)) + 1 = p_r_deg
        uint32_t psc_size = p_r_deg;
        psc_buffer_ensure_size(&psc_buffer, &psc_buffer_size, psc_size, map->ctx);

        // Get the psc
        lp_polynomial_psc(psc_buffer, p_r, p_r_d);
        // Add the initial sequence of the psc
        for (psc_i = 0; psc_i < psc_size; ++ psc_i) {
          // Add it
          if (!lp_polynomial_is_constant(psc_buffer[psc_i])) {
            lp_projection_map_add(map, psc_buffer[psc_i]);
          }
          // If it doesn't vanish we're done
          if (lp_polynomial_sgn(psc_buffer[psc_i], map->m)) {
            break;
          }
        }
      }

      if (p_r_deg > 0) {
        // Now combine with other reductums
        uint32_t x_set_j;
        for (x_set_j = x_set_i + 1; x_set_j < lp_projection_map_get_set_of(map, x)->size; ++ x_set_j) {

          // The other polynomial
          q = lp_projection_map_get_set_of(map, x)->data[x_set_j];
          assert(lp_polynomial_top_variable(p) == x);

          if (ctx_trace_enabled(map->nra->ctx, "nra::explain")) {
            ctx_trace_printf(map->nra->ctx, "q = "); lp_polynomial_print(q, ctx_trace_out(map->nra->ctx)); ctx_trace_printf(map->nra->ctx, "\n");
          }

          // Reductum
          lp_polynomial_reductum_m(q_r, q, map->m);
          uint32_t q_r_deg = lp_polynomial_top_variable(q_r) == x ? lp_polynomial_degree(q_r) : 0;

          // No need to work on univariate ones
          if (p_r_univariate && lp_polynomial_is_univariate(q_r)) {
             continue;
          }

          if (ctx_trace_enabled(map->nra->ctx, "nra::explain")) {
            ctx_trace_printf(map->nra->ctx, "q_r = "); lp_polynomial_print(q_r, ctx_trace_out(map->nra->ctx)); ctx_trace_printf(map->nra->ctx, "\n");
            ctx_trace_printf(map->nra->ctx, "q_r_deg = %u\n", p_deg);
          }

          if (q_r_deg > 0) {
            // psc size = min of degrees
            uint32_t psc_size = p_r_deg > q_r_deg ? q_r_deg + 1 : p_r_deg + 1;
            psc_buffer_ensure_size(&psc_buffer, &psc_buffer_size, psc_size, map->ctx);

            // Get the psc
            lp_polynomial_psc(psc_buffer, p_r, q_r);
            // Add the initial sequence of the psc
            for (psc_i = 0; psc_i < psc_size; ++ psc_i) {
              // Add it
              if (!lp_polynomial_is_constant(psc_buffer[psc_i])) {
                lp_projection_map_add(map, psc_buffer[psc_i]);
              }
              // If it doesn't vanish we're done
              if (lp_polynomial_sgn(psc_buffer[psc_i], map->m)) {
                break;
              }
            }
          }
        }
      }
    }
  }

  // Free the temps
  lp_polynomial_delete(p_coeff);
  lp_polynomial_delete(p_r);
  lp_polynomial_delete(q_r);
  lp_polynomial_delete(p_r_d);
  psc_buffer_delete(psc_buffer, psc_buffer_size);
}

term_t lp_projection_map_mk_root_atom(lp_projection_map_t* map, lp_variable_t x, size_t root_index, const lp_polynomial_t* p, root_atom_rel_t r) {
  assert(lp_polynomial_top_variable(p) == x);
  assert(lp_polynomial_lc_sgn(p) > 0);

  term_t root_atom = NULL_TERM;
  term_manager_t* tm = &map->nra->tm;

  size_t p_deg = lp_polynomial_degree(p);
  if (p_deg == 1 && lp_polynomial_lc_is_constant(p)) {
    // Linear
    // x r root(ax + b)
    // x r -b/a  [ a is positive ]
    // ax + b r 0

    term_t p_term = lp_polynomial_to_yices_term(map->nra, p);

    switch (r) {
    case ROOT_ATOM_LT:
      root_atom = mk_arith_term_lt0(tm, p_term);
      break;
    case ROOT_ATOM_LEQ:
      root_atom = mk_arith_term_leq0(tm, p_term);
      break;
    case ROOT_ATOM_EQ:
      root_atom = mk_arith_term_eq0(tm, p_term);
      break;
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
    variable_t x_var = nra_plugin_get_variable_from_lp_variable(map->nra, x);
    term_t x_term = variable_db_get_term(map->nra->ctx->var_db, x_var);
    term_t p_term = lp_polynomial_to_yices_term(map->nra, p);
    root_atom = mk_arith_root_atom(tm, root_index, x_term, p_term, r);
  }

  assert(term_kind(tm->terms, root_atom) != CONSTANT_TERM);

  return root_atom;
}

#ifndef NDEBUG
static
bool ensure_true(plugin_context_t* ctx, term_t literal) {
  term_t atom = unsigned_term(literal);
  variable_t atom_var = variable_db_get_variable_if_exists(ctx->var_db, atom);
  bool ok = true;
  if (atom_var != variable_null) {
    if (trail_has_value(ctx->trail, atom_var)) {
      const mcsat_value_t* atom_value = trail_get_value(ctx->trail, atom_var);
      if (atom_value->type != VALUE_BOOLEAN) {
        fprintf(stderr, "Value not Boolean\n");
        ok = false;
      } else if (atom_value->b == (literal != atom)){
        fprintf(stderr, "Value is false (should be true)\n");
        ok = false;
      }
    }
  }
  if (!ok) {
    fprintf(stderr, "var = %d\n", atom_var);
  }

  return ok;
}

#endif

/**
 * Lift from bottom of the projection map: generate intervals that contain
 * the current model where the polynomials at each level are sign invariant.
 */
void lp_projection_map_lift(lp_projection_map_t* map, ivector_t* out) {

  plugin_context_t* ctx = map->nra->ctx;

  // Sort the variables
  lp_variable_list_order(&map->all_vars, map->order);

  uint32_t var_i;
  for (var_i = 0; var_i < map->all_vars.list_size; ++ var_i) {

    // Variable we're lifting
    lp_variable_t x = map->all_vars.list[var_i];

    if (ctx_trace_enabled(ctx, "nra::explain")) {
      ctx_trace_printf(ctx, "lifting variable %s\n", lp_variable_db_get_name(map->var_db, x));
    }

    // We're done when at top variable
    if (lp_assignment_get_value(map->m, x)->type == LP_VALUE_NONE) {
      assert(var_i == map->all_vars.list_size - 1);
      break;
    }

    // Get the set to make sign invariant
    lp_polynomial_hash_set_t* x_set = lp_projection_map_get_set_of(map, x);
    lp_polynomial_hash_set_close(x_set);

    if (ctx_trace_enabled(ctx, "nra::explain")) {
      ctx_trace_printf(ctx, "x_set = "); lp_polynomial_hash_set_print(x_set, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
    }

    // The cell we're constructing
    lp_interval_t x_cell;
    lp_interval_construct_full(&x_cell);

    // Lower bound polynomial and root index
    lp_polynomial_t* x_cell_a_p = lp_polynomial_new(map->nra->lp_data.lp_ctx);
    size_t x_cell_a_root_index = 0;

    // Upper bound polynomial and root index
    lp_polynomial_t* x_cell_b_p = lp_polynomial_new(map->nra->lp_data.lp_ctx);
    size_t x_cell_b_root_index = 0;

    size_t p_i;
    for (p_i = 0; p_i < x_set->size; ++ p_i) {

      assert(x_cell.a_open && x_cell.b_open);

      // Polynomial and it's degree
      const lp_polynomial_t* p = x_set->data[p_i];
      assert(lp_polynomial_top_variable(p) == x);
      size_t p_deg = lp_polynomial_degree(p);

      if (ctx_trace_enabled(ctx, "nra::explain")) {
        ctx_trace_printf(ctx, "x_cell = "); lp_interval_print(&x_cell, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
        ctx_trace_printf(ctx, "x_cell_a_p = "); lp_polynomial_print(x_cell_a_p, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
        ctx_trace_printf(ctx, "x_cell_a_root_index = %zu\n", x_cell_a_root_index);
        ctx_trace_printf(ctx, "x_cell_b_p = "); lp_polynomial_print(x_cell_b_p, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
        ctx_trace_printf(ctx, "x_cell_b_root_index = %zu\n", x_cell_b_root_index);
        ctx_trace_printf(ctx, "p = "); lp_polynomial_print(p, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
        ctx_trace_printf(ctx, "p_deg = %zu\n", p_deg);
      }

      // Isolate the roots
      lp_value_t* p_roots = safe_malloc(sizeof(lp_value_t)*p_deg);
      size_t p_roots_size;
      lp_polynomial_roots_isolate(p, map->m, p_roots, &p_roots_size);

      if (ctx_trace_enabled(ctx, "nra::explain")) {
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
      if (ctx_trace_enabled(ctx, "nra::explain")) {
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

          if (ctx_trace_enabled(ctx, "nra::explain")) {
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
          lp_polynomial_assign(x_cell_a_p, p);
          x_cell_a_root_index = m;
          break;
        } else if (m < 0) {
          // in (-inf, p_roots[0]) so
          if (lp_interval_contains(&x_cell, p_roots)) {
            lp_interval_set_b(&x_cell, p_roots, 1);
            lp_polynomial_assign(x_cell_b_p, p);
            x_cell_b_root_index = 0;
          }
        } else if (m+1 == p_roots_size) {
          // in (p_roots[m], +inf)
          if (lp_interval_contains(&x_cell, p_roots + m)) {
            lp_interval_set_a(&x_cell, p_roots + m, 1);
            lp_polynomial_assign(x_cell_a_p, p);
            x_cell_a_root_index = m;
          }
        } else {
          // in (p_roots[m], p_roots[m+1])
          if (lp_interval_contains(&x_cell, p_roots + m)) {
            lp_interval_set_a(&x_cell, p_roots + m, 1);
            lp_polynomial_assign(x_cell_a_p, p);
            x_cell_a_root_index = m;
          }
          if (lp_interval_contains(&x_cell, p_roots + m + 1)) {
            lp_interval_set_b(&x_cell, p_roots + m + 1, 1);
            lp_polynomial_assign(x_cell_b_p, p);
            x_cell_b_root_index = m + 1;
          }
        }
      }

      if (ctx_trace_enabled(ctx, "nra::explain")) {
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

    if (ctx_trace_enabled(ctx, "nra::explain")) {
      ctx_trace_printf(ctx, "x_cell = "); lp_interval_print(&x_cell, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "x_cell_a_p = "); lp_polynomial_print(x_cell_a_p, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "x_cell_a_root_index = %zu\n", x_cell_a_root_index);
      ctx_trace_printf(ctx, "x_cell_b_p = "); lp_polynomial_print(x_cell_b_p, ctx_trace_out(ctx)); ctx_trace_printf(ctx, "\n");
      ctx_trace_printf(ctx, "x_cell_b_root_index = %zu\n", x_cell_b_root_index);
    }

    // Add the cell constraint
    if (lp_interval_is_point(&x_cell)) {
      term_t eq_root_atom = lp_projection_map_mk_root_atom(map, x, x_cell_a_root_index, x_cell_a_p, ROOT_ATOM_EQ);
      ivector_push(out, eq_root_atom);
      if (ctx_trace_enabled(ctx, "nra::explain")) {
        ctx_trace_printf(ctx, "eq_root_atom = "); ctx_trace_term(ctx, eq_root_atom);
      }
      assert(ensure_true(ctx, eq_root_atom));
    } else {

      const lp_value_t* x_cell_lb = lp_interval_get_lower_bound(&x_cell);
      const lp_value_t* x_cell_ub = lp_interval_get_upper_bound(&x_cell);

      assert(lp_value_cmp(x_cell_lb, x_cell_ub) < 0);

      if (x_cell_lb->type != LP_VALUE_MINUS_INFINITY) {
        term_t lb_root_atom = lp_projection_map_mk_root_atom(map, x, x_cell_a_root_index, x_cell_a_p, ROOT_ATOM_GT);
        ivector_push(out, lb_root_atom);
        if (ctx_trace_enabled(ctx, "nra::explain")) {
          ctx_trace_printf(ctx, "lb_root_atom = "); ctx_trace_term(ctx, lb_root_atom);
        }
        assert(ensure_true(ctx, lb_root_atom));
      }
      if (x_cell_ub->type != LP_VALUE_PLUS_INFINITY) {
        term_t ub_root_atom = lp_projection_map_mk_root_atom(map, x, x_cell_b_root_index, x_cell_b_p, ROOT_ATOM_LT);
        ivector_push(out, ub_root_atom);
        if (ctx_trace_enabled(ctx, "nra::explain")) {
          ctx_trace_printf(ctx, "ub_root_atom = "); ctx_trace_term(ctx, ub_root_atom);
        }
        assert(ensure_true(ctx, ub_root_atom));
      }
    }

    // Destruct the cell
    lp_interval_destruct(&x_cell);
    lp_polynomial_delete(x_cell_a_p);
    lp_polynomial_delete(x_cell_b_p);
  }

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

  if (TRACK_VAR(nra->conflict_variable)) {
    fprintf(stderr, "Explaining tracked variable\n.");
  }

  if (TRACK_VAR(nra->conflict_variable) || ctx_trace_enabled(nra->ctx, "nra::explain")) {
    ctx_trace_printf(nra->ctx, "nra_plugin_explain_conflict()\n");
    uint32_t i;
    int_mset_t variables;
    int_mset_construct(&variables, variable_null);
    for (i = 0; i < core->size; ++ i) {
      term_t core_i_t = variable_db_get_term(nra->ctx->var_db, core->data[i]);
      nra_plugin_get_literal_variables(nra, core_i_t, &variables);
      ctx_trace_printf(nra->ctx, "core[%u] = ", i);
      ctx_trace_term(nra->ctx, core_i_t);
    }
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

  // Create the map from variables to
  lp_projection_map_t projection_map;
  lp_projection_map_construct(&projection_map, nra);

  // Add all the polynomials
  uint32_t core_i;
  for (core_i = 0; core_i < core->size; ++ core_i) {
    variable_t constraint_var = core->data[core_i];
    assert(constraint_has_value(nra->ctx->trail, pos, neg, constraint_var));
    const poly_constraint_t* constraint = poly_constraint_db_get(nra->constraint_db, constraint_var);
    const lp_polynomial_t* p = poly_constraint_get_polynomial(constraint);
    lp_projection_map_add(&projection_map, p);
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
  lp_projection_map_project(&projection_map);

  // Lift
  lp_projection_map_lift(&projection_map, conflict);

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
