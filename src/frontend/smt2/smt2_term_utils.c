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

#include "smt2_term_utils.h"
#include "terms/term_explorer.h"
#include "utils/int_hash_sets.h"
#include "terms/terms.h"


/*
 * Explore a term t, add all boolean atoms to vector v.
 * - h is a hash set used to record visited terms
 */
static void collect_atoms_recursive(context_t *ctx, term_t t, int_hset_t *atoms, int_hset_t *visited) {
  term_table_t *terms;
  uint32_t i, n;

  if (t < 0) {
    t = not(t);
  }

  if (int_hset_member(visited, t)) {
    return;
  }
  int_hset_add(visited, t);

  terms = ctx->terms;

  if (term_type(terms, t) == bool_type(terms->types)) {
    int_hset_add(atoms, t);
  }

  if (term_is_projection(terms, t)) {
    collect_atoms_recursive(ctx, proj_term_arg(terms, t), atoms, visited);
  } else if (term_is_sum(terms, t)) {
    n = term_num_children(terms, t);
    for (i=0; i<n; i++) {
      term_t child;
      mpq_t q;
      mpq_init(q);
      sum_term_component(terms, t, i, q, &child);
      collect_atoms_recursive(ctx, child, atoms, visited);
      mpq_clear(q);
    }
  } else if (term_is_bvsum(terms, t)) {
    uint32_t nbits = term_bitsize(terms, t);
    int32_t *a = (int32_t*) safe_malloc(nbits * sizeof(int32_t));
    n = term_num_children(terms, t);
    for (i=0; i<n; i++) {
      term_t child;
      bvsum_term_component(terms, t, i, a, &child);
      collect_atoms_recursive(ctx, child, atoms, visited);
    }
    safe_free(a);
  } else if (term_is_product(terms, t)) {
    n = term_num_children(terms, t);
    for (i=0; i<n; i++) {
      term_t child;
      uint32_t exp;
      product_term_component(terms, t, i, &child, &exp);
      collect_atoms_recursive(ctx, child, atoms, visited);
    }
  } else if (term_is_composite(terms, t)) {
    n = term_num_children(terms, t);
    for (i=0; i<n; i++) {
      collect_atoms_recursive(ctx, term_child(terms, t, i), atoms, visited);
    }
  }
}

/*
 * Wrapper: initialize hash set then call the recursive function
 */
void collect_atoms(context_t *ctx, term_t t, int_hset_t *h) {
  int_hset_t visited;
  init_int_hset(&visited, 0);
  collect_atoms_recursive(ctx, t, h, &visited);
  delete_int_hset(&visited);
}

void filter_assumptions_by_term(context_t *ctx, term_t t, const ivector_t *assumptions, ivector_t *result) {
  int_hset_t seen_atoms;
  uint32_t i;
  term_t assumption;

  init_int_hset(&seen_atoms, 0);
  collect_atoms(ctx, t, &seen_atoms);
  
  for (i = 0; i < assumptions->size; i++) {
    assumption = assumptions->data[i];
    if (int_hset_member(&seen_atoms, unsigned_term(assumption))) {
      ivector_push(result, assumption);
    }
  }

  delete_int_hset(&seen_atoms);
} 