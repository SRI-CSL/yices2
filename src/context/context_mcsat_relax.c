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
 * ON-DEMAND ZERO LEMMAS FOR THE MCSAT RELAXATION
 *
 * context.c's mcsat_relax_pprod abstracts each nonlinear monomial
 * x1^e1*...*xk^ek into a fresh simplex variable z, and (at that same, base-
 * level point) pre-builds and caches the literals for the atoms "z = 0" and
 * "xi = 0" for each factor -- new theory atoms cannot be created later
 * mid-search (simplex only allows atom creation at the base decision
 * level), so this module may only look up and combine those pre-existing
 * literals into new clauses, never create atoms itself.
 *
 * The zero lemma is z = 0 <-> exists i. xi = 0, split into the clauses:
 * - some factor xi = 0 while z != 0  ==>  not(xi=0) or (z=0)
 * - z = 0 while every factor is nonzero  ==>  not(z=0) or (x1=0) or ... or (xk=0)
 * At most one such clause is added per monomial per call, checked against
 * the live simplex assignment from the MCSAT satellite's propagate and
 * final_check hooks.
 */

#include <assert.h>

#include "context/context_utils.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/simplex/simplex.h"
#include "terms/power_products.h"
#include "terms/terms.h"
#include "utils/int_hash_map.h"
#include "utils/int_stack.h"

/*
 * thvar_t for term t if t is already internalized to arithmetic, without
 * forcing internalization as a side effect of this (read-only) check.
 */
static bool mcsat_relax_term_thvar(context_t *ctx, term_t t, thvar_t *x) {
  term_t r;

  r = intern_tbl_get_root(&ctx->intern, t);
  if (!intern_tbl_root_is_mapped(&ctx->intern, r)) {
    return false;
  }
  *x = translate_code_to_arith(ctx, intern_tbl_map_of_root(&ctx->intern, r));
  return true;
}

/*
 * Look up (without building) the literal cached by mcsat_relax_cache_zero_atom
 * (context.c) for the atom "t = 0". Read-only: never creates a new atom,
 * which is unsafe once the search is past the base level.
 */
static bool mcsat_relax_cached_zero_atom(context_t *ctx, term_t t, literal_t *l) {
  int_hmap_pair_t *r;

  if (ctx->mcsat_relax_zero_atoms == NULL) {
    return false;
  }
  r = int_hmap_find(ctx->mcsat_relax_zero_atoms, t);
  if (r == NULL) {
    return false;
  }
  *l = r->val;
  return true;
}

/*
 * Check monomial (t, z) against the live simplex assignment and add at most
 * one zero-lemma clause for it:
 * - some factor xi = 0 while z != 0  ==>  add  not(xi=0) or (z=0)
 * - z = 0 while every factor is nonzero  ==>  add  not(z=0) or (x1=0) or ... or (xk=0)
 * Returns true if a clause was added.
 *
 * Only ever combines the literals cached by mcsat_relax_cache_zero_atom
 * (built eagerly at base level, see mcsat_relax_pprod in context.c) into
 * new clauses; it never builds a new atom itself, since that's unsafe
 * mid-search.
 *
 * Those literals are typically fresh and unassigned, so nothing forces the
 * search to change the sampled assignment on its own: without the "done"
 * bitmask below, the same violation would be redetected and the same
 * clause re-added forever. At most one bit is ever set per call (bits
 * 0..n-1 for the forward clauses, bit 30 for the reverse clause), matching
 * the one-clause-per-monomial-per-call rule. Once every bit is set, this
 * monomial has nothing left to ever contribute and is skipped up front.
 */
static bool mcsat_relax_check_zero_lemma(context_t *ctx, term_t t, term_t z, int_hmap_t *done_map) {
  simplex_solver_t *simplex;
  pprod_t *p;
  thvar_t zx, fxi;
  literal_t lz, *lf, *lits;
  int_hmap_pair_t *done;
  bool z_is_zero, some_factor_zero, added;
  int32_t forward_i, full_mask;
  uint32_t i, n;

  p = pprod_term_desc(ctx->terms, t);
  n = p->len;
  assert(n < 30);
  full_mask = ((1 << n) - 1) | (1 << 30);

  done = int_hmap_get(done_map, t);
  if (done->val < 0) {
    done->val = 0;
  }
  if ((done->val & full_mask) == full_mask) {
    return false;
  }

  if (!mcsat_relax_term_thvar(ctx, z, &zx) || !mcsat_relax_cached_zero_atom(ctx, z, &lz)) {
    return false;
  }
  simplex = ctx->arith_solver;
  z_is_zero = simplex_var_is_zero_in_assignment(simplex, zx);

  lf = alloc_istack_array(&ctx->istack, n);
  added = false;
  forward_i = -1;
  some_factor_zero = false;
  for (i=0; i<n; i++) {
    if (!mcsat_relax_term_thvar(ctx, p->prod[i].var, &fxi) ||
        !mcsat_relax_cached_zero_atom(ctx, p->prod[i].var, lf+i)) {
      goto cleanup;
    }
    if (simplex_var_is_zero_in_assignment(simplex, fxi)) {
      if (!z_is_zero && forward_i < 0 && (done->val & (1 << i)) == 0) {
        forward_i = (int32_t) i;
      }
      some_factor_zero = true;
    }
  }

  if (forward_i >= 0) {
    add_binary_clause(ctx->core, not(lf[forward_i]), lz);
    done->val |= (1 << forward_i);
    added = true;
  } else if (z_is_zero && !some_factor_zero && (done->val & (1 << 30)) == 0) {
    lits = alloc_istack_array(&ctx->istack, n+1);
    lits[0] = not(lz);
    for (i=0; i<n; i++) {
      lits[i+1] = lf[i];
    }
    add_clause(ctx->core, n+1, lits);
    free_istack_array(&ctx->istack, lits);
    done->val |= (1 << 30);
    added = true;
  }

 cleanup:
  free_istack_array(&ctx->istack, lf);
  return added;
}

/*
 * Scan every tracked monomial abstraction once and add at most one zero-lemma
 * clause per monomial (batched across monomials, capped per monomial so the
 * per-round cost stays bounded as more lemma families are layered on later).
 * Returns true if at least one clause was added.
 */
bool context_check_mcsat_relax_zero_lemmas(context_t *ctx) {
  int_hmap_t *done_map;
  int_hmap_pair_t *r;
  bool added;

  if (!context_mcsat_relaxation_enabled(ctx) || ctx->mcsat_relax_abstractions == NULL) {
    return false;
  }

  done_map = context_get_mcsat_relax_zero_lemma_done(ctx);
  added = false;
  for (r = int_hmap_first_record(ctx->mcsat_relax_abstractions);
       r != NULL;
       r = int_hmap_next_record(ctx->mcsat_relax_abstractions, r)) {
    if (term_kind(ctx->terms, r->key) == POWER_PRODUCT) {
      added |= mcsat_relax_check_zero_lemma(ctx, r->key, r->val, done_map);
    }
  }
  return added;
}
