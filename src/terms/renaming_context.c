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
 * Variable renaming for substitutions
 */

#include <assert.h>

#include "terms/renaming_context.h"

/*
 * Initialization:
 * - ttbl = attached term table
 * - n = initial size of the substitution table
 *   if n=0, the default size (defined in subst_context.h) is used.
 */
void init_renaming_ctx(renaming_ctx_t *ctx, term_table_t *ttbl, uint32_t n) {
  init_subst_ctx(&ctx->subst, n);
  init_renaming(&ctx->rename, ttbl);
  ctx->hash = NULL;
}


/*
 * Deletion
 */
void delete_renaming_ctx(renaming_ctx_t *ctx) {
  delete_subst_ctx(&ctx->subst);
  delete_renaming(&ctx->rename);
  ctx->hash = NULL;
}


/*
 * Full reset
 */
void reset_renaming_ctx(renaming_ctx_t *ctx) {
  reset_subst_ctx(&ctx->subst, true);
  reset_renaming(&ctx->rename);
  ctx->hash = NULL;
}


/*
 * Extend the renaming:
 * - replace variables in v[0 ... n-1] by n fresh variables.
 */
void renaming_ctx_push_vars(renaming_ctx_t *ctx, uint32_t n, term_t *v) {
  uint32_t i;
  term_t x, y;

  for (i=0; i<n; i++) {
    x = v[i];
    y = get_var_renaming(&ctx->rename, x); // x is now renamed to y
    subst_ctx_push_binding(&ctx->subst, x, y);
  }

  ctx->hash = NULL;
}


/*
 * Remove the last n variable renamings
 */
void renaming_ctx_pop_vars(renaming_ctx_t *ctx, uint32_t n) {
  ctx_binding_t *b;
  uint32_t i, m;

  assert(n <= ctx->subst.nelems);

  // clear the last n variable renamings in ctx->renaming
  b = ctx->subst.data;
  i = ctx->subst.nelems;
  m = i - n;
  while (i > m) {
    i --;
    clear_var_renaming(&ctx->rename, b[i].var);
  }

  // remove the last n bindings in ctx->subst
  subst_ctx_pop_bindings(&ctx->subst, n);

  ctx->hash = NULL;
}


/*
 * Hash code of the current renaming
 */
harray_t *renaming_ctx_hash(renaming_ctx_t *ctx) {
  harray_t *tmp;

  tmp = ctx->hash;
  if (tmp == NULL) {
    tmp = subst_ctx_hash(&ctx->subst);
    ctx->hash = tmp;
  }

  return tmp;
}
