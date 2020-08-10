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
 * CONTEXT UTILITIES FOR QUANTIFIERS
 */

#include "context/quant_context_utils.h"
#include "context/context_simplifier.h"
#include "context/context_utils.h"
#include "context/internalization_codes.h"
#include "context/ite_flattener.h"
#include "terms/term_utils.h"
#include "utils/memalloc.h"

#include "api/yices_globals.h"

#define TRACE 0


/*
 * Enable quant flag to allow adding quantifier instances
 */
void context_enable_quant(context_t *ctx) {
  assert(!context_quant_enabled(ctx));
  ctx->en_quant = true;
}


/*
 * Disable quant flag to allow adding quantifier instances
 */
void context_disable_quant(context_t *ctx) {
  assert(context_quant_enabled(ctx));
  ctx->en_quant = false;
}

