/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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

