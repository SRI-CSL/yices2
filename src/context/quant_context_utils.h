/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * CONTEXT UTILITIES FOR QUANTIFIERS
 */

#ifndef __QUANT_CONTEXT_UTILS_H
#define __QUANT_CONTEXT_UTILS_H

#include "context/context.h"


/*
 * Enable quant flag to allow adding quantifier instances
 */
extern void context_enable_quant(context_t *ctx);


/*
 * Disable quant flag to allow adding quantifier instances
 */
extern void context_disable_quant(context_t *ctx);


/*
 * Assert toplevel instance formula t:
 * - t is a boolean term (or the negation of a boolean term)
 */
extern void quant_assert_toplevel_formula(context_t *ctx, term_t t);




#endif /* __QUANT_CONTEXT_UTILS_H */
