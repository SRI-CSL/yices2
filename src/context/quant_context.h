/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * SUPPORT FOR QUANTIFIERS
 */

#ifndef __QUANT_CONTEXT_H
#define __QUANT_CONTEXT_H

#include "context/quant_context_utils.h"
#include "solvers/quant/quant_solver.h"


/*
 * Create the quant solver and attach it to the egraph
 */
extern void create_quant_solver(context_t *ctx);

/*
 * Attach problem to quant solver
 */
extern void context_attach_quant_prob(context_t *ctx, ef_prob_t *prob);



#endif /* __QUANT_CONTEXT_H */
