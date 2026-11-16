/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * SUPPORT FOR QUANTIFIERS
 */

#include "context/quant_context.h"

/*
 * Create the quant solver and attach it to the egraph
 */
void create_quant_solver(context_t *ctx) {
  quant_solver_t *solver;

  assert(ctx->egraph != NULL && ctx->quant_solver == NULL);

  solver = (quant_solver_t *) safe_malloc(sizeof(quant_solver_t));
  init_quant_solver(solver, ctx->core, &ctx->gate_manager, ctx->egraph, ctx->types);
  egraph_attach_quantsolver(ctx->egraph, solver, quant_solver_ctrl_interface(solver),
                          quant_solver_egraph_interface(solver),
                          quant_solver_quant_egraph_interface(solver));

  ctx->quant_solver = solver;
}

/*
 * Attach problem to quant solver
 */
void context_attach_quant_prob(context_t *ctx, ef_prob_t *prob) {
  assert(ctx->egraph != NULL && ctx->quant_solver != NULL);

  quant_solver_attach_prob(ctx->quant_solver, prob, ctx);
}


