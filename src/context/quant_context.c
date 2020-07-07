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

  quant_solver_attach_prob(ctx->quant_solver, prob);
}


