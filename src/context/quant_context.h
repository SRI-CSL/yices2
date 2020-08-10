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
