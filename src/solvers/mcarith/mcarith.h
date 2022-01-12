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

#ifndef __MCARITH_H
#define __MCARITH_H

#include <context/context_types.h>
//#include <solvers/cdcl/gates_manager.h>
//#include <solvers/cdcl/smt_core.h>
//#include <solvers/egraph/egraph_types.h>

typedef struct mcarith_solver_s mcarith_solver_t;

/*
 * Initialize the mcarith solver.
 * - core = the attached smt-core object
 * - gates = the gate manager for core
 * - egraph = the attached egraph (or NULL)
 *
 * Default settings:
 * - no row saving, no jump buffer (exceptions cause abort)
 */
extern void init_mcarith_solver(mcarith_solver_t **solver, context_t* ctx);

/*
 * Enable row saving (to support push/pop/multiple checks)
 * - must be done before any assertions
 */
void mcarith_enable_row_saving(mcarith_solver_t *solver);

/**
 *
 */
extern void destroy_mcarith_solver(mcarith_solver_t* solver);

/*
 * Get the internalization interface descriptor
 */
extern arith_interface_t *mcarith_arith_interface(mcarith_solver_t *solver);

/*
 * Get the solver descriptors
 */
extern th_ctrl_interface_t *mcarith_ctrl_interface(mcarith_solver_t *solver);
extern th_smt_interface_t *mcarith_smt_interface(mcarith_solver_t *solver);

/*
 * Get the egraph interface descriptors
 */
extern th_egraph_interface_t *mcarith_egraph_interface(mcarith_solver_t *solver);
extern arith_egraph_interface_t *mcarith_arith_egraph_interface(mcarith_solver_t *solver);


#endif