/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2018 SRI International.
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
 * WRAPPER FOR A SAT SOLVER OTHER THEN THE SMT_CORE
 */

#ifndef __DELEGATE_H
#define __DELEGATE_H

#include <stdbool.h>
#include <stdint.h>

#include "solvers/cdcl/smt_core.h"
#include "utils/int_vectors.h"
#include "yices_types.h"


/*
 * For bitvector and purely propositional problems, we want to
 * experiment with third-party sat solvers. The simplest way is
 * to let the bvsolver + smt core do bit-blasting (i.e., produce
 * a CNF formula) then call a sat solver on that CNF.
 *
 * To access the external solver, we assume the following API
 * - add_empty_clause()
 * - add_unit_clause(literal_t l)
 * - add_binary_clause(literal_t l1, literal_t l2)
 * - add_ternary_clause(literal_t l1, literal_t l2, literal_t l3)
 * - add_clause(n: clause size, literal_t array_of_literals[])
 * - check()
 * - get_value(int v): value of a boolean variable v
 * - set_verbosity(int level): set verbosity lvel
 * - delete()
 */
typedef void (*add_empty_clause_fun_t)(void *solver);
typedef void (*add_unit_clause_fun_t)(void *solver, literal_t l);
typedef void (*add_binary_clause_fun_t)(void *solver, literal_t l1, literal_t l2);
typedef void (*add_ternary_clause_fun_t)(void *solver, literal_t l1, literal_t l2, literal_t l3);
typedef void (*add_clause_fun_t)(void *solver, uint32_t n, literal_t *a);
typedef smt_status_t (*check_fun_t)(void *solver);
typedef bval_t (*get_value_fun_t)(void *solver, bvar_t x);
typedef void (*set_verbosity_fun_t)(void *solver, uint32_t level);
typedef void (*delete_fun_t)(void *solver);

typedef struct delegate_s {
  void *solver;     // pointer to the sat solver
  ivector_t buffer; // to make copy of clauses
  add_empty_clause_fun_t add_empty_clause;
  add_unit_clause_fun_t add_unit_clause;
  add_binary_clause_fun_t add_binary_clause;
  add_ternary_clause_fun_t add_ternary_clause;
  add_clause_fun_t add_clause;
  check_fun_t check;
  get_value_fun_t get_value;
  set_verbosity_fun_t set_verbosity;
  delete_fun_t delete;
} delegate_t;


/*
 * Create and initialize a delegate structure
 * - solver_name specifies the external solver to use
 * - nvars = number of variables
 * - return true if that worked, false is the solver_name is not supported
 *   or if something else goes wrong.
 * - allowed values for solver_name: TBD
 */
extern bool init_delegate(delegate_t *delegate, const char *solver_name, uint32_t nvars);

/*
 * Delete the solver and free memory
 */
extern void delete_delegate(delegate_t *delegate);

/*
 * Export the clauses from core to the delegate
 * then check satsfiability:
 * - return STATUS_SAT/STATUS_UNSAT if that works
 * - return STATUS_UNKNOWN if the delegate fails
 */
extern smt_status_t solve_with_delegate(delegate_t *delegate, smt_core_t *core);

/*
 * Value assigned to variable x in the delegate
 */
extern bval_t delegate_get_value(delegate_t *delegate, bvar_t x);

/*
 * Set verbosity level for the delegate
 */
extern void delegate_set_verbosity(delegate_t *delegate, uint32_t level);


#endif /* __DELEGATE_H */
