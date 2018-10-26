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

#include <assert.h>
#include <string.h>

#include "solvers/cdcl/delegate.h"
#include "solvers/cdcl/new_sat_solver.h"
#include "utils/memalloc.h"



/*
 * WRAPPERS FOR THE YICES SAT_SOLVER
 */

static void ysat_add_empty_clause(void *solver) {
  nsat_solver_simplify_and_add_clause(solver, 0, NULL);
}

static void ysat_add_unit_clause(void *solver, literal_t l) {
  nsat_solver_simplify_and_add_clause(solver, 1, &l);
}

static void ysat_add_binary_clause(void *solver, literal_t l1, literal_t l2) {
  literal_t a[2];

  a[0] = l1;
  a[1] = l2;
  nsat_solver_simplify_and_add_clause(solver, 2, a);
}

static void ysat_add_ternary_clause(void *solver, literal_t l1, literal_t l2, literal_t l3) {
  literal_t a[3];

  a[0] = l1;
  a[1] = l2;
  a[2] = l3;
  nsat_solver_simplify_and_add_clause(solver, 3, a);
}

static void ysat_add_clause(void *solver, uint32_t n, literal_t *a) {
  nsat_solver_simplify_and_add_clause(solver, n, a);
}

static smt_status_t ysat_check(void *solver) {
  switch (nsat_solve(solver)) {
  case STAT_SAT: return STATUS_SAT;
  case STAT_UNSAT: return STATUS_UNSAT;
  default: return STATUS_UNKNOWN;
  }
}

static bval_t ysat_get_value(void *solver, bvar_t x) {
  return var_value(solver, x);
}

static void ysat_delete(void *solver) {
  delete_nsat_solver(solver);
  safe_free(solver);
}

static void ysat_as_delegate(delegate_t *d, uint32_t nvars) {
  d->solver = (sat_solver_t *) safe_malloc(sizeof(sat_solver_t));
  init_nsat_solver(d->solver, nvars, true);
  nsat_solver_add_vars(d->solver, nvars);
  init_ivector(&d->buffer, 0);
  d->add_empty_clause = ysat_add_empty_clause;
  d->add_unit_clause = ysat_add_unit_clause;
  d->add_binary_clause = ysat_add_binary_clause;
  d->add_ternary_clause = ysat_add_ternary_clause;
  d->add_clause = ysat_add_clause;
  d->check = ysat_check;
  d->get_value = ysat_get_value;
  d->delete = ysat_delete;
}


/*
 * Create and initialize a delegate structure
 * - solver_name specifies the external solver to use
 * - nvars = number of variables
 * - return true if that worked, false is the solver_name is not supported
 *   or if something else goes wrong.
 * - allowed values for solver_name: TBD
 */
bool init_delegate(delegate_t *d, const char *solver_name, uint32_t nvars) {
  if (strcmp("y2sat", solver_name) == 0) {
    ysat_as_delegate(d, nvars);
    return true;
  }
  return false;
}

/*
 * Delete the solver and free memory
 */
void delete_delegate(delegate_t *d) {
  d->delete(d->solver);
  delete_ivector(&d->buffer);
  d->solver = NULL;
}


/*
 * NOTE: the copy functions below assume that literals in the core
 * and in the sat_solver use the same encoding:
 * - 0 is true_literal
 *   1 is false_literal
 * - for a boolean variable x:
 *     2x     --> positive literal pos_lit(x)
 *     2x + 1 --> negative literal neg_lit(x)
 *
 * This is OK for y2sat.
 */

/*
 * Tranfer unit clauses from core to delegate
 */
static void copy_unit_clauses(delegate_t *d, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;

  d->add_unit_clause(d->solver, true_literal); // CHECK THIS

  n = core->nb_unit_clauses;
  stack = &core->stack;
  for (i=0; i<n; i++) {
    d->add_unit_clause(d->solver, stack->lit[i]);
  }
}

/*
 * Transfer binary clauses
 */
static void copy_binary_clauses(delegate_t *d, smt_core_t *core) {
  int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = core->nlits;
  for (l1=0; l1<n; l1++) {
    bin = core->bin[l1];
    if (bin != NULL) {
      for (;;) {
        l2 = *bin ++;
        if (l2 < 0) break;
        if (l1 <= l2) {
          d->add_binary_clause(d->solver, l1, l2);
        }
      }
    }
  }
}

/*
 * Copy one clause c:
 * - we make an intermediate copy in d->vector in case the 
 *   SAT solver modifies the input array
 */
static void copy_clause(delegate_t *d, const clause_t *c) {
  uint32_t i;
  literal_t l;
  
  ivector_reset(&d->buffer);
  i = 0;
  l = c->cl[0];
  while (l >= 0) {
    ivector_push(&d->buffer, l);
    i ++;
    l = c->cl[i];
  }
  d->add_clause(d->solver, d->buffer.size, d->buffer.data);
}

/*
 * Copy the clauses from a vector
 */
static void copy_clause_vector(delegate_t *d, clause_t **vector) {
  uint32_t i, n;

  if (vector != NULL) {
    n = get_cv_size(vector);
    for (i=0; i<n; i++) {
      copy_clause(d, vector[i]);
    }
  }
}

/*
 * Copy all the problem clauses from core to d
 */
static void copy_problem_clauses(delegate_t *d, smt_core_t *core) {
  if (core->inconsistent) {
    d->add_empty_clause(d->solver);
  }
  copy_unit_clauses(d, core);
  copy_binary_clauses(d, core);
  copy_clause_vector(d, core->problem_clauses);
}


/*
 * Copy all clauses of core to a delegate d then call the delegate's solver
 */
smt_status_t solve_with_delegate(delegate_t *d, smt_core_t *core) {
  copy_problem_clauses(d, core);
  return d->check(d->solver);
}
