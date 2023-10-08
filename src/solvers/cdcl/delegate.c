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
#include <stdio.h>

#ifdef HAVE_CADICAL
#include "ccadical.h"
#endif

#ifdef HAVE_CRYPTOMINISAT
#include "cryptominisat5/cmsat_c.h"
#endif

#ifdef HAVE_KISSAT
#include "kissat.h"
#endif

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
  // use new sat solver
  switch (nsat_solve(solver)) {
  case STAT_SAT: return SMT_STATUS_SAT;
  case STAT_UNSAT: return SMT_STATUS_UNSAT;
  default: return SMT_STATUS_UNKNOWN;
  }
}

static smt_status_t ysat_preprocess(void *solver) {
  // use new sat solver
  switch (nsat_apply_preprocessing(solver)) {
  case STAT_SAT: return SMT_STATUS_SAT;
  case STAT_UNSAT: return SMT_STATUS_UNSAT;
  default: return SMT_STATUS_UNKNOWN;
  }
}

static void ysat_export_to_dimacs(void *solver, FILE *f) {
  nsat_export_to_dimacs(f, solver);
}

static bval_t ysat_get_value(void *solver, bvar_t x) {
  return var_value(solver, x);
}

static void ysat_set_verbosity(void *solver, uint32_t level) {
  nsat_set_verbosity(solver, level);
}

static void ysat_delete(void *solver) {
  delete_nsat_solver(solver);
  safe_free(solver);
}

#if 0
static void ysat_keep_var(void *solver, bvar_t x) {
  nsat_solver_keep_var(solver, x);
}
#endif

#define USE_CUTS 1

#if USE_CUTS
static void ysat_var_def2(void *solver, bvar_t x, uint32_t b, literal_t l1, literal_t l2) {
  nsat_solver_add_def2(solver, x, b, l1, l2);
}

static void ysat_var_def3(void *solver, bvar_t x, uint32_t b, literal_t l1, literal_t l2, literal_t l3) {
  nsat_solver_add_def3(solver, x, b, l1, l2, l3);
}
#endif

static void ysat_as_delegate(delegate_t *d, uint32_t nvars) {
  d->solver = (sat_solver_t *) safe_malloc(sizeof(sat_solver_t));
  init_nsat_solver(d->solver, nvars, true); // with preprocessing
  // init_nsat_solver(d->solver, nvars, false); // without preprocessing
  nsat_set_randomness(d->solver, 0.01);
  nsat_set_reduce_fraction(d->solver, 12);
  nsat_set_res_clause_limit(d->solver, 300);   // more agressive var elimination
  nsat_set_res_extra(d->solver, 20);
  nsat_set_simplify_subst_delta(d->solver, 30);
  nsat_solver_add_vars(d->solver, nvars);
  //
  init_ivector(&d->buffer, 0);
  d->add_empty_clause = ysat_add_empty_clause;
  d->add_unit_clause = ysat_add_unit_clause;
  d->add_binary_clause = ysat_add_binary_clause;
  d->add_ternary_clause = ysat_add_ternary_clause;
  d->add_clause = ysat_add_clause;
  d->check = ysat_check;
  d->get_value = ysat_get_value;
  d->set_verbosity = ysat_set_verbosity;
  d->delete = ysat_delete;

  // experimental
  //  d->keep_var = ysat_keep_var;
  d->keep_var = NULL; // don't use

#if USE_CUTS
  // with cut enumeration
  d->var_def2 = ysat_var_def2;
  d->var_def3 = ysat_var_def3;
#else
  // without
  d->var_def2 = NULL;
  d->var_def3 = NULL;
#endif
  // more experimental functions
  d->preprocess = ysat_preprocess;
  d->export = ysat_export_to_dimacs;
}


#if HAVE_CADICAL || HAVE_KISSAT
/*
 * Conversion from literal_t to dimacs:
 * - in Yices, variables are indexed from 0 to nvars-1.
 *   variable x has two literals: pos_lit(x) = 2x and neg_lit(x) = 2x + 1
 *   variable 0 is special: pos_lit(0) is true_literal, neg_lit(0) is false_literal.
 * - in Dimacs, variables are indexed from 1 to nvars
 *   variable x has two literal: pos_lit(x) = +x and neg_lit(x) = -x
 *   0 is a terminator (end of clause).
 */
static inline int lit2dimacs(literal_t l) {
  int x = var_of(l) + 1;
  return is_pos(l) ? x : - x;
}
#endif

/*
 * WRAPPERS FOR CADICAL
 */

#if HAVE_CADICAL
static void cadical_add_empty_clause(void *solver) {
  ccadical_add(solver, 0);
}

static void cadical_add_unit_clause(void *solver, literal_t l) {
  ccadical_add(solver, lit2dimacs(l));
  ccadical_add(solver, 0);
}

static void cadical_add_binary_clause(void *solver, literal_t l1, literal_t l2) {
  ccadical_add(solver, lit2dimacs(l1));
  ccadical_add(solver, lit2dimacs(l2));
  ccadical_add(solver, 0);
}

static void cadical_add_ternary_clause(void *solver, literal_t l1, literal_t l2, literal_t l3) {
  ccadical_add(solver, lit2dimacs(l1));
  ccadical_add(solver, lit2dimacs(l2));
  ccadical_add(solver, lit2dimacs(l3));
  ccadical_add(solver, 0);
}

static void cadical_add_clause(void *solver, uint32_t n, literal_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    ccadical_add(solver, lit2dimacs(a[i]));
  }
  ccadical_add(solver, 0);
}

static smt_status_t cadical_check(void *solver) {
  switch (ccadical_sat(solver)) {
  case 10: return SMT_STATUS_SAT;
  case 20: return SMT_STATUS_UNSAT;
  default: return SMT_STATUS_UNKNOWN;
  }
}


/*
 * Important: the rest of Yices (including the bit-vector solver)
 * assumes that the backend SAT solver assign a value to all variables.
 * cadical does not do this. It may return that variable x has
 * value "unknown". This means that 'x' does not occur in any clause
 * sent to cadical.
 * We convert  unknown to VAL_FALSE here.
 */
static bval_t cadical_get_value(void *solver, bvar_t x) {
  int v;

  v = ccadical_deref(solver, x + 1); // x+1 = variable in cadical = positive literal
  // v = value assigned in cadical: -1 means false, +1 means true, 0 means unknown

  return (v <= 0) ? VAL_FALSE : VAL_TRUE;
}

static void cadical_set_verbosity(void *solver, uint32_t level) {
  // verbosity 0 --> nothing (quiet = true)
  // verbosity 1 --> normal cadical output (quiet = false)
  // verbosity 2 --> cadical verbosity 1
  // verbosity 3 --> cadical verbosity 2
  //
  // With cadical 1.2.0:
  // - we must set option 'report' to true otherwise
  //   nothing is printed at verbosity level < 2
  // 
  if (level == 0) {
    ccadical_set_option(solver, "quiet", 1);
  } else {
    ccadical_set_option(solver, "quiet", 0);
    ccadical_set_option(solver, "report", 1);
    if (level == 2) {
      ccadical_set_option(solver, "verbose", 1);
    } else if (level >= 3) {
      ccadical_set_option(solver, "verbose", 2);
    }
  }
}

static void cadical_delete(void *solver) {
  ccadical_reset(solver);
}

static void cadical_as_delegate(delegate_t *d, uint32_t nvars) {
  d->solver = ccadical_init();
  ccadical_set_option(d->solver, "quiet", 1); // no output from cadical by default
  init_ivector(&d->buffer, 0); // not used
  // fine tuning
  ccadical_set_option(d->solver, "walk", 0);
  ccadical_set_option(d->solver, "lucky", 0);
  ccadical_set_option(d->solver, "chrono", 0);
  ccadical_set_option(d->solver, "elimands", 0);
  //  ccadical_set_option(d->solver, "elimequivs", 0);
  ccadical_set_option(d->solver, "elimites", 0);
  ccadical_set_option(d->solver, "elimxors", 0);
  // end of fine tuning
  d->add_empty_clause = cadical_add_empty_clause;
  d->add_unit_clause = cadical_add_unit_clause;
  d->add_binary_clause = cadical_add_binary_clause;
  d->add_ternary_clause = cadical_add_ternary_clause;
  d->add_clause = cadical_add_clause;
  d->check = cadical_check;
  d->get_value = cadical_get_value;
  d->set_verbosity = cadical_set_verbosity;
  d->delete = cadical_delete;
  d->keep_var = NULL;
  d->var_def2 = NULL;
  d->var_def3 = NULL;
  d->preprocess = NULL;
  d->export = NULL;
}

#endif



/*
 * WRAPPERS FOR CRYPTOMINISAT
 */

#if HAVE_CRYPTOMINISAT
static void cryptominisat_add_empty_clause(void *solver) {
  cmsat_add_clause(solver, NULL, 0);
}

static void cryptominisat_add_unit_clause(void *solver, literal_t l) {
  uint32_t c[1];

  assert(l >= 0);
  c[0] = l;
  cmsat_add_clause(solver, c, 1);
}

static void cryptominisat_add_binary_clause(void *solver, literal_t l1, literal_t l2) {
  uint32_t c[2];

  assert(l1 >= 0 && l2 >= 0);
  c[0] = l1;
  c[1] = l2;
  cmsat_add_clause(solver, c, 2);
}

static void cryptominisat_add_ternary_clause(void *solver, literal_t l1, literal_t l2, literal_t l3) {
  uint32_t c[3];

  assert(l1 >= 0 && l2 >= 0 && l3 >= 0);
  c[0] = l1;
  c[1] = l2;
  c[2] = l3;
  cmsat_add_clause(solver, c, 3);
}

static void cryptominisat_add_clause(void *solver, uint32_t n, literal_t *a) {
  cmsat_add_clause(solver, (uint32_t*) a, n);
}

static smt_status_t cryptominisat_check(void *solver) {
  switch (cmsat_solve(solver)) {
  case CMSAT_SAT: return SMT_STATUS_SAT;
  case CMSAT_UNSAT: return SMT_STATUS_UNSAT;
  default: return SMT_STATUS_UNKNOWN;
  }
}


/*
 * We convert  unknown to VAL_FALSE here to be safe, but it seems
 * that cryptominisat always produces a full truth assignment.
 */
static bval_t cryptominisat_get_value(void *solver, bvar_t x) {
  switch (cmsat_var_value(solver, x)) {
  case CMSAT_VAL_TRUE:
    return VAL_TRUE;

  case CMSAT_VAL_FALSE:
  default:
    return VAL_FALSE;
  }
}

static void cryptominisat_set_verbosity(void *solver, uint32_t level) {
  // verbosity 0 --> quiet (this is the default)
  cmsat_set_verbosity(solver, level);
}

static void cryptominisat_delete(void *solver) {
  cmsat_free_solver(solver);
}

static void cryptominisat_as_delegate(delegate_t *d, uint32_t nvars) {
  d->solver = cmsat_new_solver();
  cmsat_new_vars(d->solver, nvars);
  init_ivector(&d->buffer, 0); // not used
  d->add_empty_clause = cryptominisat_add_empty_clause;
  d->add_unit_clause = cryptominisat_add_unit_clause;
  d->add_binary_clause = cryptominisat_add_binary_clause;
  d->add_ternary_clause = cryptominisat_add_ternary_clause;
  d->add_clause = cryptominisat_add_clause;
  d->check = cryptominisat_check;
  d->get_value = cryptominisat_get_value;
  d->set_verbosity = cryptominisat_set_verbosity;
  d->delete = cryptominisat_delete;
  d->keep_var = NULL;
  d->var_def2 = NULL;
  d->var_def3 = NULL;
  d->preprocess = NULL;
  d->export = NULL;
}

#endif


/*
 * WRAPPERS FOR KISSAT
 */
#if HAVE_KISSAT
static void kissat_add_empty_clause(void *solver) {
  kissat_add(solver, 0);
}

static void kissat_add_unit_clause(void *solver, literal_t l) {
  kissat_add(solver, lit2dimacs(l));
  kissat_add(solver, 0);
}

static void kissat_add_binary_clause(void *solver, literal_t l1, literal_t l2) {
  kissat_add(solver, lit2dimacs(l1));
  kissat_add(solver, lit2dimacs(l2));
  kissat_add(solver, 0);
}

static void kissat_add_ternary_clause(void *solver, literal_t l1, literal_t l2, literal_t l3) {
  kissat_add(solver, lit2dimacs(l1));
  kissat_add(solver, lit2dimacs(l2));
  kissat_add(solver, lit2dimacs(l3));
  kissat_add(solver, 0);
}

static void kissat_add_clause(void *solver, uint32_t n, literal_t *a) {
  uint32_t i;

  for (i=0; i<n; i++) {
    kissat_add(solver, lit2dimacs(a[i]));
  }
  kissat_add(solver, 0);
}

static smt_status_t kissat_check(void *solver) {
  switch (kissat_solve(solver)) {
  case 10: return SMT_STATUS_SAT;
  case 20: return SMT_STATUS_UNSAT;
  default: return SMT_STATUS_UNKNOWN;
  }
}


/*
 * Important: the rest of Yices (including the bit-vector solver)
 * assumes that the backend SAT solver assign a value to all variables.
 * kissat does not do this. It may return that variable x has
 * value "unknown". This means that 'x' does not occur in any clause
 * sent to kissat.
 * We convert  unknown to VAL_FALSE here.
 */
static bval_t kissat_get_value(void *solver, bvar_t x) {
  int v;

  v = kissat_value(solver, x + 1); // x+1 = variable in kissat = positive literal
  // v = value assigned in kissat: -1 means false, +1 means true, 0 means unknown

  return (v <= 0) ? VAL_FALSE : VAL_TRUE;
}

static void kissat_set_verbosity(void *solver, uint32_t level) {
  // verbosity 0 --> nothing (quiet = true)
  // verbosity 1 --> normal kissat output (quiet = false)
  // verbosity 2 --> kissat verbosity 1
  // verbosity 3 --> kissat verbosity 2
  if (level == 0) {
    kissat_set_option(solver, "quiet", 1);
  } else {
    kissat_set_option(solver, "quiet", 0);
    if (level == 2) {
      kissat_set_option(solver, "verbose", 1);
    } else if (level >= 3) {
      kissat_set_option(solver, "verbose", 2);
    }
  }
}

static void kissat_delete(void *solver) {
  kissat_release(solver);
}

static void kissat_as_delegate(delegate_t *d, uint32_t nvars) {
  d->solver = kissat_init();
  kissat_set_option(d->solver, "quiet", 1); // no output from kissat by default
  init_ivector(&d->buffer, 0); // not used
  d->add_empty_clause = kissat_add_empty_clause;
  d->add_unit_clause = kissat_add_unit_clause;
  d->add_binary_clause = kissat_add_binary_clause;
  d->add_ternary_clause = kissat_add_ternary_clause;
  d->add_clause = kissat_add_clause;
  d->check = kissat_check;
  d->get_value = kissat_get_value;
  d->set_verbosity = kissat_set_verbosity;
  d->delete = kissat_delete;
  d->keep_var = NULL;
  d->var_def2 = NULL;
  d->var_def3 = NULL;
  d->preprocess = NULL;
  d->export = NULL;
}

#endif


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
#if HAVE_CADICAL
  } else if (strcmp("cadical", solver_name) == 0) {
    cadical_as_delegate(d, nvars);
    return true;
#endif
#if HAVE_CRYPTOMINISAT
  } else if (strcmp("cryptominisat", solver_name) == 0) {
    cryptominisat_as_delegate(d, nvars);
    return true;
#endif
#if HAVE_KISSAT
  } else if (strcmp("kissat", solver_name) == 0) {
    kissat_as_delegate(d, nvars);
    return true;
#endif
  }
  return false;
}



/*
 * Test whether a solver is known and supported.
 * - solver_name = external solver to use
 * - return true if this solver is supported (i.e., can be used in init_delegate).
 * - return false otherwise.
 * - extra information is returned in *unknown:
 *   if we don't support the solver at all, *unknown is set to true
 *   if we have optional support (but not compiled), *unknown is set to fasle.
 */
bool supported_delegate(const char *solver_name, bool *unknown) {
  if (strcmp("y2sat", solver_name) == 0) {
    *unknown = false;
    return true;
  }

  if (strcmp("cadical", solver_name) == 0) {
    *unknown = false;
#if HAVE_CADICAL
    return true;
#else
    return false;
#endif
  }

  if (strcmp("cryptominisat", solver_name) == 0) {
    *unknown = false;
#if HAVE_CRYPTOMINISAT
    return true;
#else
    return false;
#endif
  }

  if (strcmp("kissat", solver_name) == 0) {
    *unknown = false;
#if HAVE_KISSAT
    return true;
#else
    return false;
#endif
  }

  *unknown = true;
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
 * Transfer unit clauses from core to delegate
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
 * Mark all variables with atoms as variables to keep
 */
static void mark_atom_variables(delegate_t *d, smt_core_t *core) {
  uint32_t x, n;

  n = num_vars(core);
  for (x=0; x<n; x++) {
    if (bvar_has_atom(core, x)) {
      d->keep_var(d->solver, x);
    }
  }
}


/*
 * Process a gate definition g
 */
// definition l := f(l1, l2)
static void add_binary_gate(delegate_t *d, uint32_t b, literal_t l, literal_t l1, literal_t l2) {
  bvar_t x;

  // normalize to a positive l
  // l can be true_literal or false_literal, in which case we skip this gate
  x = var_of(l);
  if (x != const_bvar) {
    if (is_neg(l)) { b = ~b; }
    d->var_def2(d->solver, x, b, l1, l2);
  }
}

// definition l := f(l1, l2, l3)
static void add_ternary_gate(delegate_t *d, uint32_t b, literal_t l, literal_t l1, literal_t l2, literal_t l3) {
  bvar_t x;

  // normalize to a positive l
  // l can be true_literal or false_literal, in which case we skip this gate
  x = var_of(l);
  if (x != const_bvar) {
    if (is_neg(l)) { b = ~b; }
    d->var_def3(d->solver, x, b, l1, l2, l3);
  }
}

static void export_gate(delegate_t *d, const boolgate_t *g) {
  uint32_t n;

  switch (tag_combinator(g->tag)) {
  case XOR_GATE:
    assert(tag_outdegree(g->tag) == 1);
    n = tag_indegree(g->tag);
    if (n == 2) {
      // output is g->lit[2], inputs are g->lit[0] and g->lit[1]
      add_binary_gate(d, 0x3c, g->lit[2], g->lit[0], g->lit[1]);
    } else if (n == 3) {
      // output is g->lit[3], inputs are g->lit[0 .. 2]
      add_ternary_gate(d, 0x96, g->lit[3], g->lit[0], g->lit[1], g->lit[2]);
    }
    break;

  case OR_GATE:
    assert(tag_outdegree(g->tag) == 1);
    n = tag_indegree(g->tag);
    if (n == 2) {
      // output is g->lit[2], inputs are g->lit[0] and g->lit[1]
      add_binary_gate(d, 0xfc, g->lit[2], g->lit[0], g->lit[1]);
    } else if (n == 3) {
      // output is g->lit[3], inputs are g->lit[0 .. 2]
      add_ternary_gate(d, 0xfe, g->lit[3], g->lit[0], g->lit[1], g->lit[2]);
    }
    break;

  case ITE_GATE:
    assert(tag_indegree(g->tag) == 3 && tag_outdegree(g->tag) == 1);
     add_ternary_gate(d, 0xca, g->lit[3], g->lit[0], g->lit[1], g->lit[2]);
    break;

  case CMP_GATE:
    assert(tag_indegree(g->tag) == 3 && tag_outdegree(g->tag) == 1);
    add_ternary_gate(d, 0xb2, g->lit[3], g->lit[0], g->lit[1], g->lit[2]);
    break;

  case HALFADD_GATE:
    assert(tag_indegree(g->tag) == 2 && tag_outdegree(g->tag) == 2);
    // g->lit[2] = (xor g->lit[0] g->lit[1])
    // g->lit[3] = (and g->lit[0] g->lit[1])
    add_binary_gate(d, 0x3c, g->lit[2], g->lit[0], g->lit[1]);
    add_binary_gate(d, 0xc0, g->lit[3], g->lit[0], g->lit[1]);
    break;

   case FULLADD_GATE:
    // g->lit[3] = (xor g->lit[0] g->lit[1] g->lit[2])
    // g->lit[4] = (maj g->lit[0] g->lit[1] g->lit[2])
    assert(tag_indegree(g->tag) == 3 && tag_outdegree(g->tag) == 2);
    add_ternary_gate(d, 0x96, g->lit[3], g->lit[0], g->lit[1], g->lit[2]);
    add_ternary_gate(d, 0xe8, g->lit[4], g->lit[0], g->lit[1], g->lit[2]);
    break;
  }
}

extern void show_all_var_defs(const sat_solver_t *solver);

/*
 * Export gate definitions from the core to the sat solver
 */
static void export_gate_definitions(delegate_t *d, smt_core_t *core) {
  gate_table_t *gates;
  boolgate_t *g;
  uint32_t scan_index;

  gates = get_gate_table(core);

  scan_index = 0;
  g = gate_table_next(gates, &scan_index);
  while (g != NULL) {
    export_gate(d, g);
    g = gate_table_next(gates, &scan_index);
  }

  //  show_all_var_defs(d->solver);
}

/*
 * Copy all clauses of core to a delegate d then call the delegate's solver
 */
smt_status_t solve_with_delegate(delegate_t *d, smt_core_t *core) {
  copy_problem_clauses(d, core);
  if (d->keep_var != NULL) {
    mark_atom_variables(d, core);
  }
  if (d->var_def2 != NULL && d->var_def3 != NULL) {
    export_gate_definitions(d, core);
  }
  return d->check(d->solver);
}


/*
 * Copy all the clauses of core to delegate d then call the delegate's preprocessor
 */
smt_status_t preprocess_with_delegate(delegate_t *d, smt_core_t *core) {
  if (d->preprocess == NULL) return SMT_STATUS_UNKNOWN; // not supported

  copy_problem_clauses(d, core);
  if (d->keep_var != NULL) {
    mark_atom_variables(d, core);
  }
  if (d->var_def2 != NULL && d->var_def3 != NULL) {
    export_gate_definitions(d, core);
  }
  return d->preprocess(d->solver);
}


/*
 * Export to DIMACS (do nothing if that's not supported by the delegate)
 */
void export_to_dimacs_with_delegate(delegate_t *d, FILE *f) {
  if (d->export != NULL) {
    d->export(d->solver, f);
  }
}


/*
 * Value assigned to variable x in the delegate
 */
bval_t delegate_get_value(delegate_t *d, bvar_t x) {
  return d->get_value(d->solver, x);
}

/*
 * Set verbosity level
 */
void delegate_set_verbosity(delegate_t *d, uint32_t level) {
  d->set_verbosity(d->solver, level);
}
