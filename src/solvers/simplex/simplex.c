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
 * SIMPLEX SOLVER
 *
 * Version 3: started 2008/11/03
 */

#include <inttypes.h>

#include "io/tracer.h"
#include "solvers/egraph/theory_explanations.h"
#include "solvers/simplex/integrality_constraints.h"
#include "solvers/simplex/simplex.h"
#include "terms/rational_hash_maps.h"
#include "utils/assert_utils.h"
#include "utils/bitvectors.h"
#include "utils/dep_tables.h"
#include "utils/dprng.h"
#include "utils/hash_functions.h"
#include "utils/int_hash_classes.h"


/*
 * To enable general trace, set TRACE to 1
 * To enable the debugging code, set DEBUG to 1
 * To dump the initial tableau, set DUMP to 1
 *
 * To trace simplifications and tableau initialization set TRACE_INIT to 1
 * To trace the theory propagation set TRACE_PROPAGATION to 1 (in
 * To trace the branch&bound algorithm set TRACE_BB to 1
 * To get a summary of general solution + bounds: TRACE_INTFEAS to 1
 */
#define TRACE   0
#define DEBUG   0
#define DUMP    0

#define TRACE_INIT 0
#define TRACE_PROPAGATION 0
#define TRACE_BB 0
#define TRACE_INTFEAS 0

#if TRACE || DEBUG || DUMP || TRACE_INIT || TRACE_PROPAGATION || TRACE_BB || TRACE_INTFEAS || !defined(NDEBUG)

#include <stdio.h>

#include "io/term_printer.h"
#include "solvers/simplex/dsolver_printer.h"
#include "solvers/egraph/egraph_printer.h"
#include "solvers/cdcl/gates_printer.h"
#include "solvers/cdcl/smt_core_printer.h"
#include "solvers/simplex/simplex_printer.h"

#endif


/*
 * Debugging functions are defined at the end of this file
 */
#if DUMP

static void print_simplex(FILE *f, simplex_solver_t *solver);
static void dump_state(simplex_solver_t *solver);

#endif


#if DEBUG

static void check_assignment(simplex_solver_t *solver);
static void check_nonbasic_assignment(simplex_solver_t *solver);
static void check_vartags(simplex_solver_t *solver);
static void check_infeasible_vars(simplex_solver_t *solver);
static void check_integer_bounds(simplex_solver_t *solver);
static void check_bound_marks(simplex_solver_t *solver);

static void check_equation_satisfied(simplex_solver_t *solver, uint32_t r);

#endif


#if TRACE

static void show_heap(FILE *f, simplex_solver_t *solver);

#endif



/**********
 *  PRNG  *
 *********/

/*
 * PARAMETERS FOR THE PSEUDO RANDOM NUMBER GENERATOR
 *
 * We  use the same linear congruence as in prng.h,
 * but we use a local implementation so that different
 * solvers can use different seeds.
 */
#define SPLX_PRNG_MULTIPLIER 1664525
#define SPLX_PRNG_CONSTANT   1013904223
#define SPLX_PRNG_SEED       0xabcdef98


/*
 * Return a 32bit unsigned int
 */
static inline uint32_t random_uint32(simplex_solver_t *s) {
  uint32_t x;

  x = s->prng;
  s->prng = x * ((uint32_t) SPLX_PRNG_MULTIPLIER) + ((uint32_t) SPLX_PRNG_CONSTANT);
  return x;
}


/*
 * Return a 32bit integer between 0 and n-1
 * - n must be positive
 */
static inline uint32_t random_uint(simplex_solver_t *s, uint32_t n) {
  assert(n > 0);
  return (random_uint32(s) >> 8) % n;
}




/*************************
 *   BOUND QUEUE/STACK   *
 ************************/

/*
 * Each element i in the stack is an assertion of the form (x <= u) or (x >= l)
 * - x is an arithmetic variable  (stored in var[i])
 * - u or l is an extended rational (of the form a + b\delta) stored in bound[i]
 * - the assertion has an explanation stored in expl[i]
 *   - expl[i].lit = null_literal means that's an axiom (asserted at level 0)
 *   - expl[i].lit = literal l such that atom l is the bound
 *   - expl[i].ptr = array of bound indices that imply bound i (terminated by -1)
 *   - expl[i].v = a pair of variables (v[0], v[1]) if the bound is asserted
 *                 as the result of the egraph propagating v[0] == v[1]
 * - for backtracking, pre[i] stores the previous assertion of the same type,
 *   on the same variable.
 * - bit upper[i] identifies the constraint type: upper[i] = 1 means (x <= u)
 *   upper[i] = 0 means (x >= l)
 *
 * Other components:
 * - top = top of the stack
 * - prop_ptr = index of the first assertion to process for literal propagation
 *   (all bounds of index prop_ptr to top-1 are unprocessed)
 * - fix_ptr = index of the first assertion to process for updating assignments
 *   (all bound of index fix_ptr to top-1 are to be processed)
 * - size = size of all subarrays
 */


/*
 * Initialize the stack
 * - n = initial size
 * All extended rationals in array bounds are initialized
 */
static void init_arith_bstack(arith_bstack_t *stack, uint32_t n) {
  xrational_t *tmp;
  uint32_t i;

  assert(n < MAX_ARITH_BSTACK_SIZE);

  tmp = (xrational_t *) safe_malloc(n * sizeof(xrational_t));
  for (i=0; i<n; i++) {
    xq_init(tmp + i);
  }
  stack->bound = tmp;
  stack->var = (thvar_t *) safe_malloc(n * sizeof(thvar_t));
  stack->expl = (arith_expl_t *) safe_malloc(n * sizeof(arith_expl_t));
  stack->pre = (int32_t *) safe_malloc(n * sizeof(int32_t));
  stack->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));

  stack->top = 0;
  stack->prop_ptr = 0;
  stack->fix_ptr = 0;
  stack->size = n;
}


/*
 * Extend the stack by 50%
 * - initialize all the new extended rationals
 */
static void extend_arith_bstack(arith_bstack_t *stack) {
  xrational_t *tmp;
  uint32_t i ,n;

  n = stack->size + 1;
  n += n>>1;

  if (n >= MAX_ARITH_BSTACK_SIZE) {
    out_of_memory();
  }

  tmp = (xrational_t *) safe_realloc(stack->bound, n * sizeof(xrational_t));
  for (i=stack->size; i<n; i++) {
    xq_init(tmp + i);
  }
  stack->bound = tmp;
  stack->var = (thvar_t *) safe_realloc(stack->var, n * sizeof(thvar_t));
  stack->expl = (arith_expl_t *) safe_realloc(stack->expl, n * sizeof(arith_expl_t));
  stack->pre = (int32_t *) safe_realloc(stack->pre, n * sizeof(int32_t));
  stack->tag = (uint8_t *) safe_realloc(stack->tag, n * sizeof(uint8_t));
  stack->size = n;
}


/*
 * Allocate a new constraint descriptor on top of the stack
 * - return its index
 * - none of the constraint components is initialized
 */
static int32_t arith_bstack_new_constraint(arith_bstack_t *stack) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_arith_bstack(stack);
  }
  assert(i < stack->size);
  stack->top = i+1;
  return i;
}



/*
 * Delete the stack: free all rationals and all allocated arrays
 */
static void delete_arith_bstack(arith_bstack_t *stack) {
  uint32_t i, n;

  n = stack->size;
  for (i=0; i<n; i++) {
    xq_clear(stack->bound + i);
  }

  safe_free(stack->bound);
  safe_free(stack->var);
  safe_free(stack->expl);
  safe_free(stack->pre);
  safe_free(stack->tag);

  stack->bound = NULL;
  stack->var = NULL;
  stack->expl = NULL;
  stack->pre = NULL;
  stack->tag = NULL;
}



/*
 * Empty the stack. Also free all the rationals.
 */
static void reset_arith_bstack(arith_bstack_t *stack) {
  uint32_t i, n;

  n = stack->size;
  for (i=0; i<n; i++) {
    xq_clear(stack->bound + i);
  }

  stack->top = 0;
  stack->prop_ptr = 0;
  stack->fix_ptr = 0;
}



/*
 * Check a constraint's type
 */
static inline bool constraint_is_lower_bound(arith_bstack_t *stack, uint32_t i) {
  assert(i < stack->top);
  return arith_tag_get_type(stack->tag[i]) == ATYPE_LB;
}

static inline bool constraint_is_upper_bound(arith_bstack_t *stack, uint32_t i) {
  assert(i < stack->top);
  return arith_tag_get_type(stack->tag[i]) == ATYPE_UB;
}





/***************************************
 *  ASSERTION STACK/PROPAGATION QUEUE  *
 **************************************/

/*
 * Initialize the stack
 * - n = initial size (must be less than max size)
 */
static void init_arith_astack(arith_astack_t *stack, uint32_t n) {
  assert(n < MAX_ARITH_ASTACK_SIZE);
  stack->size = n;
  stack->top = 0;
  stack->prop_ptr = 0;
  stack->data = (int32_t *) safe_malloc(n * sizeof(int32_t));
}


/*
 * Make the stack 50% larger
 */
static void extend_arith_astack(arith_astack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n >= MAX_ARITH_ASTACK_SIZE) {
    out_of_memory();
  }

  stack->data = (int32_t *) safe_realloc(stack->data, n * sizeof(int32_t));
  stack->size = n;
}


/*
 * Add an assertion a on top of the stack
 */
static void push_assertion(arith_astack_t *stack, int32_t a) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_arith_astack(stack);
  }
  assert(i < stack->size);
  stack->data[i] = a;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static void reset_arith_astack(arith_astack_t *stack) {
  stack->top = 0;
  stack->prop_ptr = 0;
}


/*
 * Delete the stack
 */
static void delete_arith_astack(arith_astack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}



/*
 * Assertion encoding:
 * - an atom is identified by its 32bit index in the atom table
 * - there are no more than UINT32_MAX/16 atoms so atom ids fit in 28bits
 * - an assertion is an atom id + a sign bit packed into 32bits
 * The sign bit is the lower-order bit of the assertion:
 * - sign bit = 0 means atom asserted true
 * - sign bit = 1 means atom asserted false
 *
 * The following functions convert between atom_id+sign and 32bit code
 */
static inline int32_t mk_assertion(int32_t atom_id, uint32_t sign) {
  assert(sign == 0 || sign == 1);
  return (atom_id << 1) | sign;
}

static inline int32_t atom_of_assertion(int32_t a) {
  return a>>1;
}

static inline uint32_t sign_of_assertion(int32_t a) {
  return ((uint32_t) a) & 1;
}

#if DEBUG || TRACE
static inline bool assertion_is_true(int32_t a) {
  return sign_of_assertion(a) == 0;
}
#endif

#if DEBUG
static inline bool assertion_is_false(int32_t a) {
  return sign_of_assertion(a) == 1;
}
#endif



/****************
 *  UNDO STACK  *
 ***************/

/*
 * Initialize: n = initial size
 */
static void init_arith_undo_stack(arith_undo_stack_t *stack, uint32_t n) {
  assert(n < MAX_ARITH_UNDO_STACK_SIZE);

  stack->size = n;
  stack->top = 0;
  stack->data = (arith_undo_record_t *) safe_malloc(n * sizeof(arith_undo_record_t));
}

/*
 * Make the stack 50% larger
 */
static void extend_arith_undo_stack(arith_undo_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n >> 1;
  if (n >= MAX_ARITH_UNDO_STACK_SIZE) {
    out_of_memory();
  }
  stack->size = n;
  stack->data = (arith_undo_record_t *) safe_realloc(stack->data, n * sizeof(arith_undo_record_t));
}


/*
 * Push (n_b, n_a) on top of the stack
 * - n_b = number of bounds in the bstack
 * - n_a = number of assertions in the astack
 */
static void arith_push_undo_record(arith_undo_stack_t *stack, uint32_t n_b, uint32_t n_a) {
  uint32_t i;

  i = stack->top;
  if (i == stack->size) {
    extend_arith_undo_stack(stack);
  }
  assert(i < stack->size);
  stack->data[i].n_bounds = n_b;
  stack->data[i].n_assertions = n_a;
  stack->top = i+1;
}


/*
 * Empty the stack
 */
static void reset_arith_undo_stack(arith_undo_stack_t *stack) {
  stack->top = 0;
}



/*
 * Delete the stack
 */
static void delete_arith_undo_stack(arith_undo_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}





/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * Initialize: initial size = 0
 */
static void init_arith_trail(arith_trail_stack_t *stack) {
  stack->size = 0;
  stack->top = 0;
  stack->data = NULL;
}

/*
 * Save a base-level:
 * - nv = number of variables
 * - na = number of atoms
 * - nr = number of saved rows
 * - pa = propagation pointer in the assertion stack
 * - pb = propagation pointer in the bound stack
 */
static void arith_trail_save(arith_trail_stack_t *stack, uint32_t nv, uint32_t na, uint32_t nr, uint32_t pa, uint32_t pb) {
  uint32_t i, n;

  i = stack->top;
  n = stack->size;
  if (i == n) {
    if (n == 0) {
      n = DEF_SIMPLEX_TRAIL_SIZE;
    } else {
      n += n;
      if (n >= MAX_SIMPLEX_TRAIL_SIZE) {
        out_of_memory();
      }
    }
    stack->data = (arith_trail_t *) safe_realloc(stack->data, n * sizeof(arith_trail_t));
    stack->size = n;
  }
  assert(i < stack->size);

  stack->data[i].nvars = nv;
  stack->data[i].natoms = na;
  stack->data[i].nsaved_rows = nr;
  stack->data[i].bound_ptr = pb;
  stack->data[i].assertion_ptr = pa;

  stack->top = i+1;
}


/*
 * Get the top record
 */
static arith_trail_t *arith_trail_top(arith_trail_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}

/*
 * Remove the top record
 */
static void arith_trail_pop(arith_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}

/*
 * Delete the stack
 */
static void delete_arith_trail(arith_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static void reset_arith_trail(arith_trail_stack_t *stack) {
  stack->top = 0;
}





/*****************
 *  SAVED ROWS   *
 ****************/

/*
 * Delete polynomials in vector *v
 * - n = number of polynomials to keep
 */
static void delete_saved_rows(pvector_t *v, uint32_t n) {
  uint32_t i, k;

  k = v->size;
  assert(n <= k);

  for (i=n; i<k; i++) {
    free_polynomial(v->data[i]);
    v->data[i] = NULL;
  }
  pvector_shrink(v, n);
}


/***********************
 *  STATISTICS RECORD  *
 **********************/

/*
 * Initialize/reset all counters to 0
 */
static void init_simplex_statistics(simplex_stats_t *stat) {
  stat->num_init_vars = 0;
  stat->num_init_rows = 0;
  stat->num_atoms = 0;
  stat->num_elim_candidates = 0;
  stat->num_elim_rows = 0;
  stat->num_simpl_fvars = 0;
  stat->num_simpl_rows = 0;
  stat->num_fixed_vars = 0;
  stat->num_rows = 0;
  stat->num_end_rows = 0;
  stat->num_end_atoms = 0;
  stat->num_binary_lemmas = 0;
  stat->num_prop_lemmas = 0;
  stat->num_props = 0;
  stat->num_bound_props = 0;
  stat->num_prop_expl = 0;
  stat->num_interface_lemmas = 0;
  stat->num_reduced_inter_lemmas = 0;
  stat->num_tricho_lemmas = 0;
  stat->num_reduced_tricho = 0;
  stat->num_make_feasible = 0;
  stat->num_pivots = 0;
  stat->num_blands = 0;
  stat->num_conflicts = 0;

  stat->num_make_intfeasible = 0;
  stat->num_bound_conflicts = 0;
  stat->num_bound_recheck_conflicts = 0;
  stat->num_itest_conflicts = 0;
  stat->num_itest_bound_conflicts = 0;
  stat->num_itest_recheck_conflicts = 0;
  stat->num_dioph_checks = 0;
  stat->num_dioph_gcd_conflicts = 0;
  stat->num_dioph_conflicts = 0;
  stat->num_dioph_bound_conflicts = 0;
  stat->num_dioph_recheck_conflicts = 0;

  stat->num_branch_atoms = 0;
  stat->num_gomory_cuts = 0;
}


static void reset_simplex_statistics(simplex_stats_t *stat) {
  init_simplex_statistics(stat);
}



/**********************
 *  INTERVAL RECORDS  *
 *********************/

/*
 * Initialize the record:
 * - all rationals are zero, no bounds
 * - tag, k_min, k_max are not initialized yet
 */
static void init_interval(interval_t *s) {
  s->has_lb = false;
  s->has_ub = false;
  xq_init(&s->lb);
  xq_init(&s->ub);
  q_init(&s->period);
}


/*
 * Reset all to zero, no bounds
 */
static void reset_interval(interval_t *s) {
  s->has_lb = false;
  s->has_ub = false;
  xq_clear(&s->lb);
  xq_clear(&s->ub);
  q_clear(&s->period);
}


/*
 * Delete: free the rationals
 */
static void delete_interval(interval_t *s) {
  xq_clear(&s->lb);
  xq_clear(&s->ub);
  q_clear(&s->period);
}


/*
 * Update the lower bound to max(s->lb, a)
 */
static void interval_update_lb(interval_t *s, xrational_t *a) {
  if (!s->has_lb || xq_gt(a, &s->lb)) {
    s->has_lb = true;
    xq_set(&s->lb, a);
  }
}


/*
 * Update the upper bound to min(s->lb, a)
 */
static void interval_update_ub(interval_t *s, xrational_t *a) {
  if (!s->has_ub || xq_lt(a, &s->ub)) {
    s->has_ub = true;
    xq_set(&s->ub, a);
  }
}


/*
 * Update the period to LCM(s->period, a)
 * - if s->period is (b/c) and a is (d/e)
 *   then LCM = lcm(b, d)/gcd(c, e)
 * (this is a generalized LCM for rationals)
 */
static void interval_update_period(interval_t *s, rational_t *a) {
  if (q_is_zero(&s->period)) {
    q_set_abs(&s->period, a);
  } else {
    q_generalized_lcm(&s->period, a);
  }
  assert(q_is_pos(&s->period));
}


/*
 * Check whether the interval is reduced to a single point
 */
static bool singleton_interval(interval_t *s) {
  return s->has_ub && s->has_lb && xq_eq(&s->lb, &s->ub);
}


/*
 * Check whether the interval is empty
 */
static bool empty_interval(interval_t *s) {
  return s->has_ub && s->has_lb && xq_gt(&s->lb, &s->ub);
}


#ifndef NDEBUG
/*
 * For debugging: check whether delta is between s->lb and s->ub
 */
static bool sample_in_interval(interval_t *s, rational_t *delta) {
  return (!s->has_lb || xq_le_q(&s->lb, delta)) && (!s->has_ub || xq_ge_q(&s->ub, delta));
}
#endif


/*
 * Prepare the interval s for sampling:
 * - this sets tag, k_min, and k_max
 * - if the period is 0, then it's replaced by a non-zero number
 * - input: n = max number of samples
 */
static void interval_prepare_for_sampling(interval_t *s, uint32_t n) {
  xrational_t aux;
  rational_t div;

  assert(n > 0 && !singleton_interval(s));

  if (q_is_zero(&s->period)) {
    /*
     * Force a non-zero period: try (ub - lb)/n
     */
    if (s->has_ub && s->has_lb && q_neq(&s->lb.main, &s->ub.main)) {
      q_init(&div);
      q_set_int32(&div, 1, n);
      q_set(&s->period, &s->ub.main);
      q_sub(&s->period, &s->lb.main);
      q_mul(&s->period, &div);  // period = (ub - lb)/n
    } else {
      q_set_one(&s->period);
    }
  }

  assert(q_is_pos(&s->period));

  /*
   * Compute k_min = ceil(lb/period) and k_max = floor(up/period)
   */
  xq_init(&aux);
  s->k_min = INT32_MIN;
  if (s->has_lb) {
    xq_set(&aux, &s->lb);
    xq_div(&aux, &s->period);
    xq_ceil(&aux);
    assert(xq_sgn(&aux) <= 0 && xq_is_integer(&aux));
    q_normalize(&aux.main);
    if (q_is_smallint(&aux.main)) {
      s->k_min = q_get_smallint(&aux.main);
    } // else leave k_min = INT32_MIN
  }

  s->k_max = INT32_MAX;
  if (s->has_ub) {
    xq_set(&aux, &s->ub);
    xq_div(&aux, &s->period);
    xq_floor(&aux);
    assert(xq_sgn(&aux) >= 0 && xq_is_integer(&aux));
    q_normalize(&aux.main);
    if (q_is_smallint(&aux.main)) {
      s->k_max = q_get_smallint(&aux.main);
    } // else leave k_max = INT32_MAX
  }

  xq_clear(&aux);
  assert(s->k_min <= 0 && 0 <= s->k_max);
}



/*********************************
 *  ASSERT BOUNDS ON A VARIABLE  *
 ********************************/

/*
 * All push operation add a new constraint to the queue
 * - they update the upper/lower index in vartable
 * - they add a tag and an explanation
 */

// axiom x <= b
static void push_ub_axiom(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set(stack->bound + k, b);
  stack->var[k] = x;
  stack->pre[k] = arith_var_upper_index(&solver->vtbl, x);
  stack->expl[k].lit = null_literal;
  stack->tag[k] = ARITH_AXIOM_UB;
  set_arith_var_upper_index(&solver->vtbl, x, k);
}

// axiom x >= b
static void push_lb_axiom(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set(stack->bound + k, b);
  stack->var[k] = x;
  stack->pre[k] = arith_var_lower_index(&solver->vtbl, x);
  stack->expl[k].lit = null_literal;
  stack->tag[k] = ARITH_AXIOM_LB;
  set_arith_var_lower_index(&solver->vtbl, x, k);
}

// assertion x <= b with literal l as explanation
static void push_ub_assertion(simplex_solver_t *solver, thvar_t x, xrational_t *b, literal_t l) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set(stack->bound + k, b);
  stack->var[k] = x;
  stack->pre[k] = arith_var_upper_index(&solver->vtbl, x);
  stack->expl[k].lit = l;
  stack->tag[k] = ARITH_ASSERTED_UB;
  set_arith_var_upper_index(&solver->vtbl, x, k);
}

// assertion x >= b with literal l as explanation
static void push_lb_assertion(simplex_solver_t *solver, thvar_t x, xrational_t *b, literal_t l) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set(stack->bound + k, b);
  stack->var[k] = x;
  stack->pre[k] = arith_var_lower_index(&solver->vtbl, x);
  stack->expl[k].lit = l;
  stack->tag[k] = ARITH_ASSERTED_LB;
  set_arith_var_lower_index(&solver->vtbl, x, k);
}


// assertion x <= b with e as explanation: e is an array of bound indices, terminated by -1
static void push_ub_derived(simplex_solver_t *solver, thvar_t x, xrational_t *b, int32_t *e) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set(stack->bound + k, b);
  stack->var[k] = x;
  stack->pre[k] = arith_var_upper_index(&solver->vtbl, x);
  stack->expl[k].ptr = e;
  stack->tag[k] = ARITH_DERIVED_UB;
  set_arith_var_upper_index(&solver->vtbl, x, k);
}

// assertion x >= b with e as explanation: e is an array of bound indices, terminated by -1
static void push_lb_derived(simplex_solver_t *solver, thvar_t x, xrational_t *b, int32_t *e) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set(stack->bound + k, b);
  stack->var[k] = x;
  stack->pre[k] = arith_var_lower_index(&solver->vtbl, x);
  stack->expl[k].ptr = e;
  stack->tag[k] = ARITH_DERIVED_LB;
  set_arith_var_lower_index(&solver->vtbl, x, k);
}



// assertion x <= c with triple as an explanation:
static void push_ub_egraph(simplex_solver_t *solver, thvar_t x, rational_t *c, egraph_expl_triple_t *triple) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set_q(stack->bound + k, c);
  stack->var[k] = x;
  stack->pre[k] = arith_var_upper_index(&solver->vtbl, x);
  stack->expl[k].ptr = triple;
  stack->tag[k] = ARITH_EGRAPHEQ_UB;
  set_arith_var_upper_index(&solver->vtbl, x, k);
}


// assertion x >= c with triple as explanation
static void push_lb_egraph(simplex_solver_t *solver, thvar_t x, rational_t *c, egraph_expl_triple_t *triple) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set_q(stack->bound + k, c);
  stack->var[k] = x;
  stack->pre[k] = arith_var_lower_index(&solver->vtbl, x);
  stack->expl[k].ptr = triple;
  stack->tag[k] = ARITH_EGRAPHEQ_LB;
  set_arith_var_lower_index(&solver->vtbl, x, k);
}





/********************************
 *  CHECK BOUNDS ON A VARIABLE  *
 *******************************/

/*
 * Check whether v is a fixed variable
 */
static bool simplex_fixed_variable(simplex_solver_t *solver, thvar_t x) {
  int32_t l, u;

  l = arith_var_lower_index(&solver->vtbl, x);
  u = arith_var_upper_index(&solver->vtbl, x);
  return (l >= 0) && (u >= 0) && xq_eq(&solver->bstack.bound[l], &solver->bstack.bound[u]);
}

/*
 * Return the bound on v if v is a fixed variable
 */
static rational_t *fixed_variable_value(simplex_solver_t *solver, thvar_t x) {
  int32_t l;

  l = arith_var_lower_index(&solver->vtbl, x);
  assert(l >= 0);
  return &solver->bstack.bound[l].main;
}


/*
 * Check whether x is a free variable
 * - i.e., there's no lower or upper bound asserted on x
 */
static inline bool simplex_free_variable(simplex_solver_t *solver, thvar_t x) {
  return arith_var_lower_index(&solver->vtbl, x) < 0 && arith_var_upper_index(&solver->vtbl, x) < 0;
}


#ifndef NDEBUG

/*
 * Check whether x can be eliminated
 * - x must be free and it must have no atoms and no egraph term attached
 * NOTE: this is a necessary but not sufficient condition.
 * See simplex_simplify_matrix.
 */
static bool simplex_eliminable_variable(simplex_solver_t *solver, thvar_t x) {
  return simplex_free_variable(solver, x) && arith_var_num_atoms(&solver->vtbl, x) == 0
    && ! arith_var_has_eterm(&solver->vtbl, x);
}
#endif



/*
 * Check whether value v is between the bounds on x
 */
static bool value_ge_lower_bound(simplex_solver_t *solver, thvar_t x, xrational_t *v) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k < 0 || xq_ge(v, solver->bstack.bound + k);
}

static bool value_le_upper_bound(simplex_solver_t *solver, thvar_t x, xrational_t *v) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k < 0 || xq_le(v, solver->bstack.bound + k);
}

static bool value_within_bounds(simplex_solver_t *solver, thvar_t x, xrational_t *v) {
  return value_ge_lower_bound(solver, x, v) && value_le_upper_bound(solver, x, v);
}



/*
 * Check whether the value of x is between its bound
 */
static bool value_satisfies_lower_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k < 0 || xq_le(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}

static bool value_satisfies_upper_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k < 0 || xq_ge(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}

static bool value_satisfies_bounds(simplex_solver_t *solver, thvar_t x) {
  return value_satisfies_lower_bound(solver, x) && value_satisfies_upper_bound(solver, x);
}



/*
 * Check whether x is at its lower or upper bound
 */
static bool variable_at_lower_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 && xq_eq(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}

static bool variable_at_upper_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 && xq_eq(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}


/*
 * Check whether x < its lower bound or x > its upper bound
 */
static bool variable_below_lower_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 && xq_gt(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}

static bool variable_above_upper_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 && xq_lt(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}







/*********************************
 *  THEORY PROPAGATION OBJECTS   *
 ********************************/

/*
 * Allocate a simple propagation object for bound index k
 * - the object is allocated in the arena
 */
static aprop_t *make_simplex_prop_object(simplex_solver_t *solver, int32_t k) {
  aprop_t *tmp;

  tmp = (aprop_t *) arena_alloc(&solver->arena, sizeof(aprop_t));
  tmp->tag = APROP_BOUND;
  tmp->bound = k;

  return tmp;
}



/*******************************
 *  PROPAGATION TO THE EGRAPH  *
 ******************************/

/*
 * Callback: called when equality between two egraph term is detected
 */
static void prop_eq_to_egraph(void *s, eterm_t t1, eterm_t t2) {
  simplex_solver_t *solver;
  egraph_t *egraph;

  solver = s;
  egraph = solver->egraph;
  assert(egraph != NULL);

#if 0
  printf("---> eq prop: g!%"PRId32" == g!%"PRId32"\n", t1, t2);
#endif
  egraph_propagate_equality(egraph, t1, t2, EXPL_ARITH_PROPAGATION, NULL);
}


/*
 * Check whether p is of the form c + y - z or y - z
 * where c is a constant and y and z are variables.
 */
static bool offset_poly(polynomial_t *p) {
  monomial_t *mono;
  uint32_t n;

  n = p->nterms;
  mono = p->mono;
  if (n > 0 && mono[0].var == const_idx) {
    // skip the constant
    mono ++;
    n --;
  }

  if (n == 2) {
    assert(mono[0].var != const_idx && mono[1].var != const_idx);
    return (q_is_one(&mono[0].coeff) && q_is_minus_one(&mono[1].coeff))
      || (q_is_minus_one(&mono[0].coeff) && q_is_one(&mono[1].coeff));
  }

  return false;
}


/*
 * Check whether variable x is relevant for offset equality propagation
 */
static bool eqprop_relevant_var(simplex_solver_t *solver, thvar_t x) {
  arith_vartable_t *vtbl;
  polynomial_t *p;

  vtbl = &solver->vtbl;

  assert(arith_var_kind(vtbl, x) == AVAR_FREE || arith_var_kind(vtbl, x) == AVAR_POLY);

  p = arith_var_def(vtbl, x);

  /*
   * If p is NULL, then x is a variable => relevant?
   * Otherwise, p is a polynomial. x is relevant if p is of the
   * form (c + z - y) where c is a constant (possibly 0).
   *
   * Note: if p is of the form (c + z) or (c - y), then x is
   * a trivial_variable so it's eliminated from all definitions.
   * This means that x is not relevant here.
   */
  return (p == NULL) || offset_poly(p);
}


/*
 * Increase the size of bitarray eqprop->relevant to store relevance bit for variable i
 */
static void resize_eqprop(eq_propagator_t *eqprop, uint32_t i) {
  uint32_t n;

  n = eqprop->size;
  if (n <= i) {
    n += n;
    if (n <= i) {
      n = i+1;
    }
    eqprop->relevant = extend_bitvector0(eqprop->relevant, n, eqprop->size);
    eqprop->size = n;
  }
}


/*
 * Set the relevance bit for variable x
 * - x must be in the vartable and different from const_idx
 * - solver->eqprop must be initialized
 */
static void eqprop_set_relevance(simplex_solver_t *solver, thvar_t x) {
  eq_propagator_t *eqprop;

  assert(0 < x && x < solver->vtbl.nvars && solver->eqprop != NULL);

  eqprop = solver->eqprop;
  resize_eqprop(eqprop, x);
  assert(x < eqprop->size);

  if (eqprop_relevant_var(solver, x)) {
    set_bit(eqprop->relevant, x);
  }
}


/*
 * Allocate and initialize the propagator object
 */
static void simplex_alloc_eqprop(simplex_solver_t *solver) {
  eq_propagator_t *tmp;
  uint32_t i, n;

  assert(solver->eqprop == NULL);

  tmp = (eq_propagator_t *) safe_malloc(sizeof(eq_propagator_t));
  init_offset_manager(&tmp->mngr, solver, prop_eq_to_egraph);

  n = DEF_EQPROP_SIZE;
  assert(n > 0);

  tmp->relevant = allocate_bitvector0(n);
  tmp->nvars = 1;
  tmp->size = n;
  tmp->prop_ptr = 2; // skip bounds on const_idx (cf. create_constant)
  init_ivector(&tmp->aux, 20);
  init_ivector(&tmp->expl_queue, 20);
  q_init(&tmp->q_aux);

  solver->eqprop = tmp;

  // initialize the relevance bits of all other variables if any
  // for variable 0 = const_idx, relevant[0] stays 0
  n = solver->vtbl.nvars;
  for (i=1; i<n; i++) {
    eqprop_set_relevance(solver, i);
  }
}


/*
 * Delete the propagator
 */
static void simplex_delete_eqprop(simplex_solver_t *solver) {
  eq_propagator_t *eqprop;

  eqprop = solver->eqprop;
  assert(eqprop != NULL);
  delete_offset_manager(&eqprop->mngr);
  delete_bitvector(eqprop->relevant);
  delete_ivector(&eqprop->aux);
  delete_ivector(&eqprop->expl_queue);
  q_clear(&eqprop->q_aux);

  safe_free(eqprop);
  solver->eqprop = NULL;
}


/*
 * Reset
 */
static void simplex_reset_eqprop(simplex_solver_t *solver) {
  eq_propagator_t *eqprop;

  eqprop = solver->eqprop;
  assert(eqprop != NULL);
  reset_offset_manager(&eqprop->mngr);
  clear_bitvector(eqprop->relevant, eqprop->size);
  ivector_reset(&eqprop->aux);
  ivector_reset(&eqprop->expl_queue);
  q_clear(&eqprop->q_aux);
}



/*
 * Push
 */
static void simplex_push_eqprop(simplex_solver_t *solver) {
  eq_propagator_t *eqprop;

  eqprop = solver->eqprop;
  assert(eqprop != NULL);
  offset_manager_push(&eqprop->mngr);
}


/*
 * Pop is divided in two steps
 * - before we remove variables from solver->vtbl, we must
 *   call pop on solver->eqprop.mngr to remove offset variables
 *   and their definitions. This must be done first because
 *   polynomials may be shared between solver->vtbl and
 *   solver->eqprop.mngr.
 * - after we remove variables from solver->vtbl, we must
 *   mark all deleted variables as irrelevant in solver->eqprop.
 */
static void simplex_pop_eqprop(simplex_solver_t *solver) {
  eq_propagator_t *eqprop;

  eqprop = solver->eqprop;
  assert(eqprop != NULL);
  offset_manager_pop(&eqprop->mngr);
}

static void simplex_eqprop_cleanup(simplex_solver_t *solver) {
  eq_propagator_t *eqprop;
  uint32_t i, n;

  eqprop = solver->eqprop;
  assert(eqprop != NULL);

  // clear bits (of deleted variables)
  n = eqprop->size;
  for (i = solver->vtbl.nvars; i<n; i++) {
    clr_bit(eqprop->relevant, i);
  }

  // reset the propagation pointer (same as in solver)
  assert(solver->bstack.prop_ptr == solver->bstack.fix_ptr);
  eqprop->prop_ptr = solver->bstack.prop_ptr;
}



/*
 * Enable eqprop option: the option is ignored if solver->egraph is NULL
 */
void simplex_enable_eqprop(simplex_solver_t *solver) {
  if (solver->egraph != NULL) {
    simplex_enable_options(solver, SIMPLEX_EQPROP);
    if (solver->eqprop == NULL) {
      simplex_alloc_eqprop(solver);
    }
  }
}

void simplex_disable_eqprop(simplex_solver_t *solver) {
  if (solver->egraph != NULL) {
    simplex_disable_options(solver, SIMPLEX_EQPROP);
    if (solver->eqprop != NULL) {
      simplex_delete_eqprop(solver);
    }
  }
}


/*
 * Record that x is attached to eterm t
 */
static void eqprop_record_eterm(simplex_solver_t *solver, thvar_t x, eterm_t t) {
  eq_propagator_t *eqprop;
  arith_vartable_t *vtbl;
  polynomial_t *p;

  vtbl = &solver->vtbl;
  eqprop = solver->eqprop;

  assert(eqprop != NULL && (arith_var_kind(vtbl, x) == AVAR_FREE || arith_var_kind(vtbl, x) == AVAR_POLY));
  p = arith_var_def(vtbl, x);

  record_offset_poly(&eqprop->mngr, t, x, p);
}


/*
 * Check whether bound i freezes the value of variable x
 * - this returns true if x's lower and upper bound are equal and if i is the last bound
 *   asserted
 */
static bool bound_freezes_var(simplex_solver_t *solver, thvar_t x, int32_t i) {
  int32_t l, u;

  assert(i >= 0);

  l = arith_var_lower_index(&solver->vtbl, x); // lower bound on x
  u = arith_var_upper_index(&solver->vtbl, x); // upper bound on x

  if (u < l) {
    // l = last bound on x
    return (l == i) && (u >= 0) && xq_eq(&solver->bstack.bound[l], &solver->bstack.bound[u]);
  } else {
    // u = last bound on x
    return (u == i) && (l >= 0) && xq_eq(&solver->bstack.bound[l], &solver->bstack.bound[u]);
  }
}


/*
 * Process frozen variable x
 * - x is relevant to eqprop
 */
static void eqprop_process_frozen_var(simplex_solver_t *solver, thvar_t x) {
  eq_propagator_t *eqprop;
  polynomial_t *p;
  monomial_t *mono;
  rational_t *a;
  thvar_t y, z;

  assert(eqprop_relevant_var(solver, x) && simplex_fixed_variable(solver, x));

  eqprop = solver->eqprop;
  assert(eqprop != NULL);

  /*
   * We have (a == x) and (x == c + y - z):
   * - we propagate x == a and y == z + (a - c)
   */
  a = fixed_variable_value(solver, x);
  p = arith_var_def(&solver->vtbl, x);

  assert_offset_equality(&eqprop->mngr, x, -1, a, x); // x == a with id = x

  if (p != NULL) {
    mono = p->mono;
    assert((p->nterms == 3 && mono[0].var == const_idx) ||
	   (p->nterms == 2 && mono[0].var > const_idx));

    // store a - c in q_aux
    q_set(&eqprop->q_aux, a);
    if (mono[0].var == const_idx) {
      q_sub(&eqprop->q_aux, &mono[0].coeff);
      mono ++;
    }

    if (q_is_one(&mono[0].coeff)) {
      assert(q_is_minus_one(&mono[1].coeff));
      y = mono[0].var;
      z = mono[1].var;
    } else {
      assert(q_is_minus_one(&mono[0].coeff) && q_is_one(&mono[1].coeff));
      y = mono[1].var;
      z = mono[0].var;
    }

    // propagate (y == z + q_aux) to manager; use x as id
    assert_offset_equality(&eqprop->mngr, y, z, &eqprop->q_aux, x);
  }
}


/*
 * Scan all new bounds in solver->bstack
 * - for each frozen variable, add an offset equality to the offset manager
 */
static void simplex_propagate_equalities(simplex_solver_t *solver) {
  eq_propagator_t *eqprop;
  arith_bstack_t *bstack;
  uint32_t i, n, eqs;
  thvar_t x;

  bstack = &solver->bstack;
  eqprop = solver->eqprop;
  assert(eqprop != NULL);

  n = bstack->top;
  eqs = 0;
  for (i=eqprop->prop_ptr; i<n; i++) {
    x = bstack->var[i];
    if (bound_freezes_var(solver, x, i) && eqprop_relevant_var(solver, x)) {
      /*
       * x is frozen and relevant: propagate the constraint x == value
       * to the offset manager.
       */
      assert(tst_bit(eqprop->relevant, x));
      assert(simplex_fixed_variable(solver, x));
#if 0
      printf("---> fixed var: ");
      print_simplex_var(stdout, solver, x);
      printf(" == ");
      print_simplex_var_value(stdout, solver, x);
      printf(" (bound = %"PRIu32")\n", i);
      if (!arith_var_is_free(&solver->vtbl, x)) {
	printf("     ");
	print_simplex_vardef(stdout, solver, x);
      }
#endif

      eqprop_process_frozen_var(solver, x);
      eqs ++;
    }
  }

  if (eqs > 0) {
    assert_true(offset_manager_propagate(&eqprop->mngr));
  }

  eqprop->prop_ptr = n;
}



/****************************
 *  SOLVER INITIALIZATION   *
 ***************************/

/*
 * Create the constant:
 * - variable of index 0 in vartable, with definition = 1
 *   (as a rational constant)
 * - set its value to 1
 * - assert that its lower and upper bound are 1
 * This must be done before any other variable is created,
 * but after the poly_buffer and vartable are initialized
 */
static void simplex_create_constant(simplex_solver_t *solver) {
  xrational_t *v;
  bool new_var;
  thvar_t x;

  assert(solver->vtbl.nvars == 0 && solver->matrix.ncolumns == 0);

  // create the variable in vtbl
  q_set_one(&solver->constant);
  x = get_var_for_constant(&solver->vtbl, &solver->constant, &new_var);
  assert(new_var && x == const_idx);

  // create column 0 for const_idx
  matrix_add_column(&solver->matrix);

  // assignment and tags: lower-bound = upper-bound = 1
  v = arith_var_value(&solver->vtbl, x);
  xq_set_one(v);
  set_arith_var_lb(&solver->vtbl, x);
  set_arith_var_ub(&solver->vtbl, x);

  // lower and upper bounds
  xq_set_one(&solver->bound);
  push_lb_axiom(solver, x, &solver->bound);
  push_ub_axiom(solver, x, &solver->bound);

  // skip these two bounds
  assert(solver->bstack.top == 2);
  solver->bstack.prop_ptr = 2;
  solver->bstack.fix_ptr = 2;
}


/*
 * Initialize a simplex solver
 * - core = attached smt_core
 * - gates = attached gate manager
 * - egraph = attached egraph (or NULL)
 */
void init_simplex_solver(simplex_solver_t *solver, smt_core_t *core, gate_manager_t *gates, egraph_t *egraph) {
  solver->core = core;
  solver->gate_manager = gates;
  solver->egraph = egraph;
  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;

  solver->options = SIMPLEX_DEFAULT_OPTIONS;
  solver->interrupted = false;
  solver->use_blands_rule = false;
  solver->bland_threshold = SIMPLEX_DEFAULT_BLAND_THRESHOLD;
  solver->prop_row_size = SIMPLEX_DEFAULT_PROP_ROW_SIZE;
  solver->last_conflict_row = -1;
  solver->recheck = false;

  solver->prng = SPLX_PRNG_SEED;

  solver->integer_solving = false;
  solver->enable_dfeas = false;
  solver->check_counter = 0;
  solver->check_period = SIMPLEX_DEFAULT_CHECK_PERIOD;
  solver->last_branch_atom = null_bvar;
  solver->dsolver = NULL;     // allocated later if needed

  solver->cache = NULL;       // allocated later if needed

  init_simplex_statistics(&solver->stats);

  init_arith_atomtable(&solver->atbl, core);
  init_arith_vartable(&solver->vtbl);

  solver->propagator = NULL; // allocated if needed in start search

  solver->eqprop = NULL; // allocated by simplex_enable_eqprop

  init_matrix(&solver->matrix, 0, 0);
  solver->tableau_ready = false;
  solver->matrix_ready = true;
  solver->save_rows = false;

  init_int_heap(&solver->infeasible_vars, 0, 0);
  init_arith_bstack(&solver->bstack, DEF_ARITH_BSTACK_SIZE);
  init_arith_astack(&solver->assertion_queue, DEF_ARITH_ASTACK_SIZE);
  init_eassertion_queue(&solver->egraph_queue);
  init_arith_undo_stack(&solver->stack, DEF_ARITH_UNDO_STACK_SIZE);

  init_arith_trail(&solver->trail_stack);
  init_pvector(&solver->saved_rows, 0);

  init_elim_matrix(&solver->elim);
  init_fvar_vector(&solver->fvars);

  init_poly_buffer(&solver->buffer);
  q_init(&solver->constant);
  q_init(&solver->aux);
  q_init(&solver->gcd);
  xq_init(&solver->bound);
  xq_init(&solver->delta);
  xq_init(&solver->xq0);

  init_ivector(&solver->expl_vector, DEF_ARITH_EXPL_VECTOR_SIZE);
  init_ivector(&solver->expl_queue, DEF_ARITH_EXPL_VECTOR_SIZE);
  init_ivector(&solver->expl_aux, DEF_ARITH_EXPL_VECTOR_SIZE);
  init_ivector(&solver->aux_vector, 10);
  init_ivector(&solver->aux_vector2, 10);
  init_ivector(&solver->rows_to_process, DEF_PROCESS_ROW_VECTOR_SIZE);

  init_arena(&solver->arena);

  // Model
  solver->value = NULL;     // allocated when needed
  q_init(&solver->epsilon);
  q_init(&solver->factor);
  solver->dprng = DPRNG_DEFAULT_SEED;

  solver->env = NULL;

  // add the constant
  simplex_create_constant(solver);

  // push undo record for level 0
  arith_push_undo_record(&solver->stack, 0, 0);
}


/*
 * Set buffer as jump buffer for exceptions during internalization
 */
void simplex_solver_init_jmpbuf(simplex_solver_t *solver, jmp_buf *buffer) {
  solver->env = buffer;
}



/*
 * Return the diophantine system subsolver
 * - allocate and initialize it if needed
 */
static dsolver_t *simplex_get_dsolver(simplex_solver_t *solver) {
  dsolver_t *s;

  s = solver->dsolver;
  if (s == NULL) {
    s = (dsolver_t *) safe_malloc(sizeof(dsolver_t));
    init_dsolver(s, 0, 0, 0);
    solver->dsolver = s;
  }
  return s;
}


/*
 * Return the cache
 * - allocate and initialize it if needed
 */
static cache_t *simplex_get_cache(simplex_solver_t *solver) {
  cache_t *c;

  c = solver->cache;
  if (c == NULL) {
    c = (cache_t *) safe_malloc(sizeof(cache_t));
    // initialize then synchronize the push/pop level
    init_cache(c);
    cache_set_level(c, solver->base_level);
    solver->cache = c;
  }

  return c;
}






/*******************
 *  BINARY LEMMAS  *
 ******************/

/*
 * Add binary lemma for two atoms atom1 and atom2
 * - the atoms must be on the same variable x
 * - they must be distinct
 */
static void create_binary_lemma(simplex_solver_t *solver, arith_atom_t *atom1, arith_atom_t *atom2) {
  arith_atom_t *aux;
  rational_t *a, *b;
  literal_t l1, l2;

  assert(var_of_atom(atom1) == var_of_atom(atom2) && atom1 != atom2);
  assert(tag_of_atom(atom1) != tag_of_atom(atom2) || q_neq(bound_of_atom(atom1), bound_of_atom(atom2)));

#if TRACE
  printf("---> create_binary_lemma:\n");
  printf("     ");
  print_simplex_atomdef(stdout, solver, boolvar_of_atom(atom1));
  printf("     ");
  print_simplex_atomdef(stdout, solver, boolvar_of_atom(atom2));
#endif

  /*
   * - make sure atom1 has a higher tag than atom2 to
   *   cut the number of cases
   * - after this, the possible combinations are
   *     atom1      atom2
   *   (x >= a)    (x >= b)
   *   (x <= a)    (x >= b)
   *   (x <= a)    (x <= b)
   *   (x == a)    (x >= b)
   *   (x == a)    (x <= b)
   *   (x == a)    (x == b)
   */
  if (tag_of_atom(atom1) < tag_of_atom(atom2)) {
    aux = atom1;
    atom1 = atom2;
    atom2 = aux;
  }

  a = bound_of_atom(atom1);
  b = bound_of_atom(atom2);
  l1 = pos_lit(boolvar_of_atom(atom1));
  l2 = pos_lit(boolvar_of_atom(atom2));

  switch (tag_of_atom(atom1)) {
  case GE_ATM:
    assert(tag_of_atom(atom2) == GE_ATM);
    if (q_ge(a, b)) {
      add_binary_clause(solver->core, not(l1), l2);  // (x >= a) ==> (x >= b)
    } else {
      add_binary_clause(solver->core, l1, not(l2));  // (x < a) ==> (x < b)
    }
    break;

  case LE_ATM:
    if (tag_of_atom(atom2) == GE_ATM) {
      if (q_lt(a, b)) {
        add_binary_clause(solver->core, not(l1), not(l2));  // (x > a) or (x > b)
      } else {
        add_binary_clause(solver->core, l1, l2);   // (x <= a) or (x >= b)
      }
    } else {
      assert(tag_of_atom(atom2) == LE_ATM);
      if (q_le(a, b)) {
        add_binary_clause(solver->core, not(l1), l2);  // (x <= a) ==> (x <= b)
      } else {
        add_binary_clause(solver->core, l1, not(l2));  // (x > a) ==> (x > b))
      }
    }
    break;

  case EQ_ATM:
    switch (tag_of_atom(atom2)) {
    case GE_ATM:
      if (q_ge(a, b)) {
        add_binary_clause(solver->core, not(l1), l2); // (x == a) ==> (x >= b))
      } else {
        add_binary_clause(solver->core, not(l1), not(l2));  // (x == a) ==> (x < b)
      }
      break;
    case LE_ATM:
      if (q_le(a, b)) {
        add_binary_clause(solver->core, not(l1), l2);   // (x == a) ==> (x <= b)
      } else {
        add_binary_clause(solver->core, not(l1), not(l2)); // (x == a) ==> (x > b);
      }
      break;
    case EQ_ATM:
      add_binary_clause(solver->core, not(l1), not(l2)); // (not (x == a)) or (not (x == b))
      break;
    }
  }

  solver->stats.num_binary_lemmas ++;
}


/*
 * Build all the binary lemmas involving atom id on variable x
 * - id must not be in the atom_vector of x
 *
 * Let a be the bound for atom id: the atom is then either (x >= a) or (x <= a)
 * - we search for two atoms atom1 and atom2 such that
 *   bound_of(atom1) <= a and a <= bound_of(atom2)
 *   and such that bound_of(atom1) and bound_of(atom2) are
 *   as close to a as possible.
 * - then we generate two lemmas
 */
static void build_binary_lemmas_for_atom(simplex_solver_t *solver, thvar_t x, int32_t id) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom, *atom1, *atom2, *aux;
  rational_t *a;
  uint32_t i, n;
  int32_t id2;

  if (simplex_option_enabled(solver, SIMPLEX_EAGER_LEMMAS)) {
    atom_vector = arith_var_atom_vector(&solver->vtbl, x);
    /*
     * If we have N atoms on variable x, then this code is O(N^2).
     * To limit the cost, we stop generating lemmas when N gets too large
     * (i.e., more than 50).
     */
    if (atom_vector != NULL && iv_size(atom_vector) <= 50) {
      atbl = &solver->atbl;
      atom = arith_atom(atbl, id);
      assert(var_of_atom(atom) == x);
      a = bound_of_atom(atom);
      atom1 = NULL;
      atom2 = NULL;
      n = iv_size(atom_vector);
      for (i=0; i<n; i++) {
        id2 = atom_vector[i];
        assert(id != id2);
	aux = arith_atom(atbl, id2);
	if (q_eq(bound_of_atom(aux), a)) {
	  atom1 = aux;
	  atom2 = NULL;
	  break;
	}
	if (q_lt(bound_of_atom(aux), a)) {
	  // bound on aux < a
	  if (atom1 == NULL || q_gt(bound_of_atom(aux), bound_of_atom(atom1))) {
	    atom1 = aux;
	  }
	} else {
	  // bound on aux > a
	  if (atom2 == NULL || q_lt(bound_of_atom(aux), bound_of_atom(atom2))) {
	    atom2 = aux;
	  }
	}
      }
      if (atom1 != NULL) {
        create_binary_lemma(solver, atom, atom1);
      }
      if (atom2 != NULL) {
        create_binary_lemma(solver, atom, atom2);
      }
    }
  }
}





/*****************************
 *  POLYNOMIAL CONSTRUCTION  *
 ****************************/

/*
 * Check whether p is a simple polynomial (cheap to substitute for variable x)
 * - return true if p is either (c + b.y) or c or b.y or 0
 */
static bool simple_poly(polynomial_t *p) {
  uint32_t n;

  n = p->nterms;
  return (n <= 1) || (n <= 2 && p->mono[0].var == const_idx);
}


/*
 * Check whether we should substitute x by its definition in polynomials or atoms
 * - x must be different form const_idx
 * - the substitution x := p is applied if it's cheap enough
 */
static bool trivial_variable(arith_vartable_t *tbl, thvar_t x) {
  polynomial_t *q;

  assert(arith_var_kind(tbl, x) == AVAR_FREE ||
         arith_var_kind(tbl, x) == AVAR_POLY);

  /*
   * arith_var_def returns a void* pointer
   * - if x is a free variable, the definition is NULL
   * - otherwise, the definition is a pointer to a polynomial
   */
  q = arith_var_def(tbl, x);
  return q != NULL && simple_poly(q);
}


/*
 * Add monomial a.x to buffer b
 * - if x has a simple definition p, then replace x by p, that is, add a.p to b
 * - a must not be equal to solver->aux
 */
static void add_mono_or_subst(simplex_solver_t *solver, poly_buffer_t *b, thvar_t x, rational_t *a) {
  polynomial_t *p;

  if (x != const_idx && trivial_variable(&solver->vtbl, x)) {
    // replace x by its definition
    p = arith_var_poly_def(&solver->vtbl, x);
    assert(p->nterms <= 2);
    poly_buffer_addmul_poly(b, p, a);
  } else {
    poly_buffer_add_monomial(b, x, a);
  }
}


/*
 * Add variable x to buffer b if x is not trivial
 * otherwise add p to b, where (x := p) is the definition of x
 */
static void add_var_or_subst(simplex_solver_t *solver, poly_buffer_t *b, thvar_t x) {
  polynomial_t *p;

  if (x != const_idx && trivial_variable(&solver->vtbl, x)) {
    p = arith_var_poly_def(&solver->vtbl, x);
    poly_buffer_add_poly(b, p);
  } else {
    poly_buffer_add_var(b, x);
  }
}


/*
 * Subtract x from buffer b if x is not trivial
 * otherwise subtract p from b, where (x := p) is the definition of x
 */
static void sub_var_or_subst(simplex_solver_t *solver, poly_buffer_t *b, thvar_t x) {
  polynomial_t *p;

  if (x != const_idx && trivial_variable(&solver->vtbl, x)) {
    p = arith_var_poly_def(&solver->vtbl, x);
    poly_buffer_sub_poly(b, p);
  } else {
    poly_buffer_sub_var(b, x);
  }
}


/*
 * Store p into solver->buffer and apply the renaming defined by map
 * - p is of the form a_0 t_0 + ... + a_n t_n
 *   map[i] is the simplex variable that represents t_i
 *   with the possible exception that map[0] = null_thvar if t_0 = const_idx
 */
static void rename_poly_aux(simplex_solver_t *solver, polynomial_t *p, thvar_t *map) {
  poly_buffer_t *b;
  uint32_t i, n;
  monomial_t *a;

  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  n = p->nterms;

  // if n is zero, there's nothing more to do
  if (n > 0) {
    a = p->mono;

    // deal with the constant first
    if (a[0].var == const_idx) {
      assert(map[0] == null_thvar);

      poly_buffer_add_const(b, &a[0].coeff);
      a ++;
      map ++;
      n --;
    }

    // non-constant monomials
    for (i=0; i<n; i++) {
      add_mono_or_subst(solver, b, map[i], &a[i].coeff);
    }
  }
}


/*
 * Rename variables of p as defined by map
 * - store the result in the internal poly_buffer and normalize the buffer
 */
static void rename_poly(simplex_solver_t *solver, polynomial_t *p, thvar_t *map) {
  rename_poly_aux(solver, p, map);
  normalize_poly_buffer(&solver->buffer);
}



/*
 * Check whether all variables of buffer are integers
 */
static bool all_integer_vars(simplex_solver_t *solver) {
  arith_vartable_t *tbl;
  poly_buffer_t *b;
  monomial_t *a;
  uint32_t i, n;

  b = &solver->buffer;
  tbl = &solver->vtbl;
  n = poly_buffer_nterms(b);
  a = poly_buffer_mono(b);
  for (i=0; i<n; i++) {
    if (! arith_var_is_int(tbl, a[i].var)) return false;
  }
  return true;
}



/*
 * Activate variable x:
 * - add the row x - p == 0 to the matrix provided x is not trivial
 */
static void activate_variable(simplex_solver_t *solver, thvar_t x) {
  polynomial_t *p;

  p = arith_var_def(&solver->vtbl, x);
  if (p != NULL && ! simple_poly(p)) {
    matrix_add_eq(&solver->matrix, x, p->mono, p->nterms);
  }
}



/****************************************
 *  SUPPORT FOR TERM/ATOM CONSTRUCTION  *
 ***************************************/

/*
 * Get a variable x whose definition is equal to the buffer then reset the buffer
 * - if x is a new variable, add a column to the matrix and add a of the form
 *   x - buffer = 0
 */
static thvar_t get_var_from_buffer(simplex_solver_t *solver) {
  poly_buffer_t *b;
  thvar_t x;
  bool new_var;

  b = &solver->buffer;

  // check whether b is reduced to a single variable x
  x = poly_buffer_convert_to_var(b);

  /*
   * HACK: the result of poly_buffer_convert_to_var can be
   *    -1 (null_idx) if b is not of the form 1.x
   *     0 (const_idx) if b is 1
   *     a good variable x if b is 1.x (with x>0)
   *
   * We must build a poly for x in the first two cases.
   */
  if (x <= 0) {
    assert(x == const_idx || x == null_idx);
    x = get_var_for_poly(&solver->vtbl, poly_buffer_mono(b), poly_buffer_nterms(b), &new_var);
    if (new_var) {
      matrix_add_column(&solver->matrix);
      activate_variable(solver, x);
      // set relevance mark in solver->eqprop
      if (solver->eqprop != NULL) {
	eqprop_set_relevance(solver, x);
      }
    }
  }
  reset_poly_buffer(b);

  return x;
}


/*
 * Create the atom (x >= c) or (x <= c)
 * - is_int indicates whether x is an integer variable or not
 */
static literal_t get_ge_atom(simplex_solver_t *solver, thvar_t x, bool is_int, rational_t *c) {
  literal_t l;
  int32_t new_idx, k;

  assert(solver->decision_level == solver->base_level);

  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0 && xq_lt_q(solver->bstack.bound + k, c)) {
    // axiom: x <= bound[k] and bound[k] < c so (x >= c) is false
    return false_literal;
  }

  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0 && xq_ge_q(solver->bstack.bound + k, c)) {
    // axiom: x >= bound[k] and bound[k] >= c so (x >= c) is true
    return true_literal;
  }

  l = get_literal_for_ge_atom(&solver->atbl, x, is_int, c, &new_idx);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, x, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, x, new_idx);
  }
  return l;
}

static literal_t get_le_atom(simplex_solver_t *solver, thvar_t x, bool is_int, rational_t *c) {
  literal_t l;
  int32_t new_idx, k;

  assert(solver->decision_level == solver->base_level);

  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0 && xq_gt_q(solver->bstack.bound + k, c)) {
    // axiom: x >= bound[k] and bound[k] > c so (x <= c) is false
    return false_literal;
  }

  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0 && xq_le_q(solver->bstack.bound + k, c)) {
    // axiom: x <= bound[k] and bound[k] <= c so (x <= c) is true
    return true_literal;
  }

  l = get_literal_for_le_atom(&solver->atbl, x, is_int, c, &new_idx);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, x, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, x, new_idx);
  }
  return l;
}



/*
 * Decompose the buffer into (p + a) where a is the constant term
 * - store the opposite of a into solver->constant
 * - return a variable x equal to the non-constant part (i.e., p)
 * - if x is a new variable, add a column to the matrix
 */
static thvar_t decompose_and_get_var(simplex_solver_t *solver) {
  poly_buffer_t *b;
  thvar_t x;
  bool new_var;

  b = &solver->buffer;
  poly_buffer_get_neg_constant(b, &solver->constant);
  x = poly_buffer_nonconstant_convert_to_var(b);
  if (x < 0) {
    x = get_var_for_poly_offset(&solver->vtbl, poly_buffer_mono(b), poly_buffer_nterms(b), &new_var);
    if (new_var) {
      matrix_add_column(&solver->matrix);
      activate_variable(solver, x);
      // set relevance mark in solver->eqprop
      if (solver->eqprop != NULL) {
	eqprop_set_relevance(solver, x);
      }
    }
  }
  reset_poly_buffer(b);
  return x;
}


/*
 * Create the atom p >= 0 where p is stored in the solver's buffer
 * - the buffer must be normalized
 */
static literal_t make_ge_atom(simplex_solver_t *solver) {
  poly_buffer_t *b;
  bool negated, is_int;
  thvar_t x;

  b = &solver->buffer;

  /*
   * Check whether the atom is trivially true or false
   */
  if (poly_buffer_is_zero(b) || poly_buffer_is_pos_constant(b)) {
#if TRACE
    printf("---> true\n");
#endif
    reset_poly_buffer(b);
    return true_literal;
  }

  if (poly_buffer_is_neg_constant(b)) {
#if TRACE
    printf("---> false\n");
#endif
    reset_poly_buffer(b);
    return false_literal;
  }

  /*
   * Normalize to x <= b or x >= b
   */
  is_int = all_integer_vars(solver);
  if (is_int) {
    // make coefficients integers
    negated = poly_buffer_make_nonconstant_integral(b);
#if TRACE
    printf("---> int scaling: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    x = decompose_and_get_var(solver);
    assert(arith_var_is_int(&solver->vtbl, x));
    // strengthen the bound
    // TODO: if x is a polynomial, we could strengthen more, i.e.,
    //       divide by the GCD of x's coefficients?
    if (negated) {
      q_floor(&solver->constant);
    } else {
      q_ceil(&solver->constant);
    }

  } else {
    // make lead coefficient = 1
    negated = poly_buffer_make_monic(b);
#if TRACE
    printf("---> monic: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    x = decompose_and_get_var(solver);
    assert(! arith_var_is_int(&solver->vtbl, x));
  }


  /*
   * If negated is true, the atom is (x <= constant) otherwise
   * it's (x >= constant)
   */
  if (negated) {
#if TRACE
    printf("---> atom ");
    print_simplex_var(stdout, solver, x);
    printf(" <= ");
    q_print(stdout, &solver->constant);
    printf("\n");
    if (! arith_var_is_free(&solver->vtbl, x)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, x);
    }
#endif

    return get_le_atom(solver, x, is_int, &solver->constant);

  } else {
#if TRACE
    printf("---> atom ");
    print_simplex_var(stdout, solver, x);
    printf(" >= ");
    q_print(stdout, &solver->constant);
    printf("\n");
    if (! arith_var_is_free(&solver->vtbl, x)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, x);
    }
#endif

    return get_ge_atom(solver, x, is_int, &solver->constant);
  }
}


/*
 * Auxiliary function: simplify the atom p == 0 where p is stored in the buffer
 * - check whether p == 0 simplifies to true or false
 * - if not, create the two atoms (p >= 0) and (p <= 0)
 * Results:
 * - if the atom simplifies, the returned value is either true_literal or false_literal
 * - otherwise the returned value is null_literal, and literals for (p >= 0) and (p <= 0)
 *   are returned in *l1 and *l2
 */
static literal_t simplify_eq_atom(simplex_solver_t *solver, literal_t *l1, literal_t *l2) {
  poly_buffer_t *b;
  thvar_t x;
  bool is_int;

  b = &solver->buffer;

  if (poly_buffer_is_zero(b)) {
#if TRACE
    printf("---> true\n");
#endif
    reset_poly_buffer(b);
    return true_literal;
  }

  if (poly_buffer_is_nzconstant(b)) {
#if TRACE
    printf("---> false\n");
#endif
    reset_poly_buffer(b);
    return false_literal;
  }

  is_int = all_integer_vars(solver);
  if (is_int) {
    poly_buffer_make_integral(b);
#if TRACE
    printf("---> int scaling: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    if (! poly_buffer_gcd_test(b)) {
#if TRACE
      printf("---> false by GCD test\n");
#endif
      reset_poly_buffer(b);
      return false_literal;
    }
  } else {
    poly_buffer_make_monic(b); // make lead coefficient = 1

#if TRACE
    printf("---> monic: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
  }

  x = decompose_and_get_var(solver);  // buffer is now equal to x - c where c = &solver->constant

#if TRACE
  printf("---> atom ");
  print_simplex_var(stdout, solver, x);
  printf(" == ");
  q_print(stdout, &solver->constant);
  printf("\n");
  if (! arith_var_is_free(&solver->vtbl, x)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x);
  }
#endif

  *l1 = get_ge_atom(solver, x, is_int, &solver->constant);
  *l2 = get_le_atom(solver, x, is_int, &solver->constant);

  return null_literal;
}


/*
 * Create the atom p == 0 where p is stored in the buffer
 * - check for simplification first
 * - create (and (p >= 0) (p <= 0)) otherwise
 */
static literal_t make_eq_atom(simplex_solver_t *solver) {
  literal_t l1, l2, l;

  l = simplify_eq_atom(solver, &l1, &l2);
  if (l == null_literal) {
    l = mk_and_gate2(solver->gate_manager, l1, l2);
  }
  return l;
}



/*
 * Assert c as lower bound for x
 * - strict indicates whether the bound is strict or not
 */
static void add_lb_axiom(simplex_solver_t *solver, thvar_t x, rational_t *c, bool strict) {
  xrational_t *b;
  int32_t k;

  assert(solver->base_level == solver->decision_level);

#if TRACE
  printf("---> add_lb_axiom: ");
  print_simplex_var(stdout, solver, x);
  if (strict) {
    printf(" > ");
  } else {
    printf(" >= ");
  }
  q_print(stdout, c);
  printf("\n");
  if (! arith_var_is_free(&solver->vtbl, x)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x);
  }
#endif

  // store the bound as an extended rational
  b = &solver->bound;
  if (strict) {
    xq_set_q_plus_delta(b, c);
  } else {
    xq_set_q(b, c);
  }

  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0 && xq_lt(solver->bstack.bound + k, b)) {
    // Unsat: the existing upper bound on x is < b
    solver->unsat_before_search = true;
#if TRACE
    printf("---> Conflict\n\n");
#endif
    return;
  }

  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0 && xq_ge(solver->bstack.bound + k, b)) {
    // Redundant: the existing lower bound is >= b
#if TRACE
    printf("---> Redundant\n\n");
#endif
    return;
  }

  push_lb_axiom(solver, x, b);
}


/*
 * Assert c as upper bound for x
 * - strict indicates whether the bound is strict or not
 */
static void add_ub_axiom(simplex_solver_t *solver, thvar_t x, rational_t *c, bool strict) {
  xrational_t *b;
  int32_t k;

  assert(solver->base_level == solver->decision_level);

#if TRACE
  printf("---> add_ub_axiom: ");
  print_simplex_var(stdout, solver, x);
  if (strict) {
    printf(" < ");
  } else {
    printf(" <= ");
  }
  q_print(stdout, c);
  printf("\n");
  if (! arith_var_is_free(&solver->vtbl, x)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x);
  }
#endif


  // store the bound as an extended rational
  b = &solver->bound;
  if (strict) {
    xq_set_q_minus_delta(b, c);
  } else {
    xq_set_q(b, c);
  }

  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0 && xq_gt(solver->bstack.bound + k, b)) {
    // Unsat: existing lower bound on x is > b
    solver->unsat_before_search = true;
#if TRACE
    printf("---> Conflict\n\n");
#endif
    return;
  }

  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0 && xq_le(solver->bstack.bound + k, b)) {
    // redundant: existing upper bound <= b
#if TRACE
    printf("---> Redundant\n\n");
#endif
    return;
  }

  push_ub_axiom(solver, x, b);
}



/*
 * Add the axiom p == 0 where p is stored in the solver's buffer
 * - if p == 0 simplifies to false, set the 'unsat_before_search' flag
 * - if p == 0 simplifies to true, do nothing
 * - if p == 0 is equivalent to x == c for a variable x and constant c
 *   then add the bounds (x <= c) and (x >= c)
 * - otherwise, add the row p == 0 to the matrix
 */
static void add_eq_axiom(simplex_solver_t *solver) {
  poly_buffer_t *b;
  thvar_t x;

#if TRACE
  printf("---> simplex_add_eq_axiom: ");
  print_simplex_buffer(stdout, solver);
  printf(" == 0\n");
#endif

  b = &solver->buffer;
  if (poly_buffer_is_zero(b)) {
#if TRACE
    printf("---> true\n");
#endif
    goto done;
  }

  if (poly_buffer_is_nzconstant(b)) {
#if TRACE
    printf("---> false\n");
#endif
    solver->unsat_before_search = true;
    goto done;
  }

  if (all_integer_vars(solver)) {
    poly_buffer_make_integral(b);
#if TRACE
    printf("---> int scaling: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    if (! poly_buffer_gcd_test(b)) {
#if TRACE
      printf("---> false by GCD test\n");
#endif
      solver->unsat_before_search = true;
      goto done;
    }
  }


  // Check whether p == 0 can be rewritten to (x == constant)
  x = poly_buffer_convert_to_vareq(b, &solver->constant);
  if (x >= 0) {
#if TRACE
    printf("---> simplified to ");
    print_simplex_var(stdout, solver, x);
    printf(" == ");
    q_print(stdout, &solver->constant);
    printf("\n");
#endif
    // assert bounds (x <= constant) and (x >= constant)
    add_ub_axiom(solver, x, &solver->constant, false);
    add_lb_axiom(solver, x, &solver->constant, false);
    goto done;
  }


#if TRACE
  printf("---> new row\n");
#endif
  if (solver->save_rows) {
    // make a copy so that the matrix can be restored if needed
    pvector_push(&solver->saved_rows, monarray_copy_to_poly(poly_buffer_mono(b), poly_buffer_nterms(b)));
  }
  matrix_add_row(&solver->matrix, poly_buffer_mono(b), poly_buffer_nterms(b));

 done:
  reset_poly_buffer(b);
}


/*
 * Assert the axiom (p == 0) or (p != 0), where p is stored in the solver's buffer
 * - if tt is true  --> assert (p == 0)
 * - if tt is false --> assert (p != 0)
 */
static void add_eq_or_diseq_axiom(simplex_solver_t *solver, bool tt) {
  literal_t l, l1, l2;

  if (tt) {
    add_eq_axiom(solver);
  } else {
    // Add the clause (or (not (p >= 0)) (not (p <= 0)))
    l = simplify_eq_atom(solver, &l1, &l2);
    if (l == null_literal) {
      // l1 is (p >= 0), l2 is (p <= 0): assert (or (not l1) (not l2))
      add_binary_clause(solver->core, not(l1), not(l2));

#if TRACE
      printf("---> adding clause: ");
      print_binary_clause(stdout, not(l1), not(l2));
      printf("\n");
      if (var_of(l1) != const_bvar) {
	print_simplex_atomdef(stdout, solver, var_of(l1));
      }
      if (var_of(l2) != const_bvar) {
	print_simplex_atomdef(stdout, solver, var_of(l2));
      }
#endif

    } else if (l == true_literal) {
      // p == 0 is true: mark the whole thing as unsat
      solver->unsat_before_search = true;
    } // otherwise l == false_literal: nothing to do
  }
}


/*
 * Assert the axiom (p >= 0) or (p < 0), where p is stored in the solver's buffer
 * - if tt is true --> assert (p >= 0)
 * - if tt is false --> assert (p < 0)
 * - check whether the assertion simplifies to true or false first
 * - if it's false, set the flag unsat_before_search
 */
static void add_ge_axiom(simplex_solver_t *solver, bool tt) {
  poly_buffer_t *b;
  bool negated;
  thvar_t x;

#if TRACE
  printf("---> simplex_add_ge_axiom: ");
  print_simplex_buffer(stdout, solver);
  if (tt) {
    printf(" >= 0\n");
  } else {
    printf(" < 0\n");
  }
#endif

  b = &solver->buffer;
  if (poly_buffer_is_zero(b) || poly_buffer_is_pos_constant(b)) {
    // p >= 0 is trivially true
    if (! tt) solver->unsat_before_search = true;
#if TRACE
    if (!tt) {
      printf("---> unsat\n");
    } else {
      printf("---> redundant\n");
    }
#endif
    goto done;
  }

  if (poly_buffer_is_neg_constant(b)) {
    // p >= 0 is trivially false
    if (tt) solver->unsat_before_search = true;
#if TRACE
    if (!tt) {
      printf("---> unsat\n");
    } else {
      printf("---> redundant\n");
    }
#endif
    goto done;
  }


  /*
   * Normalize then assert the bound
   */
  if (all_integer_vars(solver)) {
    negated = poly_buffer_make_nonconstant_integral(b);
#if TRACE
    printf("---> int scaling: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    x = decompose_and_get_var(solver);
    assert(arith_var_is_int(&solver->vtbl, x));
    if (negated) {
      // TODO: strengthen more if x is a polynomial (divide by GCD of x's coefficients)
      q_floor(&solver->constant);
      if (tt) {
        // (p >= 0) is equivalent to (x <= constant)
        add_ub_axiom(solver, x, &solver->constant, false);
#if TRACE
	printf("---> ");
	print_simplex_vardef(stdout, solver, x);
	printf("---> bound: ");
	print_simplex_var_bounds(stdout, solver, x);
	printf("\n");
#endif
      } else {
        // not (p >= 0) is equivalent to (x >= constant + 1)
        q_add_one(&solver->constant);
        add_lb_axiom(solver, x, &solver->constant, false);
#if TRACE
	printf("---> ");
	print_simplex_vardef(stdout, solver, x);
	printf("---> bound: ");
	print_simplex_var_bounds(stdout, solver, x);
	printf("\n");
#endif
      }
    } else {
      // TODO: strengthen more if x is a polynomial (divide by GCD of x's coefficients)
      q_ceil(&solver->constant);
      if (tt) {
        // (p >= 0) is equivalent to (x >= constant)
        add_lb_axiom(solver, x, &solver->constant, false);
#if TRACE
	printf("---> ");
	print_simplex_vardef(stdout, solver, x);
	printf("---> bound: ");
	print_simplex_var_bounds(stdout, solver, x);
	printf("\n");
#endif
      } else {
        // not (p >= 0) is equivalent to (x <= constant - 1)
        q_sub_one(&solver->constant);
        add_ub_axiom(solver, x, &solver->constant, false);
#if TRACE
	printf("---> ");
	print_simplex_vardef(stdout, solver, x);
	printf("---> bound: ");
	print_simplex_var_bounds(stdout, solver, x);
	printf("\n");
#endif
      }
    }

  } else {
    negated = poly_buffer_make_monic(b);
#if TRACE
    printf("---> monic: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    x = decompose_and_get_var(solver);
    assert(! arith_var_is_int(&solver->vtbl, x));
    if (negated == tt) {
      // assert (p >= 0) <=> (x <= b) if tt
      // assert (p < 0)  <=> (x < b)  if !tt
      add_ub_axiom(solver, x, &solver->constant, !tt);
    } else {
      // assert (p >= 0) <=> (x >= b) if tt
      // assert (p < 0)  <=> (x > b) if !tt
      add_lb_axiom(solver, x, &solver->constant, !tt);
    }
  }
  return;

 done:
  reset_poly_buffer(b);
}




/**********************
 *  INTERNALIZATION   *
 *********************/

/*
 * TERM CONSTRUCTION
 */

/*
 * Create a new theory variable
 * - is_int indicates whether the variable should be an integer
 * - also add a matrix column
 */
thvar_t simplex_create_var(simplex_solver_t *solver, bool is_int) {
  thvar_t x;

  matrix_add_column(&solver->matrix);
  x = create_arith_var(&solver->vtbl, is_int);
  if (solver->eqprop != NULL) {
    eqprop_set_relevance(solver, x);
  }
  return x;
}


/*
 * Create a new variable that represents constant q
 * - add a matrix column if that's a new variable
 */
thvar_t simplex_create_const(simplex_solver_t *solver, rational_t *q) {
  poly_buffer_t *b;
  thvar_t x;
  bool new_var;

  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  poly_buffer_add_const(b, q);
  normalize_poly_buffer(b);
  x = get_var_for_poly(&solver->vtbl, poly_buffer_mono(b), poly_buffer_nterms(b), &new_var);
  if (new_var) {
    matrix_add_column(&solver->matrix);
    // set relevance mark in solver->eqprop
    if (solver->eqprop != NULL) {
      eqprop_set_relevance(solver, x);
    }
  }
  reset_poly_buffer(b);

  assert(trivial_variable(&solver->vtbl, x));

  return x;
}


/*
 * Create a theory variable equal to p
 * - arith_map maps variables of p to corresponding theory variables
 *   in the solver
 */
thvar_t simplex_create_poly(simplex_solver_t *solver, polynomial_t *p, thvar_t *map) {
#if TRACE
  thvar_t x;

  printf("\n---> simplex_create_poly: ");
  print_polynomial(stdout, p);
  printf("\n");
  rename_poly(solver, p, map);
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
  x = get_var_from_buffer(solver);
  printf("---> var: ");
  print_simplex_vardef(stdout, solver, x);
  printf("\n");

  return x;
#else
  rename_poly(solver, p, map);
  return get_var_from_buffer(solver);
#endif
}




/*
 * Placeholder for a power product p: raise an exception
 */
thvar_t simplex_create_pprod(simplex_solver_t *solver, pprod_t *p, thvar_t *map) {
  if (solver->env != NULL) {
    longjmp(*solver->env, FORMULA_NOT_LINEAR);
  }
  abort();
}

/*
 * Placeholder for a division.
 */
thvar_t simplex_create_rdiv(simplex_solver_t *solver, thvar_t num, thvar_t den) {
  if (solver->env != NULL) {
    longjmp(*solver->env, FORMULA_NOT_LINEAR);
  }
  abort();
}

/*
 * Attach egraph term t to a variable v
 * - v must not have an eterm attached already
 */
void simplex_attach_eterm(simplex_solver_t *solver, thvar_t v, eterm_t t) {
  attach_eterm_to_arith_var(&solver->vtbl, v, t);
  // propagate to the eq_propagator if it exists
  if (solver->eqprop != NULL) {
    eqprop_record_eterm(solver, v, t);
  }
}


/*
 * Get the egraph term t attached to v
 * - return null_eterm if v has no eterm attached
 */
eterm_t simplex_eterm_of_var(simplex_solver_t *solver, thvar_t v) {
  return arith_var_get_eterm(&solver->vtbl, v);
}


/*
 * ATOM CONSTRUCTION
 */

/*
 * Create the atom x >= 0
 * - this attach the atom to the smt_core
 */
literal_t simplex_create_ge_atom(simplex_solver_t *solver, thvar_t x) {
  poly_buffer_t *b;

  assert(valid_arith_var(&solver->vtbl, x));

  // replace x by its definition if it's a trivial variable
  b = &solver->buffer;
  add_var_or_subst(solver, b, x);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_create_ge_atom: ");
  print_simplex_var(stdout, solver, x);
  printf(" >= 0\n");
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  return make_ge_atom(solver);
}


/*
 * Create the atom p >= 0 and return the corresponding literal
 * - replace the variables of p as defined by map
 */
literal_t simplex_create_poly_ge_atom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map) {
  rename_poly(solver, p, map);

#if TRACE
  printf("\n---> simplex_create_poly_ge_atom: ");
  print_polynomial(stdout, p);
  printf(" >= 0\n");
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  return make_ge_atom(solver);
}



/*
 * Create the atom x == 0
 * - this attach the atom to the smt_core
 */
literal_t simplex_create_eq_atom(simplex_solver_t *solver, thvar_t x) {
  poly_buffer_t *b;

  // replace x by its definition if it's a trivial variable
  b = &solver->buffer;
  add_var_or_subst(solver, b, x);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_create_eq_atom: ");
  print_simplex_var(stdout, solver, x);
  printf(" == 0\n");
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  return make_eq_atom(solver);
}


/*
 * Create the atom p == 0
 * - apply the renaming defined by map
 */
literal_t simplex_create_poly_eq_atom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map) {
  rename_poly(solver, p, map);

#if TRACE
  printf("\n---> simplex_create_poly_eq_atom: ");
  print_polynomial(stdout, p);
  printf(" == 0\n");
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  return make_eq_atom(solver);
}

/*
 * Create the atom x - y == 0
 * - x and y are two theory variables
 */
literal_t simplex_create_vareq_atom(simplex_solver_t *solver, thvar_t x, thvar_t y) {
  poly_buffer_t *b;

  assert(valid_arith_var(&solver->vtbl, x) && valid_arith_var(&solver->vtbl, y));

  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  add_var_or_subst(solver, b, x);
  sub_var_or_subst(solver, b, y);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_create_vareq_atom: ");
  print_simplex_var(stdout, solver, x);
  printf(" == ");
  print_simplex_var(stdout, solver, y);
  printf("\n");
  printf("---> after subst: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  return make_eq_atom(solver);
}


/*
 * AXIOMS (BASE-LEVEL ASSERTIONS)
 */

/*
 * Assert a top-level inequality (either x >= 0 or x < 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x >= 0
 *   tt == false --> assert x < 0
 */
void simplex_assert_ge_axiom(simplex_solver_t *solver, thvar_t x, bool tt){
  poly_buffer_t *b;

  assert(valid_arith_var(&solver->vtbl, x));

  // replace x by its definition if it's a trivial variable
  b = &solver->buffer;
  add_var_or_subst(solver, b, x);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_assert_ge_axiom: ");
  print_simplex_var(stdout, solver, x);
  if (tt) {
    printf(" >= 0\n");
  } else {
    printf(" < 0\n");
  }
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  add_ge_axiom(solver, tt);
}


/*
 * Assert a top-level inequality (either p >= 0 or p < 0)
 * - map: convert p's variables to simplex variables
 * - tt indicates which of the two inequalities to assert
 */
void simplex_assert_poly_ge_axiom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  rename_poly(solver, p, map);

#if TRACE
  printf("\n---> simplex_assert_poly_ge_axiom: ");
  //  print_polynomial(stdout, p);
  print_simplex_buffer(stdout, solver);
  if (tt) {
    printf(" >= 0\n");
  } else {
    printf(" < 0\n");
  }
#endif

  add_ge_axiom(solver, tt);
}


/*
 * Assert a top-level equality constraint (either x == 0 or x != 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x == 0
 *   tt == false --> assert x != 0
 */
void simplex_assert_eq_axiom(simplex_solver_t *solver, thvar_t x, bool tt) {
  poly_buffer_t *b;

  assert(valid_arith_var(&solver->vtbl, x));

  // replace x by its definition if it's a trivial variable
  b = &solver->buffer;
  add_var_or_subst(solver, b, x);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_assert_eq_axiom: ");
  print_simplex_var(stdout, solver, x);
  if (tt) {
    printf(" == 0\n");
  } else {
    printf(" != 0\n");
  }
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  add_eq_or_diseq_axiom(solver, tt);
}


/*
 * Assert top-level equality or disequality (either p == 0 or p != 0)
 * - map: convert p's variables to simplex variables
 * - if tt is true  ---> assert p == 0
 * - if tt is false ---> assert p != 0
 */
void simplex_assert_poly_eq_axiom(simplex_solver_t *solver, polynomial_t *p, thvar_t *map, bool tt) {
  rename_poly(solver, p, map);

#if TRACE
  printf("\n---> simplex_assert_poly_eq_axiom: ");
  print_polynomial(stdout, p);
  if (tt) {
    printf(" == 0\n");
  } else {
    printf(" != 0\n");
  }
  printf("---> renaming: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  add_eq_or_diseq_axiom(solver, tt);
}


/*
 * If tt == true --> assert (x - y == 0)
 * If tt == false --> assert (x - y != 0)
 */
void simplex_assert_vareq_axiom(simplex_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  poly_buffer_t *b;

  assert(valid_arith_var(&solver->vtbl, x) && valid_arith_var(&solver->vtbl, y));

  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  add_var_or_subst(solver, b, x);
  sub_var_or_subst(solver, b, y);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_assert_vareq_axiom: ");
  print_simplex_buffer(stdout, solver);
  if (tt) {
    printf(" == 0\n");
  } else {
    printf(" != 0\n");
  }
#endif

  add_eq_or_diseq_axiom(solver, tt);
}


/*
 * Assert (c ==> x == y)
 */
void simplex_assert_cond_vareq_axiom(simplex_solver_t *solver, literal_t c, thvar_t x, thvar_t y) {
  poly_buffer_t *b;
  literal_t l, l1, l2;

  assert(valid_arith_var(&solver->vtbl, x) && valid_arith_var(&solver->vtbl, y));

  // compute polynomial p = (x - y)
  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  add_var_or_subst(solver, b, x);
  sub_var_or_subst(solver, b, y);
  normalize_poly_buffer(b);

#if TRACE
  printf("\n---> simplex_assert_cond_vareq_axiom: ");
  print_literal(stdout, c);
  printf(" implies ");
  print_simplex_var(stdout, solver, x);
  printf(" == ");
  print_simplex_var(stdout, solver, y);
  printf("\n");
  printf("rewritten to: ");
  print_literal(stdout, c);
  printf(" implies ");
  print_simplex_buffer(stdout, solver);
  printf(" == 0\n");
#endif

  l = simplify_eq_atom(solver, &l1, &l2);
  if (l == null_literal) {
    // l1 is (p >= 0) and l2 is (p <= 0)
    // assert (c ==> l1) and (c ==> l2)
    add_binary_clause(solver->core, not(c), l1);
    add_binary_clause(solver->core, not(c), l2);
  } else {
    assert(l == false_literal || l == true_literal);
    // if p == 0 is true, nothing to do
    // if p == 0 is false, assert (not c)
    if (l == false_literal) {
      add_unit_clause(solver->core, not(c));
    }
  }
}



/*
 * Assert (c[0] \/ ... \/ c[n-1] \/ x == y)
 */
void simplex_assert_clause_vareq_axiom(simplex_solver_t *solver, uint32_t n, literal_t *c, thvar_t x, thvar_t y) {
  poly_buffer_t *b;
  ivector_t *v;
  literal_t l, l1, l2;

  assert(valid_arith_var(&solver->vtbl, x) && valid_arith_var(&solver->vtbl, y));

  // compute polynomial p = (x - y)
  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  add_var_or_subst(solver, b, x);
  sub_var_or_subst(solver, b, y);
  normalize_poly_buffer(b);

  l = simplify_eq_atom(solver, &l1, &l2);
  if (l == null_literal) {
    // l1 is (p >= 0) and l2 is (p <= 0)
    // assert (c[0] \/ ... \/ c[n-1] \/ l1)
    //    and (c[0] \/ ... \/ c[n-1] \/ l2)

    v = &solver->aux_vector;
    assert(v->size == 0);
    ivector_copy(v, c, n);

    assert(v->size == n);
    ivector_push(v, l1);
    add_clause(solver->core, n+1, v->data);

    v->data[n] = l2;
    add_clause(solver->core, n+1, v->data);

    ivector_reset(v);

  } else {
    assert(l == false_literal || l == true_literal);
    // if p == 0 is true, nothing to do
    // if p == 0 is false, assert (c[0] \/ ... \/ c[n-1])
    if (l == false_literal) {
      add_clause(solver->core, n, c);
    }
  }
}



/*****************************************
 *  SIMPLIFICATION/TABLEAU CONSTRUCTION  *
 ****************************************/

/*
 * Record the initial statistics
 */
static void simplex_set_initial_stats(simplex_solver_t *solver) {
  solver->stats.num_init_vars = solver->vtbl.nvars;
  solver->stats.num_init_rows = solver->matrix.nrows;
  solver->stats.num_atoms = solver->atbl.natoms;
}


#if 0
/*
 * keep is a bitvector: mark all variables of p
 */
static void mark_vars_of_poly(byte_t *keep, polynomial_t *p) {
  uint32_t i, n;
  thvar_t x;

  n = p->nterms;
  for (i=0; i<n; i++) {
    x = p->mono[i].var;
    if (x != const_idx) {
      set_bit(keep, x);
    }
  }
}
#endif

/*
 * Simplify the matrix
 */
static void simplex_simplify_matrix(simplex_solver_t *solver) {
  uint32_t i, n;
  arith_vartable_t *vtbl;
  ivector_t *aux;
  byte_t *keep;
  byte_t *ivars;

#if TRACE_INIT
  printf("\n**** SIMPLIFYING THE MATRIX ****\n\n");
  print_simplex_matrix(stdout, solver);
  printf("==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n\n");
#endif

  /*
   * Mark the variables to keep
   */
  vtbl = &solver->vtbl;
  n = solver->vtbl.nvars;
  keep = allocate_bitvector0(n);  // default: all bits are 0

  if (solver->egraph != NULL && arith_vartable_has_eterms(vtbl)) {
    /*
     * We must keep at least any variable whose definition is the
     * difference of two e-terms. More generally, we assume the egraph
     * can dynamically create arbitrary linear combination of eterms.
     *
     * We could try to compute the set of variables whose definition
     * is a linear combination of eterms. Instead we keep everything.
     */
    for (i=1; i<n; i++) {
      set_bit(keep, i);
    }
  } else {
    for (i=1; i<n; i++) { // skip the constant
      if (!simplex_free_variable(solver, i) || arith_var_num_atoms(vtbl, i) > 0) {
	// i is constrained or has atoms attached: keep it
	set_bit(keep, i);
      }
    }
  }

  /*
   * Remove variables that have equal lower and upper bounds
   * Collect the unconstrained variables in aux
   */
  aux = &solver->aux_vector;
  assert(aux->size == 0);
  matrix_collect_constants(&solver->matrix);
  for (i=1; i<n; i++) { // skip const_idx == 0
    if (simplex_fixed_variable(solver, i)) {
#if TRACE_INIT
      printf("---> eliminate fixed variable ");
      print_simplex_var(stdout, solver, i);
      printf("\n");
#endif
      matrix_eliminate_fixed_variable(&solver->matrix, i, fixed_variable_value(solver, i));
    } else if (! tst_bit(keep, i)) {
      // i may be eliminated
      assert(simplex_eliminable_variable(solver, i));
      ivector_push(aux, i);
    }
  }
  matrix_cleanup_constants(&solver->matrix);

#if TRACE_INIT
  printf("---> %"PRIu32" rows after elim fixed vars.\n", solver->matrix.nrows);
  print_simplex_matrix(stdout, solver);
#endif

  /*
   * Eliminate unconstrained variables
   * - eliminated rows of the form x := constant are stored in solver->fvars
   * - other eliminated rows are stored in solver->elim
   */
  solver->stats.num_elim_candidates = aux->size;
  ivars = get_integer_vars_vector(&solver->vtbl); // set of integer variables
  simplify_matrix(&solver->matrix, aux->data, aux->size, ivars, &solver->elim, &solver->fvars);

  solver->stats.num_elim_rows = solver->elim.nrows;
  solver->stats.num_simpl_fvars = solver->fvars.nvars;
  solver->stats.num_simpl_rows = solver->matrix.nrows;

#if TRACE_INIT
  printf("---> %"PRIu32" rows after gauss. elim.\n", solver->matrix.nrows);
  printf("---> %"PRIu32" fixed variables detected\n\n", solver->fvars.nvars);
  print_simplex_matrix(stdout, solver);
  print_elim_matrix(stdout, &solver->vtbl, &solver->elim);
  print_simplex_vars(stdout, solver);
  printf("\n");
  print_simplex_bounds(stdout, solver);
  printf("\n");
  fflush(stdout);
#endif

  ivector_reset(aux);

  delete_bitvector(keep);
  delete_bitvector(ivars);
}



/*
 * Compute the initial tableau
 */
static void simplex_init_tableau(simplex_solver_t *solver) {
  assert(solver->matrix_ready);

  markowitz_tableau_construction(&solver->matrix, &solver->fvars);
  solver->stats.num_rows = solver->matrix.nrows;
  solver->stats.num_fixed_vars = solver->fvars.nvars;

#if TRACE_INIT
  printf("---> %"PRIu32" rows in initial tableau\n", solver->matrix.nrows);
  printf("---> %"PRIu32" fixed variables detected:\n\n", solver->fvars.nvars);
  print_fixed_var_vector(stdout, &solver->vtbl, &solver->fvars);
#endif

  // mark that the tableau is ready
  solver->tableau_ready = true;
  solver->matrix_ready = false;

  trace_printf(solver->core->trace, 12, "(initial tableau: %"PRIu32" rows, %"PRIu32" variables, %"PRIu32" atoms)\n",
	       solver->stats.num_rows, solver->vtbl.nvars, solver->atbl.natoms);

#if TRACE
  printf("\n==== Variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  printf("\n");
  fflush(stdout);
#endif
}


/*
 * Check the fixed variable vector and set the bounds on fixed variables
 * - also set the value of all fixed variables
 * - set unsat_before_search true if there's a conflict
 */
static void simplex_check_fixed_vars(simplex_solver_t *solver) {
  fvar_vector_t *v;
  rational_t *a;
  uint32_t i, n;
  int32_t x;

  v = &solver->fvars;
  n = v->nvars;

#if TRACE_INIT
  if (n > 0) {
    printf("\n---> CHECKING FIXED VARIABLES\n");
  }
#endif

  for (i=0; i<n; i++) {
    x = v->fvar[i].var;
    a = &v->fvar[i].value;

#if TRACE_INIT
    printf("\n---> checking ");
    print_simplex_var(stdout, solver, x);
    printf(" == ");
    q_print(stdout, a);
    printf("\n");
#endif

    assert(x >= 0);

    if (x == const_idx) {
      assert(q_is_zero(a));
      solver->unsat_before_search = true;
      return;
    }

    if (arith_var_is_int(&solver->vtbl, x) && ! q_is_integer(a)) {
      solver->unsat_before_search = true;
      return;
    }

    add_lb_axiom(solver, x, a, false);
    add_ub_axiom(solver, x, a, false);
    xq_set_q(arith_var_value(&solver->vtbl, x), a);
  }
}








/*************************
 *  VARIABLE ASSIGNMENT  *
 ************************/

/*
 * Invariant we want to maintain:
 * - for every non-basic variable x, val[x] is between the bounds on x
 * - for every non-basic variable x, the lb and ub flags for x are correct
 *   (lb_flag[x] = 1 iff val[x] = lower bound on x and
 *    ub_flag[x] = 1 iff val[x] = upper bound on x)
 * - the full assignment satisfies all the equations
 * - the heap infeasible_vars contains every basic variable x whose
 *   value is not within bounds.
 *
 * This invariant must hold before check_feasibility is called.
 */

/*
 * Set the ub/lb flags for a variable x
 */
static void simplex_set_bound_flags(simplex_solver_t *solver, thvar_t x) {
  uint8_t t;

  t = arith_var_tag(&solver->vtbl, x);
  t &= ~(AVARTAG_ATLB_MASK | AVARTAG_ATUB_MASK); // clear both bits
  if (variable_at_lower_bound(solver, x)) {
    t |= AVARTAG_ATLB_MASK;
  }
  if (variable_at_upper_bound(solver, x)) {
    t |= AVARTAG_ATUB_MASK;
  }
  set_arith_var_tag(&solver->vtbl, x, t);
}


/*
 * Clear both flags
 */
static void simplex_clear_bound_flags(simplex_solver_t *solver, thvar_t x) {
  uint8_t t;

  assert(!variable_at_lower_bound(solver, x) && !variable_at_upper_bound(solver, x));

  t = arith_var_tag(&solver->vtbl, x);
  t &= ~(AVARTAG_ATLB_MASK | AVARTAG_ATUB_MASK); // clear both bits
  set_arith_var_tag(&solver->vtbl, x, t);
}


/*
 * Compute the value of a basic variable x given a row
 * - it's computed so as to satisfy the equation row == 0
 * - store x in the heap if the bounds on x are not satisfied
 */
static void simplex_set_basic_var_value(simplex_solver_t *solver, thvar_t x, row_t *row) {
  arith_vartable_t *vtbl;
  xrational_t *v;
  uint32_t i, n;
  thvar_t y;

  vtbl = &solver->vtbl;
  v = arith_var_value(vtbl, x);
  xq_clear(v);
  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      /// monomial is a.y where a = data[i].coeff
      xq_submul(v, arith_var_value(vtbl, y), &row->data[i].coeff);
    }
  }

  if (! value_satisfies_bounds(solver, x)) {
#if TRACE_INIT
    printf("---> infeasible var: ");
    print_simplex_var(stdout, solver, x);
    printf("\n");
#endif
    int_heap_add(&solver->infeasible_vars, x);
  }
}


/*
 * Initial variable assignment:
 * - for every non-basic variable x:
 *   val[x] = lower bound on x if it exists
 *          or upper bound on x if it exists
 *          or 0
 * - for every basic variable, val[x] is computed from the matrix
 */
static void simplex_init_assignment(simplex_solver_t *solver) {
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  xrational_t *bound, *v;
  uint32_t n;
  int32_t i;
  thvar_t x;

  assert(int_heap_is_empty(&solver->infeasible_vars));

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;
  bound = solver->bstack.bound;

  // the constant should always have value = 1
  assert(xq_is_one(arith_var_value(vtbl, const_idx)));

  // assign all non-basic/non-constant variables
  n = vtbl->nvars;
  for (x=1; x<n; x++) {
    if (matrix_is_nonbasic_var(matrix, x)) {
#if 0
      i = arith_var_lower_index(vtbl, x);
      if (i < 0) {
        i = arith_var_upper_index(vtbl, x);
      }
#else
      // test: give priority to upper bound
      i = arith_var_upper_index(vtbl, x);
      if (i < 0) {
        i = arith_var_lower_index(vtbl, x);
      }
#endif

      v = arith_var_value(vtbl, x);
      if (i >= 0) {
        xq_set(v, bound + i);
        simplex_set_bound_flags(solver, x);
      } else {
	// we must clear the tags here (because they could be wrong after pop)
        xq_clear(v);
	simplex_clear_bound_flags(solver, x);
      }
    }
  }

  // propagate to the basic variables
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    x = matrix_basic_var(matrix, i);
    simplex_set_basic_var_value(solver, x, matrix_row(matrix, i));
  }

  // set the fix_ptr
  solver->bstack.fix_ptr = solver->bstack.top;
}



/*
 * Update the value of a non-basic variable x and propagate
 * to all basic variables that depend on x
 * - q = new value of x
 * - if a basic variable becomes infeasible, it's added to the heap
 */
static void update_non_basic_var_value(simplex_solver_t *solver, thvar_t x, xrational_t *q) {
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  xrational_t *v, *delta;
  column_t *col;
  uint32_t i, n;
  int32_t r, k;
  thvar_t y;

  vtbl = &solver->vtbl;
  delta = &solver->delta;
  v = arith_var_value(vtbl, x);  // current value of x

  assert(delta != q);

  xq_set(delta, q);
  xq_sub(delta, v);   // delta = new value - old value
  xq_set(v, q);       // value[x] := q

  matrix = &solver->matrix;
  col = matrix->column[x];

  if (col != NULL) {
    n = col->size;
    for (i=0; i<n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0) {
        y = matrix_basic_var(matrix, r);
        v = arith_var_value(vtbl, y);
        k = col->data[i].r_ptr;
        xq_submul(v, delta, matrix_coeff(matrix, r, k));

        // add y to the heap if the new value is not within its bounds
        if (! value_within_bounds(solver, y, v)) {
          int_heap_add(&solver->infeasible_vars, y);
        }
      }
    }
  }
}



/*
 * Update the value of non-basic var x to its lower or upper bound
 */
static void update_to_lower_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  assert(matrix_is_nonbasic_var(&solver->matrix, x));
  k = arith_var_lower_index(&solver->vtbl, x);
  assert(k >= 0);
  update_non_basic_var_value(solver, x, solver->bstack.bound + k);
  set_arith_var_lb(&solver->vtbl, x);
  if (variable_at_upper_bound(solver, x)) {
    set_arith_var_ub(&solver->vtbl, x);
  } else {
    clear_arith_var_ub(&solver->vtbl, x);
  }
}

static void update_to_upper_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  assert(matrix_is_nonbasic_var(&solver->matrix, x));
  k = arith_var_upper_index(&solver->vtbl, x);
  assert(k >= 0);
  update_non_basic_var_value(solver, x, solver->bstack.bound + k);
  set_arith_var_ub(&solver->vtbl, x);
  if (variable_at_lower_bound(solver, x)) {
    set_arith_var_lb(&solver->vtbl, x);
  } else {
    clear_arith_var_lb(&solver->vtbl, x);
  }
}



/*
 * Update the variable assignment after new bounds have been added
 * - the new bounds are in bstack queue (in bstack->bound[fix_ptr to top-1])
 * - the assignment is updated to make sure that the value of all
 *   non-basic variables is between their bounds
 * - also add all basic variables that are not within their bounds to the
 *   infeasible_vars heap
 */
static void simplex_fix_nonbasic_assignment(simplex_solver_t *solver) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  uint32_t i, n;
  int32_t cmp;
  thvar_t x;

#if TRACE
  printf("---> Simplex: update non-basic assignment\n");
#endif


  bstack = &solver->bstack;
  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  n = bstack->top;
  for (i = bstack->fix_ptr; i<n; i++) {
    x = bstack->var[i];
    if (constraint_is_lower_bound(bstack, i) && arith_var_lower_index(vtbl, x) == i) {
      /*
       * i is the current lower bound on x
       */
      cmp = xq_cmp(arith_var_value(vtbl, x), bstack->bound + i);
      if (cmp < 0) {
        // value < lower-bound
        if (matrix_is_nonbasic_var(matrix, x)) {
          // x is non-basic: correct its value
          update_to_lower_bound(solver, x);
#if TRACE
          printf("     val[");
          print_simplex_var(stdout, solver, x);
          printf("] := ");
          xq_print(stdout, arith_var_value(vtbl, x));
          printf("\n");
#endif
        } else {
          // x is basic: add it to the heap
          int_heap_add(&solver->infeasible_vars, x);
        }

      } else if (cmp == 0) {
        // value == lower-bound: set the lower-bound flag on x
        // this is required for non-basic vars and irrelevant for basic vars
        set_arith_var_lb(vtbl, x);
      }

    } else if (constraint_is_upper_bound(bstack, i) && arith_var_upper_index(vtbl, x) == i) {
      /*
       * i is the current upper bound on x
       */
      cmp = xq_cmp(arith_var_value(vtbl, x), bstack->bound + i);
      if (cmp > 0) {
        // value > upper bound
        if (matrix_is_nonbasic_var(matrix, x)) {
          // correct x's value
          update_to_upper_bound(solver, x);
#if TRACE
          printf("     val[");
          print_simplex_var(stdout, solver, x);
          printf("] := ");
          xq_print(stdout, arith_var_value(vtbl, x));
          printf("\n");
#endif
        } else {
          // x is basic: add it to the heap
          int_heap_add(&solver->infeasible_vars, x);
        }
      } else if (cmp == 0) {
        // value == upper bound: set the upper-bound flag on x
        set_arith_var_ub(vtbl, x);
      }
    }
  }

  // update fix_ptr
  bstack->fix_ptr = n;
  assert(bstack->fix_ptr == bstack->top);
}




/***************************************
 *  CONFLICTS: SETS OF BOUND INDICES   *
 **************************************/

/*
 * A conflict is a set of bounds that are mutually inconsistent.
 * The following functions builds a set of bounds in a vector.
 * In addition, every bound is marked by setting a bit in  the bound stack
 * for index k.
 */

/*
 * Check whether constraint k is marked
 */
static inline bool arith_cnstr_is_marked(arith_bstack_t *stack, int32_t k) {
  assert(0 <= k && k < stack->top);
  return arith_tag_mark(stack->tag[k]);
}

/*
 * Set the mark on constraint k
 */
static inline void arith_cnstr_set_mark(arith_bstack_t *stack, int32_t k) {
  assert(0 <= k && k < stack->top);
  stack->tag[k] |= ARITH_CNSTR_MARK_MASK;
}

/*
 * Clear the mark on constraint k
 */
static inline void arith_cnstr_clr_mark(arith_bstack_t *stack, int32_t k) {
  assert(0 <= k && k < stack->top);
  stack->tag[k] &= ~ARITH_CNSTR_MARK_MASK;
}


/*
 * Add index k into the explanation queue q if it's not there already
 * - all indices in the queue have a mark in stack
 */
static void enqueue_cnstr_index(ivector_t *q, int32_t k, arith_bstack_t *stack) {
  if (! arith_cnstr_is_marked(stack, k)) {
    ivector_push(q, k);
    arith_cnstr_set_mark(stack, k);
  }
}


/*
 * Enqueue all the elements of array a into q
 * - a must be an array of bound indices, terminated by -1
 */
static void enqueue_cnstr_array_indices(ivector_t *q, int32_t *a, arith_bstack_t *stack) {
  int32_t i;

  for (;;) {
    i = *a ++;
    if (i < 0) break;
    enqueue_cnstr_index(q, i, stack);
  }
}




/***********************
 *  FEASIBILITY CHECK  *
 **********************/

/*
 * Heuristic for selecting the entering variable:
 * - score of x = number of non-free basic variables that depend on x
 *    +  1 if x is not free
 *   (a variable is free if it has no upper or lower bound)
 * - the variable with smallest score is selected, ties are broken randomly
 *
 * The following function returns the score of x if it's smaller than best_score
 * or best_score + 1 otherwise.
 */
static uint32_t entering_var_score(simplex_solver_t *solver, thvar_t x, uint32_t best_score) {
  matrix_t *matrix;
  column_t *col;
  uint32_t i, n, score;
  int32_t r;
  thvar_t y;

  assert(0 <= x && x < solver->matrix.ncolumns &&
         x != const_idx && matrix_is_nonbasic_var(&solver->matrix, x));

  score = 0;
  if (! simplex_free_variable(solver, x)) {
    score ++;
    if (best_score == 0) goto done;
  }

  matrix = &solver->matrix;
  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0) {
      y = matrix_basic_var(matrix, r);
      assert(y >= 0);
      if (! simplex_free_variable(solver, y)) {
        score ++;
        if (score > best_score) goto done;
      }
    }
  }

 done:
  return score;
}



/*
 * Search for entering variable in a given row:
 * - x = basic variable in that row
 * - return the index of the chosen variable in the row
 *   or -1 if no variable was found
 *
 * There are two cases depending on whether the value of the
 * basic variable x must increase or decrease:
 * - if x must increase, the entering variable x_i must satisfy
 *    (a_i > 0 and value[x_i] > l_i) or (a_i < 0 and value[x_i] < u_i)
 * - if x must decrease, the entering variable x_i must satisfy
 *    (a_i < 0 and value[x_i] > l_i) or (a_i > 0 and value[x_i] > u_i)
 * where a_i = coefficient of x_i in the row
 *
 * If blands_rule is active, the entering variable is the one with smallest index,
 * otherwise, it's the one with smallest score.
 */


/*
 * Check whether y can be selected as entering variable when x must increase
 * - a = coefficient of y
 */
static bool possible_entering_var_for_increase(arith_vartable_t *vtbl, thvar_t y, rational_t *a) {
  uint8_t tag;

  assert(q_is_nonzero(a));

  tag = arith_var_tag(vtbl, y);
  if (q_is_pos(a)) {
    // a>0 and value[y] > lower bound on y
    return (tag & AVARTAG_ATLB_MASK) == 0;
  } else {
    // a<0 and value[y] < upper bound on y
    return (tag & AVARTAG_ATUB_MASK) == 0;
  }
}


/*
 * Search for an entering variable to increase x
 */
static int32_t find_entering_var_for_increase(simplex_solver_t *solver, row_t *row, thvar_t x) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t y;
  uint32_t score, best_score, k;
  int32_t best_i;

  vtbl = &solver->vtbl;

  n = row->size;

  best_i = -1;
  best_score = UINT32_MAX;

  if (solver->use_blands_rule) {

    // Bland's rule: score for y = y
    for (i=0; i<n; i++) {
      y = row->data[i].c_idx;
      if (y >= 0 && y != x && y < best_score &&
          possible_entering_var_for_increase(vtbl, y, &row->data[i].coeff)) {
        best_score = y;
        best_i = i;
      }
    }

  } else {

    k = 0; // stop GCC warning

    // Leonardo's heuristic
    for (i=0; i<n; i++) {
      y = row->data[i].c_idx;
      if (y >= 0 && y != x &&
          possible_entering_var_for_increase(vtbl, y, &row->data[i].coeff)) {
        score = entering_var_score(solver, y, best_score);

        if (score < best_score) {
          // better variable
          best_score = score;
          best_i = i;
          k = 1;
        } else if (score == best_score) {
          // pick uniformly among all variables with the same score
          k ++;
          if (random_uint(solver, k) == 0) {
            best_i = i;
          }
        }

      }
    }
  }

  assert(best_score < UINT32_MAX || best_i < 0);

  return best_i;
}


/*
 * Check whether y can be selected as entering variable when x must decrease
 * - a = coefficient of y
 */
static bool possible_entering_var_for_decrease(arith_vartable_t *vtbl, thvar_t y, rational_t *a) {
  uint8_t tag;

  assert(q_is_nonzero(a));

  tag = arith_var_tag(vtbl, y);
  if (q_is_neg(a)) {
    // a<0 and value[y] > lower bound on y
    return (tag & AVARTAG_ATLB_MASK) == 0;
  } else {
    // a>0 and value[y] < upper bound on y
    return (tag & AVARTAG_ATUB_MASK) == 0;
  }
}


/*
 * Search for an entering variable to decrease x
 */
static int32_t find_entering_var_for_decrease(simplex_solver_t *solver, row_t *row, thvar_t x) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t y;
  uint32_t score, best_score, k;
  int32_t best_i;

  vtbl = &solver->vtbl;

  n = row->size;

  best_i = -1;
  best_score = UINT32_MAX;

  if (solver->use_blands_rule) {

    // Bland's rule: score for y = y
    for (i=0; i<n; i++) {
      y = row->data[i].c_idx;
      if (y >= 0 && y != x && y < best_score &&
          possible_entering_var_for_decrease(vtbl, y, &row->data[i].coeff)) {
        best_score = y;
        best_i = i;
      }
    }

  } else {

    k = 0; // stop GCC warning

    // Leonardo's heuristic
    for (i=0; i<n; i++) {
      y = row->data[i].c_idx;
      if (y >= 0 && y != x &&
          possible_entering_var_for_decrease(vtbl, y, &row->data[i].coeff)) {
        score = entering_var_score(solver, y, best_score);

        if (score < best_score) {
          // better variable
          best_score = score;
          best_i = i;
          k = 1;
        } else if (score == best_score) {
          // pick uniformly among all variables with the same score
          k ++;
          if (random_uint(solver, k) == 0) {
            best_i = i;
          }
        }

      }
    }
  }

  assert(best_score < UINT32_MAX || best_i < 0);

  return best_i;
}


/*
 * Generate a conflict set for an infeasible row:
 * - x is the base variable in that row.
 * - x's value is smaller than x's lower bound.
 * - there are no entering variable in the row.
 *
 * Collect the bound indices from this row into solver->expl_queue + set marks.
 */
static void conflict_set_for_increase(simplex_solver_t *solver, row_t *row, thvar_t x) {
  arith_vartable_t *vtbl;
  ivector_t *v;
  thvar_t y;
  uint32_t i, n;
  int32_t k;

  vtbl = &solver->vtbl;

  // add bound indices to the explanation queue
  v = &solver->expl_queue;
  assert(v->size == 0);

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      if (q_is_pos(&row->data[i].coeff)) {
        // a>0: we need the explanation for the lower bound on y
        k = arith_var_lower_index(vtbl, y);
      } else {
        // a<0: we need the explanation for the upper bound on y
        k = arith_var_upper_index(vtbl, y);
      }
      enqueue_cnstr_index(v, k, &solver->bstack);
    }
  }

  // add index for (x >= l)
  enqueue_cnstr_index(v, arith_var_lower_index(vtbl, x), &solver->bstack);
}


/*
 * Same thing for the other case (can't decrease the value of x)
 * - x is the base variable in that row.
 * - x's value is smaller than x's lower bound.
 * - there are no entering variable in the row.
 *
 * Collect the bound indices from this row into solver->expl_queue + set marks.
 */
static void conflict_set_for_decrease(simplex_solver_t *solver, row_t *row, thvar_t x) {
  arith_vartable_t *vtbl;
  ivector_t *v;
  thvar_t y;
  uint32_t i, n;
  int32_t k;

  vtbl = &solver->vtbl;

  // add bound indices to expl_queue
  v = &solver->expl_queue;
  assert(v->size == 0);

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      if (q_is_pos(&row->data[i].coeff)) {
        // a>0: we need the explanation for the upper bound on y
        k = arith_var_upper_index(vtbl, y);
      } else {
        // a<0: we need the explanation for the lower bound on y
        k = arith_var_lower_index(vtbl, y);
      }
      enqueue_cnstr_index(v, k, &solver->bstack);
    }
  }

  // bounds contradict (x <= u)
  enqueue_cnstr_index(v, arith_var_upper_index(vtbl, x), &solver->bstack);
}


/*
 * Check for feasibility:
 * - search for an assignment that satisfies all the bounds
 * - return true if such an assignment is found
 * - return false if a conflict is detected
 *
 * Preconditions/invariant:
 * - the infeasible basic variables are stored in solver->infeasible_vars
 * - for every non-basic variable x, val[x] is between the bounds on x
 * - for every non-basic variable x, the lb and ub flags for x are correct
 *   (lb_flag[x] = 1 iff val[x] = lower bound on x and
 *    ub_flag[x] = 1 iff val[x] = upper bound on x)
 *
 * This invariant is maintained by this function.
 *
 * Result:
 * - if the function returns true, then the array val contains an assignment
 *   that satisfies all constraints. The heap solver->infeasible_vars is empty.
 * - if the function returns false, then invariant above is still satisfied
 *   in addition, a conflict set is stored in solver->expl_queue and every
 *   bound index is solver->expl_queue is marked.
 */
static bool simplex_check_feasibility(simplex_solver_t *solver) {
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  ivector_t *leaving_vars;
  row_t *row;
  thvar_t x;
  int32_t r, k;
  uint32_t repeats, loops, bthreshold;
  bool feasible;

#if TRACE
  printf("---> SIMPLEX: CHECK FEASIBILITY\n");
#endif

  matrix = &solver->matrix;
  vtbl = &solver->vtbl;

  /*
   * leaving variables are stored in aux_vector
   * and marked in vtbl
   */
  leaving_vars = &solver->aux_vector;
  assert(leaving_vars->size == 0);
  repeats = 0;
  solver->use_blands_rule = false;
  loops = 0;

  /*
   * Bland threshold: adjust it based on the number of variables
   */
  bthreshold = solver->bland_threshold;
  if (solver->vtbl.nvars > 10000) {
    bthreshold *= 1000;
  } else if (solver->vtbl.nvars > 1000) {
    bthreshold *= 100;
  }

  for (;;) {
    // check interrupt at every iteration
    if (solver->interrupted) {
      feasible = false;
      break;
    }

    if (tracing(solver->core->trace, 15)) {
      loops ++;
      if ((loops & 0xFFF) == 0) {
	trace_puts(solver->core->trace, 15, ".");
      }
    }

    x = int_heap_get_min(&solver->infeasible_vars);
    if (x < 0) {
      feasible = true;
      break;
    }

#if TRACE
    show_heap(stdout, solver);
#endif

    r = matrix_basic_row(matrix, x);
    row = matrix_row(matrix, r);
    k = -1;

    if (variable_below_lower_bound(solver, x)) {
      // find an entering variable that allows x to increase
      k = find_entering_var_for_increase(solver, row, x);
      if (k < 0) {
        // no entering variable ==> conflict
        conflict_set_for_increase(solver, row, x);
        int_heap_add(&solver->infeasible_vars, x); // x is still infeasible
        feasible = false;
        solver->last_conflict_row = r;
        break;
      } else {
        // pivot: make the entering variable basic
        matrix_pivot(matrix, r, k);
        update_to_lower_bound(solver, x);
        solver->stats.num_pivots ++;
      }

    } else if (variable_above_upper_bound(solver, x)) {
      // find an entering variable that allows x to decrease
      k = find_entering_var_for_decrease(solver, row, x);
      if (k < 0) {
        // no entering variable ==> conflict
        conflict_set_for_decrease(solver, row, x);
        int_heap_add(&solver->infeasible_vars, x); // x is still infeasible
        feasible = false;
        solver->last_conflict_row = r;
        break;
      } else {
        // pivot: make the entering variable basic
        matrix_pivot(matrix, r, k);
        update_to_upper_bound(solver, x);
        solver->stats.num_pivots ++;
      }
    }

    if (k >= 0 && !solver->use_blands_rule) {
      /*
       * Switch to Bland's rule after too many repeats
       * - repeat is incremented if x has left the basis in a previous
       *   pivoting round
       */
      if (! arith_var_is_marked(vtbl, x)) {
        set_arith_var_mark(vtbl, x);
        ivector_push(leaving_vars, x);
      } else {
        repeats ++;
        if (repeats > bthreshold) {
          solver->use_blands_rule = true;
          solver->stats.num_blands ++;
	  trace_printf(solver->core->trace, 15, "(activating bland's rule: %"PRIu32")\n", solver->stats.num_blands);
        }
      }
    }
  }

  // cleanup the marks
  r = leaving_vars->size;
  for (k=0; k<r; k++) {
    x = leaving_vars->data[k];
    clear_arith_var_mark(vtbl, x);
  }
  ivector_reset(leaving_vars);

  if (tracing(solver->core->trace, 15)) {
    if (loops > 0xFFF || solver->use_blands_rule) {
      trace_newline(solver->core->trace, 15);
    }
  }

#if TRACE
  if (feasible) {
    printf("---> Simplex: make feasible succeeded\n");
  } else {
    printf("---> Simplex: arithmetic conflict\n");
  }
#endif

  return feasible;
}





/******************
 *  EXPLANATIONS  *
 *****************/

/*
 * Add the explanation for (x1 == x2) to vector v
 * then remove duplicate literals from v.
 * - triple->var[0] = x1
 * - triple->var[1] = x2
 * - triple->id = egraph edge to explain the equality
 */
static void collect_egraph_eq_expl(simplex_solver_t *solver, egraph_expl_triple_t *triple, ivector_t *v) {
  eterm_t t1, t2;
  uint32_t n;

  t1 = arith_var_eterm(&solver->vtbl, triple->var[0]);
  t2 = arith_var_eterm(&solver->vtbl, triple->var[1]);
  n = v->size;
  egraph_explain_term_eq(solver->egraph, t1, t2, triple->id, v);
  if (n > 0) {
    ivector_remove_duplicates(v);
  }
}


/*
 * Expand the explanation queue: convert it to a conjunction of literals
 * - solver->expl_queue must contain a set of constraint indices
 * - a list of literals that explain all these constraints is added to v
 * - the conflict set is emptied: expl_queue is reset and all bound marks are removed.
 *
 * NOTE: We assume that egraph explanations and simplex explanations
 * never have common literals. This is true as long as the simplex
 * does not propagate equalities to the egraph.
 */
static void simplex_build_explanation(simplex_solver_t *solver, ivector_t *v) {
  arith_bstack_t *bstack;
  ivector_t *queue, *aux;
  uint8_t *tag;
  uint32_t k;
  int32_t i;

  queue = &solver->expl_queue;
  aux = &solver->expl_aux;  // to store literals from egraph explanations
  bstack = &solver->bstack;
  tag = bstack->tag;

  assert(queue != v && aux->size == 0);

  for (k=0; k<queue->size; k++) {
    i = queue->data[k];
    assert(arith_cnstr_is_marked(bstack, i));
    switch (arith_tag(tag[i])) {
    case ARITH_AXIOM_LB:
    case ARITH_AXIOM_UB:
      // nothing to do
      break;

    case ARITH_ASSERTED_LB:
    case ARITH_ASSERTED_UB:
      // add literal explanation to v
      ivector_push(v, bstack->expl[i].lit);
      break;

    case ARITH_DERIVED_LB:
    case ARITH_DERIVED_UB:
      // add antecedents to the queue
      enqueue_cnstr_array_indices(queue, bstack->expl[i].ptr, bstack);
      solver->stats.num_prop_expl ++;
      break;

    case ARITH_EGRAPHEQ_LB:
    case ARITH_EGRAPHEQ_UB:
      // add explanation from the egraph into aux
      collect_egraph_eq_expl(solver, bstack->expl[i].ptr, aux);
      break;

    default:
      abort();
      break;
    }
  }


  // add literals of aux into v
  ivector_add(v, aux->data, aux->size);
  ivector_reset(aux);

  ivector_remove_duplicates(v);  // TEST

  // cleanup the marks and empty the queue
  for (k=0; k<queue->size; k++) {
    i = queue->data[k];
    arith_cnstr_clr_mark(bstack, i);
  }
  ivector_reset(queue);
}




/*
 * Add explanation for bound k into vector v
 * - the explanation is a conjunction of literals
 */
static void simplex_explain_bound(simplex_solver_t *solver, int32_t k, ivector_t *v) {
  ivector_t *queue;

  queue = &solver->expl_queue;
  assert(queue->size == 0);
  enqueue_cnstr_index(queue, k, &solver->bstack);
  simplex_build_explanation(solver, v);
}



/*
 * Negate all literals in v
 * - this turns a conflict explanation (l_1 and .... and l_n) ==> false
 *   into the clause (\not l1) or ... or (not l_n)
 */
static void convert_expl_to_clause(ivector_t *v) {
  uint32_t i, n;
  literal_t *a;

  n = v->size;
  a = v->data;
  for (i=0; i<n; i++) {
    a[i] = not(a[i]);
  }
}


/*
 * Build a conflict clause from the content of the explanation queue
 * and store it in v.
 * - queue must contain a set of bound indices (that is inconsistent)
 * - this is expanded first into a conjunction of literals (inconsistent)
 * - then this is turned into a clause
 */
static void simplex_build_conflict_clause(simplex_solver_t *solver, ivector_t *v) {
#if TRACE
  uint32_t i, j, n;
  literal_t l;
  bool show;
  void *atom;
#endif

  assert(v->size == 0);
  simplex_build_explanation(solver, v);
  convert_expl_to_clause(v);
#if TRACE
  show = true;
  n = v->size;
  if (show) {
    printf("---> Simplex: conflict clause (size = %"PRIu32")\n", n);
    show = false;
  }
  for (i=0; i<n; i++) {
    printf(" ");
    print_literal(stdout, v->data[i]);
  }
  printf("\n");
  for (i=0; i<n; i++) {
    l = v->data[i];
    atom = bvar_atom(solver->core, var_of(l));
    if (atom != NULL) {
      printf("    ");
      print_literal(stdout, l);
      printf(" := ");
      if (atom_tag(atom) == ARITH_ATM_TAG) {
	print_simplex_atom_of_literal(stdout, solver, l);
      } else {
	print_egraph_atom_of_literal(stdout, solver->egraph, l);
      }
      printf("\n");
    }
  }
  printf("\n");
  for (j=i+1; j<n; j++) {
    if (v->data[i] == v->data[j]) {
      printf("     duplicate literal: %"PRId32" (at index %"PRIu32" and %"PRIu32")\n", v->data[i], i, j);
    }
  }
#endif
}


/*
 * Convert a conflict set to a clause and report the conflict to the core
 * - the conflict set is in solver->expl_queue.
 * - the conflict clause is stored in solver->expl_vector
 */
static void simplex_report_conflict(simplex_solver_t *solver) {
  ivector_t *v;

  // translate the queue into a conjunction of literals (stored in expl_vector);
  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_build_conflict_clause(solver, v);

#if 0
  printf("\n---> SIMPLEX CONFLICT: not feasible\n");
#endif
  // record expl_vector as a conflict (first add the null-literal terminator)
  ivector_push(v, null_literal);
  record_theory_conflict(solver->core, v->data);

  solver->stats.num_conflicts ++;
}




/*
 * EXPLANATIONS FOR EQUALITIES SENT TO THE EGRAPH
 */

/*
 * Add the two bounds for x to q (unless they are marked)
 */
static void enqueue_frozen_var_constraints(simplex_solver_t *solver, ivector_t *q, thvar_t x) {
  int32_t l, u;

  assert(simplex_fixed_variable(solver, x));

  l = arith_var_lower_index(&solver->vtbl, x);
  u = arith_var_upper_index(&solver->vtbl, x);
  enqueue_cnstr_index(q, l, &solver->bstack);
  enqueue_cnstr_index(q, u, &solver->bstack);
}


/*
 * For an equality (x1 == x2) received from the egraph, add the corresponding egraph equality
 * (t1 == t2) to result.
 * - triple->var[0] = x1
 * - triple->var[1] = x2
 * - triple->id = egraph edge that caused (x1 == x2)
 */
static void explain_vareq_from_egraph(simplex_solver_t *solver, egraph_expl_triple_t *triple, th_explanation_t *result) {
  eterm_t t1, t2;

  t1 = arith_var_eterm(&solver->vtbl, triple->var[0]);
  t2 = arith_var_eterm(&solver->vtbl, triple->var[1]);
  th_explanation_add_eq(result, t1, t2);
}


/*
 * Expand the explanation queue and build a theory explanation object for the egraph
 * - queue must contain a set of constraint indices that imply an equality (x1 == x2)
 *   that was propagated to the egraph.
 * - the queue is emptied and all constraint marks are cleared
 */
static void simplex_build_theory_explanation(simplex_solver_t *solver, ivector_t *queue, th_explanation_t *result) {
  arith_bstack_t *bstack;
  uint8_t *tag;
  uint32_t k;
  int32_t i;

  bstack = &solver->bstack;
  tag = bstack->tag;

  for (k=0; k<queue->size; k++) {
    i = queue->data[k];
    assert(arith_cnstr_is_marked(bstack, i));
    switch (arith_tag(tag[i])) {
    case ARITH_AXIOM_LB:
    case ARITH_AXIOM_UB:
      // nothing to do
      break;

    case ARITH_ASSERTED_LB:
    case ARITH_ASSERTED_UB:
      // add literal explanation to result
      th_explanation_add_atom(result, bstack->expl[i].lit);
      break;

    case ARITH_DERIVED_LB:
    case ARITH_DERIVED_UB:
      // add antecedents to the queue
      enqueue_cnstr_array_indices(queue, bstack->expl[i].ptr, bstack);
      solver->stats.num_prop_expl ++;
      break;

    case ARITH_EGRAPHEQ_LB:
    case ARITH_EGRAPHEQ_UB:
      // add eq to the result
      explain_vareq_from_egraph(solver, bstack->expl[i].ptr, result);
      break;

    default:
      abort();
      break;
    }
  }

  // remove duplicates in result
  cleanup_th_explanation(result);

  // cleanup the marks and empty the queue
  for (k=0; k<queue->size; k++) {
    i = queue->data[k];
    arith_cnstr_clr_mark(bstack, i);
  }
  ivector_reset(queue);
}


/*
 * Build an explanation for the egraph
 * - this function is called by the egraph when it needs the explanation for (x1 == x2)
 * - expl is NULL (we ignore it)
 * - the explanation must be stored in result
 * - when this function is called, result is empty
 */
static void simplex_expand_th_explanation(simplex_solver_t *solver, thvar_t x1, thvar_t x2, void *expl, th_explanation_t *result) {
  eq_propagator_t *eqprop;
  ivector_t *queue, *v;
  uint32_t i, n;

  eqprop = solver->eqprop;
  assert(eqprop != NULL);

  /*
   * collect the relevant frozen variables in aux
   */
  v = &eqprop->aux;
  ivector_reset(v);
  offset_manager_explain_equality(&eqprop->mngr, x1, x2, v);

  /*
   * All variables in eqprop->aux are frozen: add explanation for them
   * to eqprop->expl_queue
   */
  queue = &eqprop->expl_queue;
  assert(queue->size == 0);
  n = v->size;
  for (i=0; i<n; i++) {
    enqueue_frozen_var_constraints(solver, queue, v->data[i]);
  }

  // build the explanation from the queue then reset the queue
  simplex_build_theory_explanation(solver, queue, result);

#if 0
  printf("---> simplex provides explanation for g!%"PRId32" == g!%"PRId32"\n",
	 arith_var_eterm(&solver->vtbl, x1), arith_var_eterm(&solver->vtbl, x2));
  printf("     antecedents: ");
  print_theory_explanation(stdout, result);
  printf("\n");
  fflush(stdout);
#endif
}




/*********************************
 *  TOP-LEVEL FEASIBILITY CHECK  *
 ********************************/

/*
 * This function checks whether the bounds are consistent.  It
 * constructs a feasible solution if they are and return true.
 * Otherwsie, it builds a conflict clause and add it to the core
 * otherwise, and it returns false.
 *
 * Preconditions: same as simplex_check_feasibility.
 */
static bool simplex_make_feasible(simplex_solver_t *solver) {
  bool feasible;

#if DEBUG
  check_nonbasic_assignment(solver);
  check_vartags(solver);
  check_infeasible_vars(solver);
  check_integer_bounds(solver);
  check_bound_marks(solver);
#endif

  solver->stats.num_make_feasible ++;
  feasible = simplex_check_feasibility(solver);
  if (!feasible) {
    simplex_report_conflict(solver);
  }

#if DEBUG
  check_bound_marks(solver);
  check_vartags(solver);
  if (feasible) {
    check_assignment(solver);
  } else {
    check_nonbasic_assignment(solver);
  }

#endif

  return feasible;
}





/********************************
 *  ADD LOWER AND UPPER BOUNDS  *
 *******************************/

/*
 * Construct a simple conflict when we have bound k ==> (not l)
 * - the conflict clause is stored in solver->expl_vector
 */
static void record_simple_conflict(simplex_solver_t *solver, int32_t k, literal_t l) {
  ivector_t *v;

  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_explain_bound(solver, k, v);

  /*
   * negate literals in v to turn (l1 and ... and l_m ==> (not l))
   * into the clause (or (not l1) ... (not l_m) (not l))
   */
  convert_expl_to_clause(v);
  ivector_push(v, not(l));

#if 0
  if (is_pos(l)) {
    printf("\n---> SIMPLEX CONFLICT: bound %"PRId32" => ~p!%"PRId32"\n", k, var_of(l));
  } else {
    printf("\n---> SIMPLEX CONFLICT: bound %"PRId32" => p!%"PRId32"\n", k, var_of(l));
  }
#endif
  // add the end marker
  ivector_push(v, null_literal);
  record_theory_conflict(solver->core, v->data);

  solver->stats.num_conflicts ++;
}


/*
 * Add a lower bound: x >= c or x > c
 * - x = variable
 * - c = rational bound
 * - strict indicates whether the bound is strict or not
 * - l = explanation (literal)
 *
 * return true if the bound is consistent
 * return false if the  bound is inconsistent with the existing
 * upper bound on x.
 */
static bool add_lower_bound(simplex_solver_t *solver, thvar_t x, rational_t *c, bool strict, literal_t l) {
  arith_vartable_t *vtbl;
  xrational_t *b;
  int32_t k;

  vtbl = &solver->vtbl;

  // store the bound as an extended rational
  b = &solver->bound;
  xq_set_q(b, c);
  if (strict) {
    if (arith_var_is_int(vtbl, x)) {
      // bound is c+1
      assert(q_is_integer(c));
      xq_add_one(b);
    } else {
      // bound is c+delta
      xq_add_delta(b);
    }
  }

#if TRACE
  printf("---> checking bound: ");
  print_simplex_var(stdout, solver, x);
  printf(" >= ");
  xq_print(stdout, b);
  printf("\n");
#endif


  k = arith_var_upper_index(vtbl, x);
  if (k >= 0 && xq_lt(solver->bstack.bound + k, b)) {
    // conflict: current upper bound on x is less than b
    record_simple_conflict(solver, k, l);

#if TRACE
    printf("---> conflict with bound ");
    print_simplex_bound(stdout, solver, k);
    printf("\n");
#endif

    return false;
  }

  k = arith_var_lower_index(vtbl, x);
  if (k < 0 || xq_lt(solver->bstack.bound + k, b)) {
    // the new bound is not redundant
    push_lb_assertion(solver, x, b, l);

#if TRACE
    printf("---> added ");
    print_simplex_bound(stdout, solver, solver->bstack.top - 1);
    printf("\n");
  } else {
    printf("---> redundant\n");
#endif

  }

  return true;
}


/*
 * Add a upper bound: x <= c or x < c
 * - x = variable
 * - c = rational bound
 * - strict indicates whether the bound is strict or not
 * - l = explanation (literal)
 *
 * return true if the bound is consistent
 * return false if the  bound is inconsistent with the existing
 * lower bound on x.
 */
static bool add_upper_bound(simplex_solver_t *solver, thvar_t x, rational_t *c, bool strict, literal_t l) {
  arith_vartable_t *vtbl;
  xrational_t *b;
  int32_t k;

  vtbl = &solver->vtbl;

  // store the bound as an extended rational
  b = &solver->bound;
  xq_set_q(b, c);
  if (strict) {
    if (arith_var_is_int(vtbl, x)) {
      // bound is c-1
      assert(q_is_integer(c));
      xq_sub_one(b);
    } else {
      // bound is c-delta
      xq_sub_delta(b);
    }
  }


#if TRACE
  printf("---> checking bound: ");
  print_simplex_var(stdout, solver, x);
  printf(" <= ");
  xq_print(stdout, b);
  printf("\n");
#endif

  k = arith_var_lower_index(vtbl, x);
  if (k >= 0 && xq_gt(solver->bstack.bound + k, b)) {
    // conflict: current lower bound on x is more than b
    record_simple_conflict(solver, k, l);

#if TRACE
    printf("---> conflict with bound ");
    print_simplex_bound(stdout, solver, k);
    printf("\n");
#endif

    return false;
  }

  k = arith_var_upper_index(vtbl, x);
  if (k < 0 || xq_gt(solver->bstack.bound + k, b)) {
    // the new bound is not redundant
    push_ub_assertion(solver, x, b, l);

#if TRACE
    printf("---> added ");
    print_simplex_bound(stdout, solver, solver->bstack.top - 1);
    printf("\n");
  } else {
    printf("---> redundant\n");
#endif

  }

  return true;
}





/***********************************
 *   PROCESS THE ASSERTION QUEUE   *
 **********************************/

/*
 * Code for switch label when processing an asserted atom
 * - the code is 2 bits for the atom type (GE, LE, EQ)
 *   + 1 bit to indicate whether the atom is asserted true or false
 * - the codes depend on the encoding used by arithatm_tag_t:
 *   GE_ATM = 00, LE_ATM = 01, EQ_ATM = 10
 */
typedef enum atom_process_code {
  GE_TRUE,   // 000
  GE_FALSE,  // 001
  LE_TRUE,   // 010
  LE_FALSE,  // 011
  EQ_TRUE,   // 100
  EQ_FALSE,  // 101
} atom_process_code_t;

static inline atom_process_code_t procode(arithatm_tag_t tag, uint32_t sgn_bit) {
  assert(sgn_bit == 0 || sgn_bit == 1);
  return (atom_process_code_t) ((tag << 1)|sgn_bit);
}


/*
 * Process assertion a = atom index + sign bit
 * - return true if no conflict is found
 * - return false if a conflict is found (i.e., if the assertion is
 *   incompatible with an existing bound)
 */
static bool simplex_process_assertion(simplex_solver_t *solver, int32_t a) {
  arith_atom_t *atom;
  int32_t id;
  thvar_t x;
  bvar_t z;
  bool ok;

  id = atom_of_assertion(a);
  atom = arith_atom(&solver->atbl, id);
  x = var_of_atom(atom);
  z = boolvar_of_atom(atom);


#if TRACE
  printf("---> processing assertion: ");
  print_simplex_atom(stdout, solver, id);
  if (assertion_is_true(a)) {
    printf("  (true)\n");
  } else {
    printf("  (false)\n");
  }
#endif


  switch (procode(tag_of_atom(atom), sign_of_assertion(a))) {
  case GE_TRUE:  // x>=b
    ok = add_lower_bound(solver, x, bound_of_atom(atom), false, pos_lit(z));
    break;
  case GE_FALSE: // x<b
    ok = add_upper_bound(solver, x, bound_of_atom(atom), true, neg_lit(z));
    break;
  case LE_TRUE:  // x<=b
    ok = add_upper_bound(solver, x, bound_of_atom(atom), false, pos_lit(z));
    break;
  case LE_FALSE: // x>b
    ok = add_lower_bound(solver, x, bound_of_atom(atom), true, neg_lit(z));
    break;
  case EQ_TRUE:  // x == b: should never occur
  case EQ_FALSE:
  default:
    abort();
    break;
  }

  return ok;
}


/*
 * Process all assertions in the queue
 * - add the asserted bound and update the assignment
 * - return true if no conflict is found
 * - return false if a conflict is found. If so, a conflict clause
 *   is added to the core.
 */
static bool simplex_process_assertions(simplex_solver_t *solver) {
  arith_astack_t *astack;
  uint32_t p;

  astack = &solver->assertion_queue;
  for (p=astack->prop_ptr; p<astack->top; p++) {
    if (! simplex_process_assertion(solver, astack->data[p])) {
      return false;
    }
  }

  assert(p == astack->top);
  astack->prop_ptr = p;

  return true;
}





/**************************************************
 *  LITERALS IMPLIED BY AXIOMS OR DERIVED BOUNDS  *
 *************************************************/

/*
 * Record that atom atm or its negation is implied by bound i
 * - l = implied literal = either pos_lit(x) or neg_lit(x) where x = boolean variable of atm
 */
static void simplex_implied_literal(simplex_solver_t *solver, int32_t atm, int32_t i, literal_t l) {
  aprop_t *expl;

  assert(var_of(l) == boolvar_of_atom(arith_atom(&solver->atbl, atm)));

  /*
   * If we're at the base level, just assert l
   * Otherwise, propagate l with i as antecedent
   */
  if (solver->base_level == solver->decision_level) {
    add_unit_clause(solver->core, l);
  } else {
    expl = make_simplex_prop_object(solver, i);
    propagate_literal(solver->core, l, expl);
    solver->stats.num_props ++;
  }

  // mark that atm is assigned and push the assertion into the assertion stack
  push_assertion(&solver->assertion_queue, mk_assertion(atm, sign_of(l)));
  mark_arith_atom(&solver->atbl, atm);

}



/*
 * Scan all atoms in atom vector v (all are atoms on a variable x)
 * - if any of them is implied by the constraint (x >= a) then propagate it to the core
 * - i = index of the bound (x >= a)
 */
static void check_lower_bound_implications(simplex_solver_t *solver, uint32_t i, xrational_t *a, int32_t *v) {
  arith_atomtable_t *atbl;
  arith_atom_t *p;
  uint32_t n, j;
  int32_t atm;

  atbl = &solver->atbl;
  n = iv_size(v);
  for (j=0; j<n; j++) {
    atm = v[j];
    if (arith_atom_is_unmarked(atbl, atm)) {
      p = arith_atom(atbl, atm);
      assert(var_of_atom(p) == solver->bstack.var[i]);
      switch (tag_of_atom(p)) {
      case GE_ATM:
        /*
         * x >= a implies x >= b  if a >= b
         */
        if (xq_ge_q(a, bound_of_atom(p))) {

#if TRACE
          printf("---> atom[%"PRId32"]:\t", atm);
          print_simplex_atom(stdout, solver, atm);
          printf("\t\tis true by ");
          print_simplex_bound(stdout, solver, i);
          printf("\n");
#endif
          simplex_implied_literal(solver, atm, i, pos_lit(boolvar_of_atom(p)));

        }
        break;
      case LE_ATM:
      case EQ_ATM:
        /*
         * x >= a implies (not x <= b) if a > b
         * x >= a implies (not x == b) if a > b
         */
        if (xq_gt_q(a, bound_of_atom(p))) {

#if TRACE
          printf("---> atom[%"PRId32"]:\t", atm);
          print_simplex_atom(stdout, solver, atm);
          printf("\t\tis false by ");
          print_simplex_bound(stdout, solver, i);
          printf("\n");
#endif
          simplex_implied_literal(solver, atm, i, neg_lit(boolvar_of_atom(p)));
        }
        break;
      }
    }
  }
}


/*
 * Same thing for the constraint (x <= a)
 */
static void check_upper_bound_implications(simplex_solver_t *solver, uint32_t i, xrational_t *a, int32_t *v) {
  arith_atomtable_t *atbl;
  arith_atom_t *p;
  uint32_t n, j;
  int32_t atm;

  atbl = &solver->atbl;
  n = iv_size(v);
  for (j=0; j<n; j++) {
    atm = v[j];
    if (arith_atom_is_unmarked(atbl, atm)) {
      p = arith_atom(atbl, atm);
      assert(var_of_atom(p) == solver->bstack.var[i]);
      switch (tag_of_atom(p)) {
      case LE_ATM:
        /*
         * x <= a implies x <= b  if a <= b
         */
        if (xq_le_q(a, bound_of_atom(p))) {

#if TRACE
          printf("---> atom[%"PRId32"]:\t", atm);
          print_simplex_atom(stdout, solver, atm);
          printf("\t\tis true by ");
          print_simplex_bound(stdout, solver, i);
          printf("\n");
#endif

          simplex_implied_literal(solver, atm, i, pos_lit(boolvar_of_atom(p)));
        }
        break;
      case GE_ATM:
      case EQ_ATM:
        /*
         * x <= a implies (not x >= b) if a < b
         * x <= a implies (not x == b) if a < b
         */
        if (xq_lt_q(a, bound_of_atom(p))) {

#if TRACE
          printf("---> atom[%"PRId32"]:\t", atm);
          print_simplex_atom(stdout, solver, atm);
          printf("\t\tis false by ");
          print_simplex_bound(stdout, solver, i);
          printf("\n");
#endif

          simplex_implied_literal(solver, atm, i, neg_lit(boolvar_of_atom(p)));
        }
        break;
      }
    }
  }
}




/*
 * Propagation: find all literals implied by new bounds
 * - scan the bound queue from bstack->prop_ptr to bstack->top-1
 */
static void simplex_literal_propagation(simplex_solver_t *solver) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  int32_t *atom_vector;
  uint32_t i;
  thvar_t x;

  assert(solver->assertion_queue.prop_ptr == solver->assertion_queue.top &&
         solver->bstack.fix_ptr == solver->bstack.top);

  bstack = &solver->bstack;
  vtbl = &solver->vtbl;

  for (i = bstack->prop_ptr; i<bstack->top; i++) {
    x = bstack->var[i];
    atom_vector = arith_var_atom_vector(vtbl, x);
    if (atom_vector != NULL) {
      /*
       * bound[i] is a constraint on x
       */
      if (constraint_is_lower_bound(bstack, i)) {
        check_lower_bound_implications(solver, i, bstack->bound + i, atom_vector);
      } else {
        assert(constraint_is_upper_bound(bstack, i));
        check_upper_bound_implications(solver, i, bstack->bound + i, atom_vector);
      }
    }
  }

  assert(i == bstack->top);
  bstack->prop_ptr = i;

  // update prop_ptr in the assertion queue to skip the implied atoms
  solver->assertion_queue.prop_ptr = solver->assertion_queue.top;
}






/*********************************************
 *  HELPER FUNCTIONS FOR THEORY PROPAGATION  *
 ********************************************/

/*
 * Record a conflict between an existing bound j and an implied bound
 * - v = explanation for the implied bound = a set of bound indices
 * - j = bound index
 * There are two cases of conflict:
 * 1) v implies (x >= b) and (u < b) where u = current upper bound on x
 *    then j = index of the constraint (x <= u) in the bstack
 * 2) v implies (x <= b) and (l > b) where l = current lower bound on x
 *    then j = index of the constraint (x >= l) in the bstack
 */
static void record_derived_conflict(simplex_solver_t *solver, int32_t j, ivector_t *v) {
  uint32_t i, n;
  ivector_t *q;

  // add j and all elements of v into the queue
  q = &solver->expl_queue;
  assert(q->size == 0 && q != v);
  enqueue_cnstr_index(q, j, &solver->bstack);
  n = v->size;
  for (i=0; i<n; i++) {
    enqueue_cnstr_index(q, v->data[i], &solver->bstack);
  }

  // expand into a conjunction of literals
  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_build_explanation(solver, v);

  convert_expl_to_clause(v);
  ivector_push(v, null_literal);
  record_theory_conflict(solver->core, v->data);

  solver->stats.num_conflicts ++;
}



/*
 * Check whether b is larger than the current lower bound on x
 */
static bool improved_lower_bound(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_bstack_t *bstack;
  int32_t k;

  bstack = &solver->bstack;
  k = arith_var_lower_index(&solver->vtbl, x);
  return  k < 0 || xq_lt(bstack->bound + k, b);
}


/*
 * Check whether b is smaller than the current upper bound on x
 */
static bool improved_upper_bound(simplex_solver_t *solver, thvar_t x, xrational_t *b) {
  arith_bstack_t *bstack;
  int32_t k;

  bstack = &solver->bstack;
  k = arith_var_upper_index(&solver->vtbl, x);
  return k < 0 || xq_gt(bstack->bound + k, b);
}


/*
 * Add a derived bound (x >= b) with explanation stored in *v
 * - v must be a set of bound indices that imply (x >= b)
 * - b must be better than the current lower bound on x
 * Return true if the new bound does not cause a conflict;
 * return false and record a theory conflict otherwise.
 *
 * The new bound may cause val[x] to no longer be between the
 * lower and upper bounds on x. If that's the case, the function
 * set the global flag solver->recheck to true.
 */
static bool simplex_add_derived_lower_bound(simplex_solver_t *solver, thvar_t x, xrational_t *b, ivector_t *v) {
  int32_t *a, k;
  uint32_t i, n;

  assert(improved_lower_bound(solver, x, b));

  // Strengthen the bound to ceil(b) if x is an integer
  if (arith_var_is_int(&solver->vtbl, x)) {
    xq_ceil(b);
  }

  // Check for conflict
  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0 && xq_lt(solver->bstack.bound + k, b)) {
    // conflict: ub[x] = bound[k] < b
    record_derived_conflict(solver, k, v);
    return false;
  }

  // Make a copy of v in the arena (add -1 as a terminator)
  n = v->size;
  a = (int32_t *) arena_alloc(&solver->arena, (n+1) * sizeof(literal_t));
  for (i=0; i<n; i++) {
    a[i] = v->data[i];
  }
  a[i] = -1;

  // Add the bound
  push_lb_derived(solver, x, b, a);

#if TRACE_INTFEAS
  printf("---> Derived bound\n");
  print_simplex_bound(stdout, solver, arith_var_lower_index(&solver->vtbl, x));
  printf("\n");
  fflush(stdout);
#endif

  /*
   * Check whether val[x] is still within bounds (i.e., val[x] >= b holds)
   */
  if (xq_ge(b, arith_var_value(&solver->vtbl, x))) {
    // b >= val[x]: set the recheck flag
    solver->recheck = true;
  }

  solver->stats.num_bound_props ++;

  return true;
}


/*
 * Add a derived bound (x <= b) with explanation stored in *v
 * - v must be a set of bound indices that imply (x <= b)
 * - b must be better than the current upper bound on x
 * Return true if the new bound does not cause a conflict.
 * Return false if the new bound causes a conflict.
 *
 * Set solver->recheck to true if val[x] is no longer within bounds
 */
static bool simplex_add_derived_upper_bound(simplex_solver_t *solver, thvar_t x, xrational_t *b, ivector_t *v) {
  int32_t *a, k;
  uint32_t i, n;

  assert(improved_upper_bound(solver, x, b));

  // Strengthen the bound to floor(b) if x is an integer
  if (arith_var_is_int(&solver->vtbl, x)) {
    xq_floor(b);
  }

  // Check for conflict
  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0 && xq_gt(solver->bstack.bound + k, b)) {
    // conflict: lb[x] = bound[k] > b
    record_derived_conflict(solver, k, v);
    return false;
  }

  // make a copy of v in the arena (add -1 as a terminator)
  n = v->size;
  a = (int32_t *) arena_alloc(&solver->arena, (n+1) * sizeof(literal_t));
  for (i=0; i<n; i++) {
    a[i] = v->data[i];
  }
  a[i] = -1;

  // Add the bound
  push_ub_derived(solver, x, b, a);

#if TRACE_INTFEAS
  printf("---> Derived bound\n");
  print_simplex_bound(stdout, solver, arith_var_upper_index(&solver->vtbl, x));
  printf("\n");
  fflush(stdout);
#endif

  /*
   * Check whether val[x] is still within bounds (i.e., val[x] <= b holds)
   */
  if (xq_le(b, arith_var_value(&solver->vtbl, x))) {
    // b <= val[x]: set the recheck flag
    solver->recheck = true;
  }

  solver->stats.num_bound_props ++;

  return true;
}



/*********************
 *  DERIVED BOUNDS   *
 ********************/

/*
 * Check whether we can derive a lower or upper bound on x from the row where x is basic
 * - x must be a basic variable
 * - if lower is true, this checks for a lower bound. Otherwise the function checks
 *   for an upper bound.
 *
 * The row is of the form  x + sum of monomials == 0
 * - we can derive a lower bound on x if all the monomials have an upper bound
 *   (namely x >= - sum of monomials' upper bounds)
 * - we can derive an upper bound on x if all the monomials have a lower bound
 *   (namely x <= - sum of monomials' lower bounds)
 */
static bool simplex_basic_var_has_derived_bound(simplex_solver_t *solver, thvar_t x, bool lower) {
  arith_vartable_t *vtbl;
  row_t *row;
  int32_t k;
  uint32_t i, n;
  thvar_t y;

  vtbl = &solver->vtbl;

  k = matrix_basic_row(&solver->matrix, x);
  assert(k >= 0); // i.e., x is a basic variable
  row = matrix_row(&solver->matrix, k);

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      /*
       * monomial a * y where a = row->data[i].coeff
       * - if lower is true, we check whether a * y has an upper bound
       *   (i.e., a>0 and y has an upper bound or a<0 and y has a lower bound)
       * - if lower is false, we check whether a * y has a lower bound
       *   (i.e., a>0 and y has a lower bound or a>0 and y has an upper bound)
       */
      if (q_is_pos(&row->data[i].coeff) == lower) {
	k = arith_var_upper_index(vtbl, y);
      } else {
	k = arith_var_lower_index(vtbl, y);
      }
      if (k < 0) return false;
    }
  }

  return true;
}


/*
 * Compute the derived lower or upper bound on x
 * - x must be a basic variable
 * - if lower is true, the function computes the lower bound,
 *   otherwise it computes the upper bound.
 * - the bound is returned in b
 *
 * - If v is non-null, the antecedents (bounds that imply x <= b or x >= b) are added to vector v
 */
static void simplex_derived_bound_on_basic_var(simplex_solver_t *solver, thvar_t x, bool lower, xrational_t *b, ivector_t *v) {
  arith_vartable_t *vtbl;
  row_t *row;
  int32_t k;
  uint32_t i, n;
  thvar_t y;

  vtbl = &solver->vtbl;

  k = matrix_basic_row(&solver->matrix, x);
  assert(k >= 0); // i.e., x is a basic variable
  row = matrix_row(&solver->matrix, k);

  xq_clear(b);

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      // monomial a * y where a = row->data[i].coeff
      if (q_is_pos(&row->data[i].coeff) == lower) {
	k = arith_var_upper_index(vtbl, y);
      } else {
	k = arith_var_lower_index(vtbl, y);
      }
      assert(k >= 0);
      xq_addmul(b, solver->bstack.bound + k, &row->data[i].coeff);
      if (v != NULL) ivector_push(v, k);
    }
  }

  xq_neg(b);
}


/*
 * Wrapper: don't get antecedents
 */
static inline void simplex_get_derived_bound_on_basic_var(simplex_solver_t *solver, thvar_t x, bool lower, xrational_t *b) {
  simplex_derived_bound_on_basic_var(solver, x, lower, b, NULL);
}





/*
 * DERIVED BOUNDS ON NON-BASIC VARIABLES
 */

/*
 * Check whether row r implies a bound on variable x
 * - index ptr = where variable x occurs in the row
 * - we must have row->data[ptr].c_idx == x
 * - if lower is true, this checks for a lower bound on x, otherwise
 *   this checks for an upper bound.
 *
 * The row has the form (a.x + sum of monomials == 0) so
 * we have a.x = - (sum of monomials).
 *
 * If a<0 then
 * - implied lower bound for x = - (lower bound on sum)/a
 * - implied upper bound for x = - (upper bound on sum)/a
 *
 * If a>0 then
 * - implied lower bound for x = - (upper bound on sum)/a
 * - implied upper bound for x = - (lower bound on sum)/a
 */
static bool simplex_row_implies_bound_on_var(simplex_solver_t *solver, row_t *row, thvar_t x, int32_t ptr, bool lower) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  int32_t k;
  thvar_t y;

  assert(row->data[ptr].c_idx == x);

  vtbl = &solver->vtbl;

  if (q_is_neg(&row->data[ptr].coeff)) {
    // x has a negative coefficient, we flip the flag lower.
    lower = !lower;
  }

  /*
   * If lower is true, this loop checks whether all monomials other than a.x
   * have an un upper bound. If lower is false, it checks whether all monomials
   * other than a.x have a lower bound.
   */
  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      if (q_is_pos(&row->data[i].coeff) == lower) {
	k = arith_var_upper_index(vtbl, y);
      } else {
	k = arith_var_lower_index(vtbl, y);
      }
      if (k < 0) return false;
    }
  }

  return true;
}


/*
 * Compute a derived bound on x implied by row
 * - x must occur in the row at index ptr
 * - the row must imply a bound (as checked by the previous function)
 * - if lower is true, the function computes a lower bound on x, otherwise it computes an upper bound.
 * - the resulting bound is stored in *b
 */
static void simplex_bound_on_var_implied_by_row(simplex_solver_t *solver, row_t *row, thvar_t x, int32_t ptr, bool lower, xrational_t *b) {
  arith_vartable_t *vtbl;
  int32_t k;
  uint32_t i, n;
  thvar_t y;

  assert(row->data[ptr].c_idx == x);

  vtbl = &solver->vtbl;

  if (q_is_neg(&row->data[ptr].coeff)) {
    // x has a negative coefficient, we flip the flag lower.
    lower = !lower;
  }

  xq_clear(b);

  /*
   * The row is (a.x) + sum = 0.
   *
   * If lower is true, this loop computes an upper bound on sum
   * If lower is false, this loop computes a lower bound on sum
   */
  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      // monomial a * y where a = row->data[i].coeff
      if (q_is_pos(&row->data[i].coeff) == lower) {
	k = arith_var_upper_index(vtbl, y);
      } else {
	k = arith_var_lower_index(vtbl, y);
      }
      assert(k >= 0);
      xq_addmul(b, solver->bstack.bound + k, &row->data[i].coeff);
    }
  }

  // bound on x is - (bound on sum)/a
  xq_neg(b);
  xq_div(b, &row->data[ptr].coeff);
}


/*
 * Collect antecedents for an implied bound on x
 * - same parameters as the previous function.
 * - the antecedents are added to vector v
 */
static void simplex_explain_bound_implied_by_row(simplex_solver_t *solver, row_t *row, thvar_t x, int32_t ptr, bool lower, ivector_t *v) {
  arith_vartable_t *vtbl;
  int32_t k;
  uint32_t i, n;
  thvar_t y;

  assert(row->data[ptr].c_idx == x);

  vtbl = &solver->vtbl;

  if (q_is_neg(&row->data[ptr].coeff)) {
    // x has a negative coefficient, we flip the flag lower.
    lower = !lower;
  }

  /*
   * The row is (a.x) + sum = 0.
   *
   * If lower is true, this loop collects upper bound on monomials of sum
   * If lower is fales, this loop collects lower bound on monomials of sum
   */
  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0 && y != x) {
      // monomial a * y where a = row->data[i].coeff
      if (q_is_pos(&row->data[i].coeff) == lower) {
	k = arith_var_upper_index(vtbl, y);
      } else {
	k = arith_var_lower_index(vtbl, y);
      }
      assert(k >= 0);
      ivector_push(v, k);
    }
  }
}


/*
 * Check whether bound b1 is stronger than b2.
 * - if lower is true --> b1 > b2
 * - otherwise b1 < b2
 */
static bool better_bound(xrational_t *b1, xrational_t *b2, bool lower) {
  int c;
  c = xq_cmp(b1, b2);
  return lower ? c>0 : c<0;
}


/*
 * Test whether the basic variable in row r has a bound (lower or upper)
 */
static bool base_var_has_bound(simplex_solver_t *solver, int32_t r) {
  thvar_t x;

  x = matrix_basic_var(&solver->matrix, r);
  return arith_var_upper_index(&solver->vtbl, x) >= 0 || arith_var_lower_index(&solver->vtbl, x) >= 0;
}


/*
 * Computes a derived bound on variable x and asserts it if it's better than the current bound on x
 * - if lower is true, this attempts to add a lower bound
 * - if lower is false, this attempts to add an upper bound.
 * - returns false if the new bound causes a conflict (and adds a theory conflict in the core)
 * - returns true otherwise.
 * - the flag solver->recheck is set to true if val[x] is no-longer within the bounds on x
 */
static bool simplex_strengthen_bound_on_var(simplex_solver_t *solver, thvar_t x, bool lower) {
  xrational_t *bound;
  xrational_t *aux;
  column_t *col;
  row_t *row;
  ivector_t *v;
  uint32_t i, n;
  int32_t best_r, r;
  int32_t best_ptr, ptr;
  bool ok;

  best_r = -1;
  best_ptr = -1;
  bound = &solver->bound;
  aux = &solver->xq0;

  ok = true;
  col = matrix_column(&solver->matrix, x);
  if (col != NULL) {
    /*
     * Get the strongest derived bound on x
     */
    n = col->size;
    for (i=0; i<n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0 && base_var_has_bound(solver, r)) {
	row = matrix_row(&solver->matrix, r);
	ptr = col->data[i].r_ptr;
	// x occurs in row r at index ptr
	if (simplex_row_implies_bound_on_var(solver, row, x, ptr, lower)) {
	  simplex_bound_on_var_implied_by_row(solver, row, x, ptr, lower, aux);
	  if (best_r < 0 || better_bound(aux, bound, lower)) {
	    // aux is stronger than the current best bound
	    best_r = r;
	    best_ptr = ptr;
	    xq_set(bound, aux);
	  }
	}
      }
    }

    /*
     * assert the bound if it's better than the existing upper/lower bound on x
     */
    if (best_r >= 0) {
      v = &solver->aux_vector;
      assert(v->size == 0);

      if (lower) {
	if (improved_lower_bound(solver, x, bound)) {
	  row = matrix_row(&solver->matrix, best_r);
	  simplex_explain_bound_implied_by_row(solver, row, x, best_ptr, lower, v);
	  ok = simplex_add_derived_lower_bound(solver, x, bound, v);
	}
      } else {
	if (improved_upper_bound(solver, x, bound)) {
	  row = matrix_row(&solver->matrix, best_r);
	  simplex_explain_bound_implied_by_row(solver, row, x, best_ptr, lower, v);
	  ok = simplex_add_derived_upper_bound(solver, x, bound, v);
	}
      }

      ivector_reset(v); // must ensure that aux_vector is empty
    }

  }

  return ok;
}


/*
 * Attempt to strengthen the bounds on all non-basic variables.
 * - return false if that causes a conflict (and add a theory conflict)
 * - return true otherwise
 * - sets solver->recheck to true if some variables are no-longer within their bounds
 */
static bool simplex_strengthen_bounds_on_non_basic_vars(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  bool ok;

  ok = true;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;

  // nothing to do for variable 0 (constant index)
  for (i=1; i<n; i++) {
    if (matrix_is_nonbasic_var(&solver->matrix, i)) {
      ok = simplex_strengthen_bound_on_var(solver, i, true)
	&& simplex_strengthen_bound_on_var(solver, i, false);
      if (!ok) {
	// conflict detected
	break;
      }
    }
  }

  return ok;
}


/*
 * Computes a derived bound on basic variable x and asserts it if it's better than x's current bound.
 * - if lower is true: this tries to strengthen the lower bound
 * - if lower is false: tries to strengthen the upper bound
 * - returns false if the new bound causes a conflict (and add a theory conflict in the core)
 * - returns true otherwise
 */
static bool simplex_strengthen_bound_on_basic_var(simplex_solver_t *solver, thvar_t x, bool lower) {
  xrational_t *bound;
  ivector_t *v;
  bool ok;

  ok = true;
  bound = &solver->bound;
  v = &solver->aux_vector;
  assert(v->size == 0);

  if (simplex_basic_var_has_derived_bound(solver, x, lower)) {
    simplex_derived_bound_on_basic_var(solver, x, lower, bound, v);

    if (lower) {
      if (improved_lower_bound(solver, x, bound)) {
	ok = simplex_add_derived_lower_bound(solver, x, bound, v);
      }
    } else {
      if (improved_upper_bound(solver, x, bound)) {
	ok = simplex_add_derived_upper_bound(solver, x, bound, v);
      }
    }

    ivector_reset(v);
  }

  return ok;
}


/*
 * Attempt to strengthen the bounds on all basic variables.
 * - return false if that causes a conflict (adds a theory conflict in the core)
 * - return true otherwise
 */
static bool simplex_strengthen_bounds_on_basic_vars(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  bool ok;

  ok = true;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;

  // nothing to do for variable 0 (constant index)
  for (i=1; i<n; i++) {
    if (matrix_is_basic_var(&solver->matrix, i)) {
      ok = simplex_strengthen_bound_on_basic_var(solver, i, true)
	&& simplex_strengthen_bound_on_basic_var(solver, i, false);
      if (!ok) {
	// conflict detected
	break;
      }
    }
  }

  return ok;
}



/*
 * Attempt to strengthen all the bounds
 * - one pass for the non-basic variables + one pass for the basic variables
 */
static bool simplex_strengthen_bounds(simplex_solver_t *solver) {
  return simplex_strengthen_bounds_on_non_basic_vars(solver) && simplex_strengthen_bounds_on_basic_vars(solver);
}


#if 0

// NOT USED
/*
 * Several rounds of strengthening
 * - MAX_STRENGTHEN_ITERS  = maximal number of rounds
 * - the function returns false if bound strengthening caused a conflict
 */
#define MAX_STRENGTHEN_ITERS 2

static bool simplex_strengthen_bounds_iter(simplex_solver_t *solver) {
  uint32_t nb, i;

  for (i=0; i<MAX_STRENGTHEN_ITERS; i++) {
    nb = solver->bstack.top;
    if (!simplex_strengthen_bounds(solver)) return false;
    // quit if the last round didn't find any new bound
    if (nb == solver->bstack.top) break;
  }

  return true;
}

#endif


/******************************
 *  PROPAGATOR INCLUDED HERE  *
 *****************************/

#include "solvers/simplex/simplex_propagator1.h"






/***********************************
 *  REBUILD THE CONSTRAINT MATRIX  *
 **********************************/

/*
 * Delete the tableau + elimination matrices etc.
 */
static void simplex_reset_tableau(simplex_solver_t *solver) {
  if (solver->tableau_ready) {
    assert(solver->save_rows);

    reset_elim_matrix(&solver->elim);
    reset_fvar_vector(&solver->fvars);
    reset_matrix(&solver->matrix);

    // clear statistics
    solver->stats.num_elim_rows = 0;
    solver->stats.num_simpl_fvars = 0;
    solver->stats.num_simpl_rows = 0;

    // reset the propagator if any
    if (solver->propagator != NULL) {
      simplex_reset_propagator(solver);
    }

    // reset the diophantine subsolver if any
    if (solver->dsolver != NULL) {
      reset_dsolver(solver->dsolver);
    }

    solver->tableau_ready = false;
  }
}


/*
 * Prepare for new assertions:
 * - rebuild the constraint matrix as it was before the previous call to
 *   start_search (modulo reordering; the rows may be permuted)
 * - we must make sure the rows are added in chronological order:
 *   all rows created at base_level 0 must come first,
 *   then all rows created at base_level 1 and so forth.
 */
static void simplex_restore_matrix(simplex_solver_t *solver) {
  arith_trail_t *trail;
  pvector_t *v;
  polynomial_t *p;
  uint32_t i, n, ns, nv;

  if (! solver->matrix_ready) {
    assert(solver->save_rows && solver->matrix.nrows == 0 &&
           solver->matrix.ncolumns == 0);

    // rebuild n empty columns in the matrix
    matrix_add_columns(&solver->matrix, solver->vtbl.nvars);

    /*
     * Restore rows from the trail stack:
     * - for each base_level i,
     *   tail->nvars = number of variables
     *   tail->nsaved_rows = number of polynomials in solver->saved_rows
     * (these counters are saved when we leave base_level i and enter i+1)
     */

    v = &solver->saved_rows;

    ns = 0; // number of saved rows added so far
    nv = 1; // number of variables visited so far (we start with 1 to skip const_idx)

    n = solver->trail_stack.top;
    trail = solver->trail_stack.data;
    assert(n == solver->base_level);

    for (i=0; i<n; i++) {
      // saved rows for level i
      while (ns < trail->nsaved_rows) {
	assert(ns < v->size);
	p = v->data[ns];
	matrix_add_row(&solver->matrix, p->mono, p->nterms);
	ns ++;
      }

      // definition rows for level i
      while (nv < trail->nvars) {
	p = arith_var_def(&solver->vtbl, nv);
	if (p != NULL && !simple_poly(p)) {
	  matrix_add_eq(&solver->matrix, nv, p->mono, p->nterms);
	}
	nv ++;
      }

      trail ++;
    }

    /*
     * Restore rows added at the current base level
     */
    while (ns < v->size) {
      p = v->data[ns];
      matrix_add_row(&solver->matrix, p->mono, p->nterms);
      ns ++;
    }

    n = solver->vtbl.nvars;
    while (nv < n) {
      p = arith_var_def(&solver->vtbl, nv);
      if (p != NULL && !simple_poly(p)) {
        matrix_add_eq(&solver->matrix, nv, p->mono, p->nterms);
      }
      nv ++;
    }

    // mark that the matrix is ready
    solver->matrix_ready = true;
  }

}






/**************************************
 *  ADDITION OF VARIABLES ON THE FLY  *
 *************************************/

/*
 * Decompose the buffer into (p + a) where a is the constant term
 * - store the opposite of a into solver->constant
 * - return a variable x equal to p
 * - reset the buffer
 *
 * If a new variable x is created, add a row to the tableau and make x basic
 * and also compute the value of x in the simplex assignment.
 */
static thvar_t decompose_and_get_dynamic_var(simplex_solver_t *solver) {
  poly_buffer_t *b;
  matrix_t *matrix;
  thvar_t x;
  int32_t r;
  bool new_var;

  assert(solver->tableau_ready);

  b = &solver->buffer;

  poly_buffer_get_neg_constant(b, &solver->constant); // store -a, b is (p + a)
  x = poly_buffer_nonconstant_convert_to_var(b);      // check whether p is a variable
  if (x < 0) {
    x = get_var_for_poly_offset(&solver->vtbl, poly_buffer_mono(b), poly_buffer_nterms(b), &new_var);
    if (new_var) {
      matrix = &solver->matrix;
      // add a new column to the matrix`
      assert(x == matrix->ncolumns);
      matrix_add_column(matrix);

      // add a row and make x basic
      poly_buffer_clear_const(b); // now b is equal to p
      poly_buffer_substitution(b, matrix); // substitute basic variables of b
      normalize_poly_buffer(b);
      matrix_add_tableau_eq(matrix, x, poly_buffer_mono(b), poly_buffer_nterms(b));

      // compute the value of x
      r = matrix_basic_row(matrix, x);
      assert(0 <= r && r < matrix->nrows);
      simplex_set_basic_var_value(solver, x, matrix_row(matrix, r));

      // set the relevance bit in eqprop if present
      if (solver->eqprop != NULL) {
	eqprop_set_relevance(solver, x);
      }

#if TRACE
      printf("     new simplex variable: ");
      print_simplex_vardef(stdout, solver, x);
#endif
    }
  }
  reset_poly_buffer(b);

  return x;
}



/*
 * Build a polynomial p such that (x1 == x2) is equivalent to p == 0
 * then check whether p == 0 simplifies to true or false.
 * - normalize p as much as possible
 * Results:
 * - p is stored (normalized) in solver->buffer
 * - if p == 0 simplifies, the result is true_literal or false_literal
 * - otherwise, the returned value is null_literal
 */
static literal_t simplify_dynamic_vareq(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  poly_buffer_t *b;
  bool is_int;

#if TRACE
  printf("---> Simplex: simplify dynamic vareq: ");
  print_simplex_var(stdout, solver, x1);
  printf(" == ");
  print_simplex_var(stdout, solver, x2);
  printf("\n---> ");
  print_simplex_vardef(stdout, solver, x1);
  printf("---> ");
  print_simplex_vardef(stdout, solver, x2);
#endif

  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);

  add_var_or_subst(solver, b, x1);
  sub_var_or_subst(solver, b, x2);
  normalize_poly_buffer(b);

#if TRACE
  printf("---> buffer: ");
  print_simplex_buffer(stdout, solver);
  printf("\n");
#endif

  if (poly_buffer_is_zero(b)) {
#if TRACE
    printf("---> vareq is true\n");
#endif
    return true_literal;
  }

  if (poly_buffer_is_nzconstant(b)) {
#if TRACE
    printf("---> vareq is false\n");
#endif
    return false_literal;
  }

  is_int = all_integer_vars(solver);
  if (is_int) {
    poly_buffer_make_integral(b);
#if TRACE
    printf("---> int scaling: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
    if (! poly_buffer_gcd_test(b)) {
#if TRACE
      printf("---> vareq is false by GCD test\n");
#endif
      return false_literal;
    }
  } else {
    poly_buffer_make_monic(b); // make lead coefficient = 1
#if TRACE
    printf("---> monic: ");
    print_simplex_buffer(stdout, solver);
    printf("\n");
#endif
  }

  return null_literal;
}





/**************************
 *  INTEGER FEASIBILITY   *
 *************************/

/*
 * Check whether all integer variables have an integer value
 */
static bool simplex_assignment_integer_valid(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(vtbl, i) && ! arith_var_value_is_int(vtbl, i)) {
      return false;
    }
  }

  return true;
}


#if TRACE_BB
/*
 * Number of integer variables with a non-integer value
 */
static uint32_t simplex_num_integer_invalid_vars(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n, c;

  c = 0;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(vtbl, i) && ! arith_var_value_is_int(vtbl, i)) {
      c ++;
    }
  }

  return c;
}
#endif


/*
 * Check whether the system has integer variables other than the constant
 * (const_idx ==0)
 */
static bool simplex_has_integer_vars(simplex_solver_t *solver) {
  return num_integer_vars(&solver->vtbl) > 1;
}


/*
 * Check whether the system mixes integer and non-integer variables
 */
static bool simplex_is_mixed_system(simplex_solver_t *solver) {
  uint32_t k;
  k = num_integer_vars(&solver->vtbl);
  return 1 < k && k < num_arith_vars(&solver->vtbl);
}


/*
 * Search for a variable in row that is non-integer and not fixed
 * - return its index k in the row (i.e., row->data[k].c_idx is a non-integer variable)
 *   or -1 if all variables are integer
 * Note: We can substitute any fixed variable by its value, since the value of
 * a fixed variable is always a rational (never an extended rational).
 */
static int32_t find_real_var_in_row(simplex_solver_t *solver, row_t *row) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0 && ! arith_var_is_int(vtbl, x) && ! simplex_fixed_variable(solver, x)) {
      return i;
    }
  }
  return -1;
}


/*
 * Make integer variables non-basic (as much as possible)
 * - this preserves feasibility
 * - after this, if x is a basic integer variable in a row i then all variables
 *   of row i are integer.
 */
static void make_integer_vars_nonbasic(simplex_solver_t *solver) {
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  row_t *row;
  thvar_t x;
  uint32_t i, n;
  int32_t k;

  matrix = &solver->matrix;
  vtbl = &solver->vtbl;

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    x = matrix_basic_var(matrix, i);
    assert(x >= 0);
    if (arith_var_is_int(vtbl, x)) {
      // check whether row i contains a non-integer variable y
      // if so make y basic
      row = matrix_row(matrix, i);
      k = find_real_var_in_row(solver, row);
      if (k >= 0) {
        matrix_pivot(matrix, i, k);
        solver->stats.num_pivots ++;

        // make sure the ub/lb flags for x are correct
        simplex_set_bound_flags(solver, x);
      }
    }
  }
}


/*
 * Search for a feasible assignment where all non-basic integer variables
 * have an integer value. Return true if such an assignment is found,
 * false otherwise.
 *
 * We do this in two steps:
 * 1) assign an integer value to the non-basic, integer variables
 * 2) call make_feasible
 *
 * Step 2 may change the set of non-basic variables, but it maintains
 * the property that all non-basic integer variables are assigned an
 * integer value (because any variable that leaves the basis is assigned
 * a value equal to its lower or upper bound).
 *
 * If the tableau is feasible when this function is called, then step 1
 * may construct an infeasible solution but step 2 restores feasibility.
 * So the function returns true in such a case.
 */
static bool assign_integers_to_nonbasic_vars(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  xrational_t *aux;
  uint32_t i, n;

  // we can use solver->bound here
  aux = &solver->bound;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(vtbl, i) && matrix_is_nonbasic_var(&solver->matrix, i) &&
        ! arith_var_value_is_int(vtbl, i)) {
      /*
       * update value[i] to the ceil and set ub tag if needed
       * (since value[i] is not an integer and upper the bound on i is an integer,
       * ceil[value[i]] is within bounds).
       */
      xq_set(aux, arith_var_value(vtbl, i));
      xq_ceil(aux);
      update_non_basic_var_value(solver, i, aux);
      if (variable_at_upper_bound(solver, i)) {
        set_arith_var_ub(vtbl, i);
      }
      assert(value_satisfies_bounds(solver, i));
    }
  }

  return simplex_make_feasible(solver);
}




#ifndef NDEBUG
/*
 * For debugging: check that all the integer variables that don't have an integer value
 * are basic.
 */
static bool non_integer_vars_are_basic(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(vtbl, i) && ! arith_var_value_is_int(vtbl, i) &&
	matrix_is_nonbasic_var(&solver->matrix, i)) {
      return false;
    }
  }

  return true;
}

#endif


/*
 * Prepare for integer solving:
 * - make sure all non-basic integer variables have an integer value
 * - so all the integer-infeasible variables are in the basis
 */
static void prepare_for_integer_solving(simplex_solver_t *solver) {
  // move non-integer variables to the basis
  if (simplex_is_mixed_system(solver)) {
    make_integer_vars_nonbasic(solver);
  }

#if TRACE_INTFEAS
  printf("\nMOVED NON-INTEGER VARIABLES TO THE BASIS\n\n");
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif

  // assign an integer value to all non-basic variables
  if (! assign_integers_to_nonbasic_vars(solver)) {
    abort();
  }

#if TRACE_INTFEAS
  printf("\nASSIGNED INTEGER VALUES TO NON_BASIC INTEGER VARIABLES\n\n");
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif

  assert(non_integer_vars_are_basic(solver));

#if DEBUG
  check_assignment(solver);
  check_vartags(solver);
#endif
}




#if 0

// NOT USED FOR NOW

/*
 * Search for a feasible assignment that maps all non-basic variables
 * to their upper or lower bound (except the variables that don't have bounds).
 * Return true if such an assignment is found, false otherwise.
 *
 * This is done in two steps, as in the previous function.
 */
static bool move_nonbasic_vars_to_bounds(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (matrix_is_nonbasic_var(&solver->matrix, i) && ! arith_var_at_bound(vtbl, i)) {
      if (arith_var_lower_index(vtbl, i) >= 0) {
        update_to_lower_bound(solver, i);
      } else if (arith_var_upper_index(vtbl, i) >= 0) {
        update_to_upper_bound(solver, i);
      }
    }
  }

  return simplex_make_feasible(solver);
}

#endif



/*
 * NAIVE GREEDY SEARCH
 */

/*
 * Naive search: attempt to make all the columns in the tableau integral
 * by adjusting the values of the non-basic variables.
 */

/*
 * Heuristic: check whether the problem looks underconstrained
 * - we count the number of variables with no upper or no lower bound
 */
static uint32_t num_unconstrained_vars(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n, count;

  count = 0;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    if (arith_var_lower_index(vtbl, i) < 0 ||
	arith_var_upper_index(vtbl, i) < 0) {
      count ++;
    }
  }

  return count;
}

static bool underconstrained(simplex_solver_t *solver) {
  uint32_t n, p;

  p = num_unconstrained_vars(solver);
  n = solver->vtbl.nvars;
  if (n > 20) {
    return p >= n - (n/20);
  } else {
    return p >= n - 1;
  }
}


/*
 * Check whether the basic variable in row r is an integer variable
 */
static inline bool row_has_integer_basic_var(matrix_t *matrix, arith_vartable_t *vtbl, int32_t r) {
  thvar_t x;

  assert(0 <= r && r < matrix->nrows);
  x = matrix_basic_var(matrix, r);
  assert(x >= 0);
  return arith_var_is_int(vtbl, x);
}

#ifndef NDEBUG
/*
 * For debugging: go through the column of variable x
 * check that all elements a_i.x in this column are integer
 */
static bool column_is_integral(simplex_solver_t *solver, thvar_t x) {
  xrational_t prod;
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  column_t *col;
  uint32_t i, n;
  int32_t r, j;
  bool all_int;

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  assert(matrix_is_nonbasic_var(matrix, x));

  all_int = true;

  xq_init(&prod);
  col = matrix_column(matrix, x);
  if (col != NULL) {
    n = col->size;
    for (i=0; i<n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0 && row_has_integer_basic_var(matrix, vtbl, r)) {
	j = col->data[i].r_ptr;
	xq_set(&prod, arith_var_value(vtbl, x));
	xq_mul(&prod, matrix_coeff(matrix, r, j));
	// prod is val[x] * coeff of x in row r
	if (! xq_is_integer(&prod)) {
	  all_int = false;
	  break;
	}
      }
    }

  }

  xq_clear(&prod);

  return all_int;
}
#endif


/*
 * Compute a period for x
 * - the column of x contains coefficients { a_1, ...., a_n }.
 * - we want to ensure a_1 * x .... a_n * x are all integers
 * - so x must be a multiple of 1/a_1, ...., 1/a_n
 *
 * If x is an integer variable, this function computes the
 *  lcm of { 1, 1/a_1, ..., 1/a_n }
 * If x is not an integer variable, it computes the
 *  lcm of { 1/a_1, ..., 1/a_n }
 */
static void lcm_in_column(simplex_solver_t *solver, rational_t *lcm, thvar_t x) {
  rational_t inv_a;
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  column_t *col;
  uint32_t i, n;
  int32_t r, j;

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  assert(matrix_is_nonbasic_var(matrix, x));

  q_clear(lcm);
  if (arith_var_is_int(vtbl, x)) {
    q_set_one(lcm);
  }

  col = matrix_column(matrix, x);
  assert(col != NULL);

  q_init(&inv_a);

  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0 && row_has_integer_basic_var(matrix, vtbl, r)) {
      // x occurs in row r with coefficient a
      j = col->data[i].r_ptr;
      q_set(&inv_a, matrix_coeff(matrix, r, j));
      assert(q_is_nonzero(&inv_a));
      q_inv(&inv_a);
      if (q_is_zero(lcm)) {
	// lcm must be positive
	q_set_abs(lcm, &inv_a);
      } else {
	q_generalized_lcm(lcm, &inv_a);
      }
    }
  }

  q_clear(&inv_a);
}


/*
 * Compute a safe delta interval for x
 * - the interval stores: a lower bound L, an upper bound U
 * - this defines a set of deltas for x: { d | L <= d && d <= U }
 * - for any delta in this interval, updating
 *      val[x] to val[x] + delta
 *   maintains feasibility.
 */
static void safe_adjust_interval(simplex_solver_t *solver, interval_t *s, thvar_t x) {
  xrational_t aux;
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  column_t *col;
  rational_t *a;
  uint32_t i, n;
  int32_t r, j;
  thvar_t y;

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  xq_init(&aux);

  assert(matrix_is_nonbasic_var(matrix, x));

  /*
   * Initialize the interval:
   * - period = not used
   * - lower bound on delta = lower bound on x - value of x
   * - upper bound on delta = upper bound on x - value of x
   */
  j = arith_var_lower_index(vtbl, x);
  if (j >= 0) {
    xq_set(&aux, &solver->bstack.bound[j]); // lower bound on x
    xq_sub(&aux, arith_var_value(vtbl, x));
    interval_update_lb(s, &aux);
  }
  j = arith_var_upper_index(vtbl, x);
  if (j >= 0) {
    xq_set(&aux, &solver->bstack.bound[j]); // upper bound on x
    xq_sub(&aux, arith_var_value(vtbl, x));
    interval_update_ub(s, &aux);
  }

  assert(! empty_interval(s));

  // refine the bounds based on x's column
  col = matrix_column(matrix, x);
  assert(col != NULL);
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0) {
      j = col->data[i].r_ptr;
      a = matrix_coeff(matrix, r, j);
      y = matrix_basic_var(matrix, r);
      assert(y >= 0 && q_is_nonzero(a));

      /*
       * Update the interval using the bounds on y,
       *
       * We have y + ... + a x + ... = 0, so moving val[x]
       * to val[x] + delta changes val[y] to val[y] - a * delta.
       */
      j = arith_var_lower_index(vtbl, y);
      if (j >= 0) {
	/*
	 * L := lower bound on y:
	 * if a > 0, we want delta <= (val[y] - L)/a
	 * if a < 0, we want delta >= (val[y] - L)/a
	 */
	xq_set(&aux, arith_var_value(vtbl, y));
	xq_sub(&aux, &solver->bstack.bound[j]);
	xq_div(&aux, a);   // aux is (val[y] - L)/a
	if (q_is_pos(a)) {
	  interval_update_ub(s, &aux);
	} else {
	  interval_update_lb(s, &aux);
	}
      }

      j = arith_var_upper_index(vtbl, y);
      if (j >= 0) {
	/*
	 * U := upper bound on y:
	 * if a > 0, we want delta >= (val[y] - U)/a
	 * if a < 0, we want delta <= (val[y] - U)/a
	 */
	xq_set(&aux, arith_var_value(vtbl, y));
	xq_sub(&aux, &solver->bstack.bound[j]);
	xq_div(&aux, a);  // aux is (val[y] - U)/a
	if (q_is_pos(a)) {
	  interval_update_lb(s, &aux);
	} else {
	  interval_update_ub(s, &aux);
	}
      }

      assert(! empty_interval(s));
    }
  }

  xq_clear(&aux);
}


#if 0
/*
 * For testing: display data about column x
 */
static void show_column_data(simplex_solver_t *solver, thvar_t x) {
  interval_t interval;
  xrational_t newval;
  arith_vartable_t *vtbl;
  bool x_is_int;

  vtbl = &solver->vtbl;
  x_is_int = arith_var_is_int(vtbl, x);

  init_interval(&interval);
  xq_init(&newval);

  // Get period
  lcm_in_column(solver, &interval.period, x);
  if (q_is_zero(&interval.period)) {
    /*
     * x is a non-integer variable
     * and no integer basic variable depend on x
     * no need to touch x.
     */
    assert(!x_is_int);
    assert(column_is_integral(solver, x));
    goto done;
  }

  // Get bounds
  safe_adjust_interval(solver, &interval, x);
  if (interval.has_lb) {
    xq_add(&interval.lb, arith_var_value(vtbl, x));
    if (x_is_int) {
      xq_ceil(&interval.lb);
    }
  }
  if (interval.has_ub) {
    xq_add(&interval.ub, arith_var_value(vtbl, x));
    if (x_is_int) {
      xq_floor(&interval.ub);
    }
  }

#if 0
  printf("---> column of var = i!%"PRId32"\n", x);
  if (interval.has_lb) {
    printf("     lower bound: ");
    xq_print(stdout, &interval.lb);
    printf("\n");
  } else {
    printf("     no lower bound\n");
  }
  if (interval.has_ub) {
    printf("     upper bound: ");
    xq_print(stdout, &interval.ub);
    printf("\n");
  } else {
    printf("     no upper bound\n");
  }
  printf("     period: ");
  q_print(stdout, &interval.period);
  printf("\n");
  fflush(stdout);
#endif

  if (empty_interval(&interval)) {
    // no multiple of period between the two bounds
#if 0
    printf("     empty interval: can't fix\n");
    fflush(stdout);
#endif
    goto done;
  }


  xq_set(&newval, arith_var_value(vtbl, x));
  xq_div(&newval, &interval.period);
  xq_floor(&newval);
  xq_mul(&newval, &interval.period);

  assert(xq_le(&newval, arith_var_value(vtbl, x)));

  /*
   * newval is a multiple of period and we have
   *   newval <= val[x] < newval + period
   */
  if (xq_eq(&newval, arith_var_value(vtbl, x))) {
    // no change needed
    assert(column_is_integral(solver, x));
#if 0
    printf("     column already integral\n");
    fflush(stdout);
#endif
  }

 done:
  delete_interval(&interval);
  xq_clear(&newval);
}

#endif

/*
 * Try to adjust the value of non-basic variable x to make x's column integral,
 * while preserving all the bounds
 * - x must be a non-basic, integer variable
 * - x must have an integer value in the assignment
 * - returns false if that's not possible
 * - returns true and update the variable assignment otherwise
 */
static bool make_column_integral(simplex_solver_t *solver, thvar_t x) {
  interval_t interval;
  xrational_t newval;
  arith_vartable_t *vtbl;
  bool x_is_int, ok;

  vtbl = &solver->vtbl;
  x_is_int = arith_var_is_int(vtbl, x);
  ok = false;

  init_interval(&interval);
  xq_init(&newval);

  // Get period
  lcm_in_column(solver, &interval.period, x);
  if (q_is_zero(&interval.period)) {
    /*
     * x is a non-integer variable
     * and no integer basic variable depend on x
     * no need to touch x.
     */
    assert(!x_is_int);
    assert(column_is_integral(solver, x));

    ok = true;
    goto done;
  }

  // Get bounds
  safe_adjust_interval(solver, &interval, x);
  if (interval.has_lb) {
    xq_add(&interval.lb, arith_var_value(vtbl, x));
    if (x_is_int) {
      xq_ceil(&interval.lb);
    }
  }
  if (interval.has_ub) {
    xq_add(&interval.ub, arith_var_value(vtbl, x));
    if (x_is_int) {
      xq_floor(&interval.ub);
    }
  }

#if 0
  printf("---> make column integral: var = i!%"PRId32"\n", x);
  if (interval.has_lb) {
    printf("     lower bound: ");
    xq_print(stdout, &interval.lb);
    printf("\n");
  } else {
    printf("     no lower bound\n");
  }
  if (interval.has_ub) {
    printf("     upper bound: ");
    xq_print(stdout, &interval.ub);
    printf("\n");
  } else {
    printf("     no upper bound\n");
  }
  printf("     period: ");
  q_print(stdout, &interval.period);
  printf("\n");
  fflush(stdout);
#endif

  if (empty_interval(&interval)) {
    // no multiple of period between the two bounds
#if 0
    printf("     empty interval: can't fix\n");
    fflush(stdout);
#endif

    goto done;
  }


  xq_set(&newval, arith_var_value(vtbl, x));
  xq_div(&newval, &interval.period);
  xq_floor(&newval);
  xq_mul(&newval, &interval.period);

  assert(xq_le(&newval, arith_var_value(vtbl, x)));

  /*
   * newval is a multiple of period and we have
   *   newval <= val[x] < newval + period
   */
  if (xq_eq(&newval, arith_var_value(vtbl, x))) {
    // no change needed
    assert(column_is_integral(solver, x));

#if 0
    printf("     column already integral\n");
    fflush(stdout);
#endif

    ok = true;
    goto done;
  }

  // check whether newval works
  if (!interval.has_lb || xq_le(&interval.lb, &newval)) {
    // we can update x to newval
    update_non_basic_var_value(solver, x, &newval);
    simplex_set_bound_flags(solver, x);

    assert(column_is_integral(solver, x));
    assert(int_heap_is_empty(&solver->infeasible_vars));
    assert(value_satisfies_bounds(solver, x));

#if 0
    printf("     update value to ");
    xq_print(stdout, &newval);
    printf("\n");
    fflush(stdout);
#endif

    ok = true;
    goto done;
  }

  // check whether newval + period works
  xq_add_q(&newval, &interval.period);
  if (!interval.has_ub || xq_ge(&interval.ub, &newval)) {
    update_non_basic_var_value(solver, x, &newval);
    simplex_set_bound_flags(solver, x);

    assert(column_is_integral(solver, x));
    assert(int_heap_is_empty(&solver->infeasible_vars));
    assert(value_satisfies_bounds(solver, x));

#if 0
    printf("     update value to ");
    xq_print(stdout, &newval);
    printf("\n");
    fflush(stdout);
#endif

    ok = true;
    goto done;
  }

#if 0
  printf("     can't fix\n");
  fflush(stdout);
#endif

 done:
  delete_interval(&interval);
  xq_clear(&newval);

  return ok;
}


/*
 * Naive search
 */
static bool simplex_try_naive_integer_search(simplex_solver_t *solver) {
  ivector_t aux;
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  uint32_t i, j, n;
  thvar_t x;
  bool ok;

#if 0
  printf("\nNAIVE INTEGER SEARCH %"PRIu32" [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	 solver->stats.num_make_intfeasible, solver->core->decision_level, solver->core->stats.decisions);
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  init_ivector(&aux, 20);

  n = vtbl->nvars;
  ok = true;

  i = n;
  while (i > 0) {
    i --;
    if (matrix_is_nonbasic_var(matrix, i) && matrix_column(matrix, i) != NULL) {
      if (! make_column_integral(solver, i)) {
	ivector_push(&aux, i);
      }
    }
  }

  while (aux.size > 0 && ok) {
    j = 0;
    n = aux.size;
    for (i=0; i<n; i++) {
      x = aux.data[i];
      if (!make_column_integral(solver, x)) {
	aux.data[j] = x;
	j ++;
      }
    }
    ivector_shrink(&aux, j);
    ok = (j < n);
  }

  delete_ivector(&aux);

#if DEBUG
  check_assignment(solver);
  check_vartags(solver);
#endif

  assert(!ok || simplex_assignment_integer_valid(solver));

#if 0
  if (ok) {
    printf("\nNAIVE INTEGER SEARCH WORKED\n\n");
    print_simplex_matrix(stdout, solver);
    print_simplex_bounds(stdout, solver);
    printf("\n");
    print_simplex_assignment(stdout, solver);
    printf("\n\n");
    fflush(stdout);
  }
#endif

  return ok;
}



/*
 * BRANCHING
 */

#if TRACE_INTFEAS
static void print_branch_candidates(FILE *f, simplex_solver_t *solver, ivector_t *v) {
  uint32_t i, n;

  n = v->size;
  for (i=0; i<n; i++) {
    print_simplex_var_bounds(f, solver, v->data[i]);
  }
  fprintf(f, "\n");
  fflush(f);
}

#endif


/*
 * Collect all basic, integer variables that don't have an integer value
 * in the current assignment
 * - the result is stored in vector v (added to v)
 */
static void collect_non_integer_basic_vars(simplex_solver_t *solver, ivector_t *v) {
  arith_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(vtbl, i) &&
	matrix_is_basic_var(&solver->matrix, i) &&
        ! arith_var_value_is_int(vtbl, i)) {
      ivector_push(v, i);
    }
  }
}


/*
 * Create branch & bound atom for a variable x.
 * - if x has a lower and an upper bound: l <= x <= u,
 *   we use the midpoint. The branch atom is (x >= ceil((l+u)/2)).
 * - otherwise, we use (x >= ceil(value[x])).
 */
static void create_branch_atom(simplex_solver_t *solver, thvar_t x) {
  xrational_t *bound;
  int32_t new_idx, lb, ub;
  literal_t l;

  assert(arith_var_is_int(&solver->vtbl, x) & ! arith_var_value_is_int(&solver->vtbl, x));

  bound = &solver->bound;
  lb = arith_var_lower_index(&solver->vtbl, x);
  ub = arith_var_upper_index(&solver->vtbl, x);
  if (lb >= 0 && ub >= 0) {
    xq_set(bound, solver->bstack.bound + lb);
    xq_add(bound, solver->bstack.bound + ub);
    q_set32(&solver->aux, 2);
    xq_div(bound, &solver->aux);
  } else {
    xq_set(bound, arith_var_value(&solver->vtbl, x));
  }
  xq_ceil(bound);
  assert(xq_is_integer(bound));

#if 0
  printf("\n---> Branch & bound\n\n");
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
#endif

  l = get_literal_for_ge_atom(&solver->atbl, x, true, &bound->main, &new_idx);
  solver->last_branch_atom = var_of(l);

  /*
   * If support periodic calls to make_integer_feasible is enabled,
   * then the branch atom may not be new.
   */
  // assert(new_idx >= 0);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, x, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, x, new_idx);

#if TRACE_BB || TRACE_INTFEAS
    printf("---> Branch & bound: create ");
    print_simplex_atomdef(stdout, solver, var_of(l));
#endif

    solver->stats.num_branch_atoms ++;
  }
}


/*
 * Heuristic for selecting branching variable
 * - try to select the most constrained variable
 * - the score for x is (upper bound - lower bound) if that's small enough
 * - return MAX_BRANCH_SCORE if x has zero or one bounds
 */
#define MAX_BRANCH_SCORE UINT32_MAX
#define HALF_MAX_BRANCH_SCORE (UINT32_MAX/2)

#if 0

/*
 * Simple version: use current bounds on x
 */
static uint32_t simplex_branch_score(simplex_solver_t *solver, thvar_t x) {
  rational_t *diff;
  int32_t l, u;
  uint32_t s;

  diff = &solver->aux;
  l = arith_var_lower_index(&solver->vtbl, x);
  u = arith_var_upper_index(&solver->vtbl, x);
  if (l < 0 && u < 0) {
    return MAX_BRANCH_SCORE;
  } else if (l < 0 || u < 0) {
    return HALF_MAX_BRANCH_SCORE + 1;
  }
  q_set(diff, &solver->bstack.bound[u].main);
  q_sub(diff, &solver->bstack.bound[l].main);
  q_normalize(diff);
  // diff = upper bound - lower bound
  if (q_is_smallint(diff)) {
    s = q_get_smallint(diff);
    if (s < HALF_MAX_BRANCH_SCORE) {
      return s;
    }
  }

  return HALF_MAX_BRANCH_SCORE;
}

#else

/*
 * New version: try to learn new bounds on x first (by bound strengthening)
 */

/*
 * Check whether x has an upper bound
 * - if so, add the bound to diff
 * - x must be an integer basic variable..
 */
static bool simplex_branch_var_add_ub(simplex_solver_t *solver, thvar_t x, rational_t *diff) {
  xrational_t *bound;
  xrational_t *ub;
  bool derived, has_ub;
  int32_t u;

  assert(arith_var_is_int(&solver->vtbl, x) && matrix_is_basic_var(&solver->matrix, x));

  ub = NULL; // Some versions of GCC give a warning otherwise

  bound = &solver->bound;

  derived = simplex_basic_var_has_derived_bound(solver, x, false);
  if (derived) {
    simplex_get_derived_bound_on_basic_var(solver, x, false, bound);
    xq_floor(bound); // since x is an integer
  }

  u = arith_var_upper_index(&solver->vtbl, x);
  if (u >= 0) {
    ub = solver->bstack.bound + u; // upper bound on x in the bound stack
  }

  has_ub = false;
  if (derived && (u < 0 || q_lt(&bound->main, &ub->main))) {
    q_add(diff, &bound->main);
    has_ub = true;
  } else if (u >= 0) {
    q_add(diff, &ub->main);
    has_ub = true;
  }

  return has_ub;
}

/*
 * Check whether x has a lower bound
 * - if so, subtract the bound from diff
 * - x must be an integer basic variable..
 */
static bool simplex_branch_var_sub_lb(simplex_solver_t *solver, thvar_t x, rational_t *diff) {
  xrational_t *bound;
  xrational_t *lb;
  bool derived, has_lb;
  int32_t l;

  assert(arith_var_is_int(&solver->vtbl, x) && matrix_is_basic_var(&solver->matrix, x));

  lb = NULL; // Some versions of GCC give a warning otherwise

  bound = &solver->bound;

  derived = simplex_basic_var_has_derived_bound(solver, x, true);
  if (derived) {
    simplex_get_derived_bound_on_basic_var(solver, x, true, bound);
    xq_ceil(bound); // since x is an integer
  }

  l = arith_var_lower_index(&solver->vtbl, x);
  if (l >= 0) {
    lb = solver->bstack.bound + l; // lower bound on x in the bound stack
  }

  has_lb = false;
  if (derived && (l < 0 || q_gt(&bound->main, &lb->main))) {
    q_sub(diff, &bound->main);
    has_lb = true;
  } else if (l >= 0) {
    q_sub(diff, &lb->main);
    has_lb = true;
  }

  return has_lb;
}


// new version: use derived bounds on x if available
static uint32_t simplex_branch_score(simplex_solver_t *solver, thvar_t x) {
  rational_t *diff;
  bool has_lb, has_ub;
  uint32_t s;

  diff = &solver->aux;
  q_clear(diff);
  has_ub = simplex_branch_var_add_ub(solver, x, diff);
  assert(q_is_integer(diff));
  has_lb = simplex_branch_var_sub_lb(solver, x, diff);
  assert(q_is_integer(diff));

  if (has_ub && has_lb) {
    q_normalize(diff);
    /*
     * The derived bounds could be in conflict (because we don't do
     * exhaustive bound strengthening in strengthen bounds). In
     * such a case, we have diff < 0. We give x a score of 0.
     */
    if (q_is_neg(diff)) {
      s = 0;
    } else if (q_is_smallint(diff)) {
      s = q_get_smallint(diff);
      if (s > HALF_MAX_BRANCH_SCORE) {
	s = HALF_MAX_BRANCH_SCORE;
      }
    } else {
      s = HALF_MAX_BRANCH_SCORE;
    }
  } else if (has_ub || has_lb) {
    // at least one bound
    s = HALF_MAX_BRANCH_SCORE + 1;
  } else {
    // no bounds
    s = MAX_BRANCH_SCORE;
  }

  return s;
}

#endif


/*
 * Select a branch variable of v: pick the one with smallest score.
 * Break ties randomly.
 * - return the selected variable
 * - score its score in *var_score
 */
static thvar_t select_branch_variable(simplex_solver_t *solver, ivector_t *v, uint32_t *var_score) {
  uint32_t i, n, best_score, score, k;
  thvar_t x, best_var;

#if TRACE_INTFEAS
  printf("\nSELECT BRANCH VARIABLE\n\n");
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif


  n = v->size;
  assert(n > 0);

  best_var = v->data[0];
  best_score = simplex_branch_score(solver, best_var);
  k = 1;

  for (i=1; i<n; i++) {
    x = v->data[i];
    score = simplex_branch_score(solver, x);
    if (score < best_score) {
      best_score = score;
      best_var = x;
      k = 1;
    } else if (score == best_score) {
      // break ties randomly
      k ++;
      if (random_uint(solver, k) == 0) {
        best_var = x;
      }
    }
  }

  *var_score = best_score;
  return best_var;
}





/*
 * EXPLANATIONS FOR INTEGER UNSATISFIABILITY
 */

/*
 * Prepare to explain why variable x is fixed
 * - add the constraint indices for x's lower and upper bound to vector q
 */
static void explain_fixed_variable(simplex_solver_t *solver, thvar_t x, ivector_t *q) {
  int32_t k;

  assert(simplex_fixed_variable(solver, x));

  k = arith_var_lower_index(&solver->vtbl, x);
  assert(k >= 0);
  enqueue_cnstr_index(q, k, &solver->bstack);

  k = arith_var_upper_index(&solver->vtbl, x);
  assert(k >= 0);
  enqueue_cnstr_index(q, k, &solver->bstack);
}


/*
 * Explain all fixed variables of a row
 * - for each fixed var x, the lower index and upper index are pushed into q
 *   (unless they are in q already)
 */
static void explain_fixed_variables_of_row(simplex_solver_t *solver, row_t *row, ivector_t *q) {
  uint32_t i, n;
  thvar_t x;

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0 && simplex_fixed_variable(solver, x)) {
      explain_fixed_variable(solver, x, q);
    }
  }
}


/*
 * Collect all the fixed variables that occur in a row of v
 * - for each fixed variable x, its lower and upper index are pushed into q
 */
static void explain_fixed_variables_of_row_vector(simplex_solver_t *solver, ivector_t *v, ivector_t *q) {
  matrix_t *matrix;
  uint32_t i, n;
  int32_t r;

  assert(v != q);
  matrix = &solver->matrix;
  n = v->size;
  for (i=0; i<n; i++) {
    r = v->data[i];
    explain_fixed_variables_of_row(solver, matrix->row[r], q);
  }
}



/*
 * Generate a conflict when the GCD test fails for a row
 * - the explanation is stored in expl_vector
 * - it's a set of literals that explain the fixed variables in the row
 */
static void build_gcd_conflict(simplex_solver_t *solver, row_t *row) {
  ivector_t *v;

  // Collect bound indices in solver->expl_queue
  v = &solver->expl_queue;
  assert(v->size == 0);
  explain_fixed_variables_of_row(solver, row, v);

  // Build the explanation into solver->expl_vector
  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_build_explanation(solver, v);

  // turn v into a clause and add null-literal as terminator
  convert_expl_to_clause(v);
  ivector_push(v, null_literal);

  // record v as a conflict
  record_theory_conflict(solver->core, v->data);

  solver->stats.num_dioph_gcd_conflicts ++;
}



/*
 * Build a conflict from an integer-infeasible set of rows
 * (returned by the diophantine solver)
 * - v = vector of row indices
 * - the conflict is a set of literals that explain the constant
 *   in each of v (i.e., the fixed variables).
 */
static void build_dsolver_conflict(simplex_solver_t *solver, ivector_t *v) {
  ivector_t *w;

  // Collect bound indices in solver->expl_queue
  w = &solver->expl_queue;
  assert(w->size == 0 && v != w);
  explain_fixed_variables_of_row_vector(solver, v, w);

  // Build the explanation into solver->expl_vector
  w = &solver->expl_vector;
  ivector_reset(w);
  simplex_build_explanation(solver, w);

  // turn expl into a clause then record the conflict
  convert_expl_to_clause(w);
  ivector_push(w, null_literal);

  record_theory_conflict(solver->core, w->data);

  solver->stats.num_dioph_conflicts ++;
}




/*
 * BOUND STRENGTHENING
 */

#ifndef NDEBUG

/*
 * Check whether k is an element of q
 */
static bool in_vector(ivector_t *q, int32_t k) {
  uint32_t i, n;

  n = q->size;
  for (i=0; i<n; i++) {
    if (q->data[i] == k) return true;
  }

  return false;
}

static bool not_in_vector(ivector_t *q, int32_t k) {
  return ! in_vector(q, k);
}

#endif

/*
 * Clear the mark on all elements of q
 */
static void clear_antecedent_marks(simplex_solver_t *solver, ivector_t *q) {
  arith_bstack_t *bstack;
  uint32_t i, n;
  int32_t k;

  bstack = &solver->bstack;
  n = q->size;
  for (i=0; i<n; i++) {
    k = q->data[i];
    arith_cnstr_clr_mark(bstack, k);
  }
}

/*
 * Collect a set of bound indices that explain the general solution for
 * variable x.
 * - the diophantine solver returns a set of row indices as explanation for x
 * - this function converts the set of rows to a set of bound indices (i.e.,
 *   the lower/upper bound constraints on all the fixed variables in the
 *   set of rows
 * - the set of indices is added to vector q
 */
static void build_integer_solution_antecedent(simplex_solver_t *solver, thvar_t x, ivector_t *q) {
  dsolver_t *dioph;
  ivector_t *v;

  v = &solver->aux_vector;
  dioph = solver->dsolver;
  assert(v->size == 0 && v != q && dioph != NULL);

  // get the set of rows from the diophantine solver
  dsolver_explain_solution(dioph, x, v);

  // collect the fixed variables of v into q
  explain_fixed_variables_of_row_vector(solver, v, q);

  ivector_reset(v);

  /*
   * HACK: the bstack marks are used to avoid adding the same
   * bound index twice to q. They must be cleared here to avoid
   * interference with conflict explanation if a conflict occurs.
   */
  clear_antecedent_marks(solver, q);
}




/*
 * Attempt to strengthen the lower or upper bound on x
 * using the general solution for x found by the diophantine solver
 * - p must be the solution found for x
 * - dioph must be non-null
 * - return true if the strengthened bounds do not cause a conflict
 * - return false otherwise
 * Set the recheck flag if make_feasible is required after this
 */
static bool strengthen_bounds_on_integer_variable(simplex_solver_t *solver, dsolver_t *dioph, thvar_t x, polynomial_t *p) {
  ivector_t *q;
  rational_t *gcd, *aux, *constant;
  xrational_t *bound;
  int32_t k;
  bool ok;

  gcd = &solver->gcd;
  aux = &solver->aux;
  constant = &solver->constant;
  bound = &solver->bound;

  q = NULL;
  ok = true;

  /*
   * compute the gcd of all non-constant coefficients of p
   * if gcd == 0, then p is a constant polynomial, which can happen only
   * if x is a fixed variable in solver.
   * if gcd == 1, we can't strengthen the bounds on x
   */
  monarray_gcd(p->mono, gcd);
  assert(q_is_nonneg(gcd));

  if (q_cmp_int32(gcd, 1, 1) > 0) {
    // get the constant of p
    monarray_constant(p->mono, constant);

    //try to strengthen the lower bound on x
    k = arith_var_lower_index(&solver->vtbl, x);
    if (k >= 0) {
      /*
       * Let b = constant of p and l = current lower bound on x
       * the strengthened bound is l' = b + d * ceil((l - b)/d)
       * Let r = remainder of (l-b) divided by d
       * if r = 0, then l' = l else l' = l + d - r (and l' > l)
       */
      assert(xq_is_integer(solver->bstack.bound + k));
      q_set(aux, &solver->bstack.bound[k].main);
      q_sub(aux, constant);

      q_integer_rem(aux, gcd);  // remainder of (l - b) divided by d
      if (q_is_pos(aux)) {

        // the bound can be strengthened
        xq_set(bound, solver->bstack.bound + k);
        q_add(&bound->main, gcd);
        q_sub(&bound->main, aux);
        assert(xq_is_integer(bound));


        // build the antecedent for x == p into aux_vector2
        q = &solver->aux_vector2; // WARNING: we can't use expl_queue here
        assert(q->size == 0);
        build_integer_solution_antecedent(solver, x, q);

        // add bound index k at the end of q
        assert(not_in_vector(q, k));
        ivector_push(q, k);

        // add the new bound as a derived bound with antecedent q
        ok = simplex_add_derived_lower_bound(solver, x, bound, q);

        ivector_pop(q); // remove k from q but keep the rest

        if (! ok) goto done;
      }
    }

    // try to strengthen the upper bound on x
    k = arith_var_upper_index(&solver->vtbl, x);
    if (k >= 0) {
      /*
       * The strengthened bound is u' = b + d * floor((u - b)/d)
       * Let r = remainder of (u - b) divided by d
       * If r = 0 then u' = u else u' = u - r
       */
      assert(xq_is_integer(solver->bstack.bound + k));
      q_set(aux, &solver->bstack.bound[k].main);
      q_sub(aux, constant);
      q_integer_rem(aux, gcd);   // remainder of (u - b) divided by d
      if (q_is_pos(aux)) {
        // the bound can be strengthened
        xq_set(bound, solver->bstack.bound + k);
        q_sub(&bound->main, aux);
        assert(xq_is_integer(bound));

        if (q == NULL) {
          // explain x == p: build antecedent in q
          q = &solver->aux_vector2; // can't use expl_queue or aux_vector
          assert(q->size == 0);
          build_integer_solution_antecedent(solver, x, q);
        }

        // add bound index k at the end of q
        assert(not_in_vector(q, k));
        ivector_push(q, k);

        // add the new bound with antecedent q
        ok = simplex_add_derived_upper_bound(solver, x, bound, q);

        ivector_pop(q); // remove k for cleanup
      }
    }
  }

 done:
  if (q != NULL) {
    ivector_reset(q);
  }

  return ok;
}



/*
 * Strengthen the bounds on all integer variables
 * - dsolver = diophantine solver where the general solution was computed
 * - return false if a conflict is detected (and record the conflict in the core)
 * - return true otherwise
 * - set solver->recheck to true if make_feasible is needed
 */
static bool strengthen_integer_bounds(simplex_solver_t *solver, dsolver_t *dioph) {
  polynomial_t *p;
  uint32_t i, n;

  assert(dioph->status == DSOLVER_SOLVED_SAT);

  n = dioph->nvars;
  for (i=1; i<n; i++) {  //skip 0 == const_idx
    p = dsolver_gen_sol(dioph, i);
    if (p != NULL) {
      if (! strengthen_bounds_on_integer_variable(solver, dioph, i, p)) {
        // conflict detected: exit
        solver->stats.num_dioph_bound_conflicts ++;
        return false;
      }
    }
  }

  return true;
}




/*
 * TEST INTEGER FEASIBILITY USING THE DIOPHANTINE SUBSOLVER
 */

/*
 * Check whether row contains only integer (or non-integer but fixed variables)
 */
static bool matrix_row_is_integral(simplex_solver_t *solver, row_t *row) {
  return find_real_var_in_row(solver, row) < 0;
}

/*
 * Add a row of the tableau to the subsolver
 * - r = the row index in tableau
 * - dioph = the subsolver
 * - all variables of row must be fixed or integer variables
 * - return true if the row is consistent, false otherwise
 */
static bool simplex_dsolver_add_row(simplex_solver_t *solver, dsolver_t *dioph, int32_t r, row_t *row) {
  uint32_t i, n;
  int32_t x;

  assert(matrix_row_is_integral(solver, row));

  (void) dsolver_row_open(dioph, r);

  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      if (simplex_fixed_variable(solver, x)) {
        dsolver_row_addmul_constant(dioph, &row->data[i].coeff, fixed_variable_value(solver, x));
      } else {
        dsolver_row_add_mono(dioph, &row->data[i].coeff, x);
      }
    }
  }
  return dsolver_row_close(dioph);
}




/*
 * Run the diophantine system solver on the current tableau
 * - return false if a conflict is found
 * - return true otherwise
 * - set solver->recheck to true if bound-strengthening requires a call to make_feasible
 *
 * Heuristics:
 * - dsolver_is_feasible can be very slow and expensive.
 * - we call it only if solver->enable_dfeas is true
 * - if dsolver_is_feasible is interrupted or gives up, we set enable_dfeas to false
 *   (so dsolver_is_feasible will be skipped on the next call).
 */
static bool simplex_dsolver_check(simplex_solver_t *solver) {
  dsolver_t *dioph;
  matrix_t *matrix;
  row_t *row;
  ivector_t *v;
  uint32_t i, n;
  bool pure_integer;

  dioph = simplex_get_dsolver(solver);
  reset_dsolver(dioph);

  pure_integer = ! simplex_is_mixed_system(solver);

  matrix = &solver->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (pure_integer || matrix_row_is_integral(solver, row)) {
      if (! simplex_dsolver_add_row(solver, dioph, i, row)) {
        // row i is not integer feasible (GCD test failed)
        build_gcd_conflict(solver, row);
        return false;
      }
    }
  }

  /*
   * Don't call dsolver_is_feasible if enable_dfeas is false.
   */
  if (! solver->enable_dfeas) return true;
  //  if (dioph->nvars > 2000) return true;

  solver->stats.num_dioph_checks ++;

  // run the diophantine solver
  dsolver_simplify(dioph);
  switch (dsolver_is_feasible(dioph)) {
  case DSOLVER_SOLVED_UNSAT:
    /*
     * get the set of unsat rows in aux_vector
     * then build a conflict for these rows
     */
    v = &solver->aux_vector;
    assert(v->size == 0);
    dsolver_unsat_rows(dioph, v);
    build_dsolver_conflict(solver, v);
    ivector_reset(v);

    return false;

  case DSOLVER_SOLVED_SAT:
    // Try to strengthen the bounds
    dsolver_build_general_solution(dioph);
    //  dsolver_print_gen_solution(stdout, dioph);
    //  fflush(stdout);
    return strengthen_integer_bounds(solver, dioph);

  case DSOLVER_INTERRUPTED:
  case DSOLVER_UNSOLVED:
    solver->enable_dfeas = false;
    return true;

  default:
    assert(false);
    return true;
  }
}


/*
 * CHEAPER INTEGRALITY CONSTRAINTS
 */

#if 0
/*
 * Print a list of variables
 */
static void show_vars(simplex_solver_t *solver, thvar_t *a, uint32_t n) {
  uint32_t i;
  thvar_t x;

  if (n == 0) {
    printf("[]");
  } else {
    x = a[0];
    printf("[");
    print_simplex_var(stdout, solver, x);
    for (i=1; i<n; i++) {
      x = a[i];
      printf(" ");
      print_simplex_var(stdout, solver, x);
    }
    printf("]");
  }
}

static void show_array_of_bound_ids(ivector_t *a) {
  uint32_t i, n;

  n = a->size;
  if (n == 0) {
    printf("[]");
  } else {
    printf("[%"PRId32, a->data[0]);
    for (i=1; i<n; i++) {
      printf(" %"PRId32, a->data[i]);
    }
    printf("]");
  }

}

#endif

/*
 * Conflict explanation when an integrality constraint is not feasible.
 * - the explanation is a list of fixed variables stored in array a
 * - n = number of elements of this array.
 */
static void build_integrality_conflict(simplex_solver_t *solver, thvar_t *a, uint32_t n) {
  ivector_t *v;
  uint32_t i;

  // Collect bound indices in solver->expl_queue
  v = &solver->expl_queue;
  assert(v->size == 0);

  for (i=0; i<n; i++) {
    explain_fixed_variable(solver, a[i], v);
  }

  // Build the explanation into solver->expl_vector
  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_build_explanation(solver, v);

  // turn v into a clause and add null-literal as terminator
  convert_expl_to_clause(v);
  ivector_push(v, null_literal);

  // record v as a conflict
  record_theory_conflict(solver->core, v->data);
}


/*
 * Build the antecedent for a bound derived from an integer constraint.
 * An integer constraint may imply a bound on x when we know that
 *  (x - T) is a multiple of Q.
 * The integrality constraint code computes the relevant Q and T for x.
 * The constraint "Q divides (x - T)" has an explanation given as
 * a set of fixed variables.
 *
 * This function collects the bound indices that explain why these
 * variables are fixed.
 *
 * Input:
 * - a = array of n fixed variables
 * - v = vector in which the bounds are added.
 */
static void collect_fixed_vars_antecedents(simplex_solver_t *solver, thvar_t *a, uint32_t n, ivector_t *v) {
  uint32_t i;
  thvar_t x;
  int32_t l, u;

  assert(a != v->data);

  for (i=0; i<n; i++) {
    x = a[i];
    assert(simplex_fixed_variable(solver, x));

    l = arith_var_lower_index(&solver->vtbl, x);
    u = arith_var_upper_index(&solver->vtbl, x);
    assert(l >= 0 && u >= 0);

    ivector_push(v, l);
    ivector_push(v, u);
  }
}


/*
 * Attempt to strengthen the bounds on x, when we know
 * x = period * n + phase for some integer n.
 * - v = explanation for this constraint (as an array of fixed variables)
 * - returns false if the new bound causes a conflict
 * - returns true otherwise (may also set the global flag solver->recheck to true)
 */
static bool simplex_integer_derived_bounds(simplex_solver_t *solver, thvar_t x,
					   rational_t *period, rational_t *phase, ivector_t *v) {
  ivector_t *antecedents;
  xrational_t *bound;
  rational_t *aux;
  int32_t k;
  bool ok, antecedents_ready;

  assert(q_is_pos(period));
  assert(arith_var_is_int(&solver->vtbl, x));

  antecedents = &solver->aux_vector;
  assert(antecedents->size == 0 && antecedents != v);
  antecedents_ready = false;

  bound = &solver->bound;
  aux = &solver->aux;
  ok = true;

  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0) {
    /*
     * Let L = current lower bound on x, P = period, and B = phase.
     * We have:
     *  1) x >= L
     *  2) there's an integer k such that (x = B + P k).
     * This implies
     *    (B + P k >= L) so k >= (L - B)/P and then k >= ceil((L - B)/P)
     * This gives the derived bound
     *   x >= B + P * ceil((L - B)/P).
     *
     * If (L - B)/P is not an integer, then B + P * ceil((L - B)/P) > L,
     * so the derived bound is stronger than L.
     *
     */
    assert(xq_is_integer(solver->bstack.bound + k)); // because x is an integer
    q_set(aux, &solver->bstack.bound[k].main);  // L
    q_sub(aux, phase);
    q_div(aux, period);  // aux is (L - B)/P
    q_normalize(aux);
    if (! q_is_integer(aux)) {
      /*
       * strengthen the lower bound on x
       */
      q_ceil(aux);
      q_mul(aux, period);
      q_add(aux, phase);   // aux is B + P * ceil((L - B)/P)
      q_normalize(aux);
      assert(q_gt(aux, &solver->bstack.bound[k].main));

#if 0
      printf("---> Strengthening lower bound on ");
      print_simplex_var(stdout, solver, x);
      printf("\n");
      printf("  current value: ");
      print_simplex_var_value(stdout, solver, x);
      printf("\n");
      printf("  current bounds: ");
      print_simplex_var_bounds(stdout, solver, x);
      printf("  period: ");
      q_print(stdout, period);
      printf("\n");
      printf("  phase: ");
      q_print(stdout, phase);
      printf("\n");
      printf("  derived lower bound: ");
      q_print(stdout, aux);
      printf("\n");
#endif
      /*
       * Antecedents for the new bound:
       * - we have (x >= Current bound) AND (x = B + P * some integer) => (x >= New bound)
       * - and fixed vars => (x = B + P * some integer)
       * So the antecendents for the new bounds are
       * - the antecedents for the fixed vars + the current bound
       */
      collect_fixed_vars_antecedents(solver, v->data, v->size, antecedents);
      antecedents_ready = true;
      ivector_push(antecedents, k); // index for (x >= current bound)
      xq_set_q(bound, aux);
      ok = simplex_add_derived_lower_bound(solver, x, bound, antecedents);

#if 0
      printf("  new bounds: ");
      print_simplex_var_bounds(stdout, solver, x);
      printf("  antecedents: ");
      show_array_of_bound_ids(antecedents);
      printf("\n\n");
      fflush(stdout);

#endif
      /*
       * cleanup the antecedents vector: we want to remove the index k
       * since the vector may be used again if we can strengthen the
       * upper bound on x
       */
      ivector_pop(antecedents);
      if (! ok) goto done;

    }
  }

  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0) {
    /*
     * Let U = current upper bound x. We have
     *  1) x <= U
     *  2) x = B + P k
     * So  k <= floor((U - B)/P).
     *
     * The derived bound is then x <= B + P * floor((U - B)/P).
     * If that's less than U, we add it as upper bound on x.
     */
    assert(xq_is_integer(solver->bstack.bound + k));
    q_set(aux, &solver->bstack.bound[k].main); // U
    q_sub(aux, phase);
    q_div(aux, period); // aux is (U - B)/P
    q_normalize(aux);
    if (!q_is_integer(aux)) {
      /*
       * Derived bound smaller than U
       */
      q_floor(aux);
      q_mul(aux, period);
      q_add(aux, phase);
      q_normalize(aux);
      assert(q_lt(aux, &solver->bstack.bound[k].main));

#if 0
      printf("---> Strengthening upper bound on ");
      print_simplex_var(stdout, solver, x);
      printf("\n");
      printf("  current value: ");
      print_simplex_var_value(stdout, solver, x);
      printf("\n");
      printf("  current_bounds: ");
      print_simplex_var_bounds(stdout, solver, x);
      printf("  period: ");
      q_print(stdout, period);
      printf("\n");
      printf("  phase: ");
      q_print(stdout, phase);
      printf("\n");
      printf("  derived upper bound: ");
      q_print(stdout, aux);
      printf("\n");
#endif

      /*
       * As above: antecedents for the derived bounds = current bound +
       * antecedents for the fixed variables.
       */
      if (!antecedents_ready) {
	collect_fixed_vars_antecedents(solver, v->data, v->size, antecedents);
      }
      ivector_push(antecedents, k);

      xq_set_q(bound, aux);
      ok = simplex_add_derived_upper_bound(solver, x, bound, antecedents);

#if 0
      printf("  new bounds: ");
      print_simplex_var_bounds(stdout, solver, x);
      printf("  antecedents: ");
      show_array_of_bound_ids(antecedents);
      printf("\n\n");
      fflush(stdout);

#endif
    }
  }

 done:
  // Must always clean up the aux_vector
  ivector_reset(antecedents);

#if 0
  if (!ok) {
    printf("---> Bound conflict\n\n");
    fflush(stdout);
  }
#endif

  return ok;
}



#ifndef NDEBUG
/*
 * Some checks on period/phase computations for variable k
 */

/*
 * Sum of all fixed terms
 */
static void sum_of_fixed_terms(int_constraint_t *cnstr, rational_t *sum) {
  uint32_t i, n;

  q_clear(sum);
  n = cnstr->fixed_nterms;
  for (i=0; i<n; i++) {
    q_addmul(sum, cnstr->fixed_val + i, &cnstr->fixed_sum[i].coeff);
  }
}

/*
 * Get a value of of variable k that satisfies the constraints.
 * - the constraint is (a * var[k] + other vars + fixed sum) is an integer
 * - so a possible solution is to set all other vars to zero
 * - and var[k] is (z - fixed_sum)/a
 */
static void get_solution_for_var(int_constraint_t *cnstr, uint32_t k, rational_t *val, int32_t z) {
  rational_t qz;

  assert(k < cnstr->sum_nterms);

  q_init(&qz);

  q_set32(&qz, z);
  sum_of_fixed_terms(cnstr, val);
  q_neg(val);
  q_add(val, &qz);
  q_div(val, &cnstr->sum[k].coeff);

  q_clear(&qz);
}


/*
 * Check whether cnstr => var[k] = period * integer + phase holds
 */
static bool plausible_period_and_phase(int_constraint_t *cnstr, uint32_t k, rational_t *period, rational_t *phase) {
  rational_t test_val;
  int32_t z;

  q_init(&test_val);

  for (z = -20; z <= 20; z++) {
    get_solution_for_var(cnstr, k, &test_val, z);
    q_sub(&test_val, phase);  // value - phase
    if (! q_divides(period, &test_val)) {

#if 0
      printf("--- plausible_period_and_phase failed ---\n");
      printf("period = ");
      q_print(stdout, period);
      printf("\n");
      printf("phase = ");
      q_print(stdout, phase);
      printf("\n");
      printf("test z = %"PRId32"\n", z);
      printf("test_val = ");
      q_print(stdout, &test_val);
      printf("\n\n");
      fflush(stdout);

      assert(false);
#endif

      return false;
    }
  }

  q_clear(&test_val);

  return true;
}

#endif


/*
 * Process a constraint stored in checker
 * - first check feasibility
 * - it this succeeds, try bound strengthening on all integer variables
 *   in checker that are not fixed.
 */
static bool process_integrality_constraint(simplex_solver_t *solver, int_constraint_t *checker) {
  ivector_t v;
  rational_t *p, *q;
  uint32_t i, n;
  thvar_t x;
  bool feasible;

#if 0
  printf("==== Integrality constraint ====\n");
  print_int_constraint(stdout, solver, checker);
  fflush(stdout);

  init_ivector(&v, 10);
  feasible = int_constraint_is_feasible(checker, &v);
  if (feasible) {
    printf("Feasible\n");
  } else {
    printf("Not feasible\n");
    printf("Conflict vars: ");
    show_vars(solver, v.data, v.size);
    printf("\n");
    fflush(stdout);
  }

  if (feasible) {
    n = int_constraint_num_terms(checker);
    for (i=0; i<n; i++) {
      ivector_reset(&v);
      int_constraint_period_of_var(checker, i, &v);
      x = int_constraint_get_var(checker, i);
      p = int_constraint_period(checker);
      q = int_constraint_phase(checker);
      printf("Variable ");
      print_simplex_var(stdout, solver, x);
      printf(": period = ");
      q_print(stdout, p);
      printf(", phase = ");
      q_print(stdout, q);
      printf("\n");
      printf("  antecedents: ");
      show_vars(solver, v.data, v.size);
      printf("\n");
    }
  }

  delete_ivector(&v);

  printf("=====\n\n");
  fflush(stdout);
#endif

  init_ivector(&v, 10);
  feasible = int_constraint_is_feasible(checker, &v);
  if (!feasible) {
    build_integrality_conflict(solver, v.data, v.size);
    trace_printf(solver->core->trace, 10, "(unsat by integrality test)\n");
    solver->stats.num_itest_conflicts ++;

  } else {

    // Try bound strengthening
    n = int_constraint_num_terms(checker);
    for (i=0; i<n; i++) {
      x = int_constraint_get_var(checker, i);
      // if x is free, there's no bound to improve
      if (! simplex_free_variable(solver, x)) {
	ivector_reset(&v);
	int_constraint_period_of_var(checker, i, &v);
	p = int_constraint_period(checker);
	q = int_constraint_phase(checker);
	assert(plausible_period_and_phase(checker, i, p, q));

	feasible = simplex_integer_derived_bounds(solver, x, p, q, &v);
	if (!feasible) {
	  solver->stats.num_itest_bound_conflicts ++;
	  trace_printf(solver->core->trace, 10, "(unsat by integer bound strengthening)\n");
	  goto done;
	}
      }
    }

  }

 done:
  delete_ivector(&v);

  return feasible;
}


/*
 * Go through a row and extract an integrality constraint from it.
 * - all variables in the row must be integer or fixed
 */
static bool test_integrality_in_row(simplex_solver_t *solver, int_constraint_t *checker, row_t *row) {
  arith_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;
  rational_t *q;

  vtbl = &solver->vtbl;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      q = &row->data[i].coeff;
      if (arith_var_is_int(vtbl, x)) {
	/*
	 * Integer variable: we skip it if it has an integer coefficient.
	 */
	if (!q_is_integer(q)) {
	  if (simplex_fixed_variable(solver, x)) {
	    // x is fixed
	    int_constraint_add_fixed_mono(checker, q, x, true, fixed_variable_value(solver, x));
	  } else {
	    // x is not fixed
	    int_constraint_add_mono(checker, q, x);
	  }
	}
      } else {
	/*
	 * Not an integer variable: it must be fixed
	 */
	assert(simplex_fixed_variable(solver, x));
	int_constraint_add_fixed_mono(checker, q, x, false, fixed_variable_value(solver, x));
      }
    }
  }

  return process_integrality_constraint(solver, checker);
}

static bool simplex_integrality_check(simplex_solver_t *solver) {
  int_constraint_t checker;
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  row_t *row;
  thvar_t x;
  uint32_t i, n;
  bool feasible;
  bool pure_integer;

  feasible = true;

  pure_integer = ! simplex_is_mixed_system(solver);

  init_int_constraint(&checker);
  vtbl = &solver->vtbl;
  matrix = &solver->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    x = matrix_basic_var(matrix, i);
    if (arith_var_is_int(vtbl, x) && !arith_var_value_is_int(vtbl, x)) {
      row = matrix->row[i];
      if (pure_integer || matrix_row_is_integral(solver, row)) {
	feasible = test_integrality_in_row(solver, &checker, row);
	if (! feasible) {
	  break;
	}
	reset_int_constraint(&checker);
      }
    }
  }

  delete_int_constraint(&checker);

  return feasible;
}



#if 1

// NOT READY FOR PRIME TIME.

#include "solvers/simplex/gomory_cuts.h"

/*
 * MIXED-INTEGER GOMORY CUTS
 */

/*
 * When we create atoms on the fly for an existing variable,
 * we reset the prop_ptr so that we can propagate the new atom if necessary.
 * - we reset the pointer to what's saved for the current decision level in the undo stack
 */
static void reset_prop_ptr(simplex_solver_t *solver) {
  assert(solver->stack.top == solver->decision_level + 1);
  solver->bstack.prop_ptr = solver->stack.data[solver->decision_level].n_bounds;
  /* if (solver->base_level == 0) { */
  /*   assert(solver->trail_stack.top == 0); */
  /*   solver->bstack.prop_ptr = 0; */
  /* } else { */
  /*   assert(solver->trail_stack.top > 0); */
  /*   solver->bstack.prop_ptr = arith_trail_top(&solver->trail_stack)->bound_ptr; */
  /* } */
}

/*
 * Build atom (x >= c) or (x <= c) on the fly
 * - flag is_int indicates whether x is an integer variable
 */
static literal_t mk_dynamic_ge_atom(simplex_solver_t *solver, thvar_t x, bool is_int, rational_t *c) {
  int32_t new_idx;
  literal_t l;

  assert(x != const_idx);

  l = get_literal_for_ge_atom(&solver->atbl, x, is_int, c, &new_idx);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, x, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, x, new_idx);
  }
  return l;
}

static literal_t mk_dynamic_le_atom(simplex_solver_t *solver, thvar_t x, bool is_int, rational_t *c) {
  int32_t new_idx;
  literal_t l;

  assert(x != const_idx);

  l = get_literal_for_le_atom(&solver->atbl, x, is_int, c, &new_idx);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, x, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, x, new_idx);
  }
  return l;
}


/*
 * Build an atom equivalent to p >= 0.
 */
static literal_t mk_gomory_atom(simplex_solver_t *solver) {
  poly_buffer_t *b;
  bool negated, is_int;
  thvar_t x;

  b = &solver->buffer;

  if (poly_buffer_is_zero(b) || poly_buffer_is_pos_constant(b)) {
    reset_poly_buffer(b);
    return true_literal;
  }

  if (poly_buffer_is_neg_constant(b)) {
    reset_poly_buffer(b);
    return false_literal;
  }

#if 0
  is_int = all_integer_vars(solver);
  if (is_int) {
    negated = poly_buffer_make_nonconstant_integral(b);
    x = decompose_and_get_dynamic_var(solver);
    assert(arith_var_is_int(&solver->vtbl, x));
    if (negated) {
      q_floor(&solver->constant);
    } else {
      q_ceil(&solver->constant);
    }
  } else {
    negated = poly_buffer_make_monic(b);
    x = decompose_and_get_dynamic_var(solver);
    assert(! arith_var_is_int(&solver->vtbl, x));
  }
#else
  // This seems to work better
  negated = poly_buffer_make_monic(b);
  x = decompose_and_get_dynamic_var(solver);
  is_int = arith_var_is_int(&solver->vtbl, x);
  if (is_int) {
    if (negated) {
      q_floor(&solver->constant);
    } else {
      q_ceil(&solver->constant);
    }
  }
#endif



#if TRACE
  printf("---> New var:\n");
  print_simplex_vardef(stdout, solver, x);
  printf("\n");
  fflush(stdout);
#endif

  // if negated is true, the atom is (x <= constant)
  // otherwise, it's (x >= constant)
  if (negated) {
    return mk_dynamic_le_atom(solver, x, is_int, &solver->constant);
  } else {
    return mk_dynamic_ge_atom(solver, x, is_int, &solver->constant);
  }
}


/*
 * Literal for an assumption: x >= a
 * - x is an existing variable
 * - is_int indicates whether x is an integer
 */
static literal_t assumed_lb(simplex_solver_t *solver, thvar_t x, bool is_int, rational_t *a) {
  int32_t k;
  literal_t l;

  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0 && xq_eq_q(solver->bstack.bound + k, a)) {
    // this is the current bound on x
    if (solver->decision_level == solver->base_level) {
      return true_literal;
    }
    if (solver->bstack.tag[k] == ARITH_AXIOM_LB) {
      return true_literal;
    }
    if (solver->bstack.tag[k] == ARITH_ASSERTED_LB) {
      return solver->bstack.expl[k].lit;
    }
  }

  // in all other cases, create a new atom
  l = mk_dynamic_ge_atom(solver, x, is_int, a);
  reset_prop_ptr(solver);

  return l;
}


/*
 * Same thing for an assumption x <= a
 */
static literal_t assumed_ub(simplex_solver_t *solver, thvar_t x, bool is_int, rational_t *a) {
  int32_t k;
  literal_t l;

  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0 && xq_eq_q(solver->bstack.bound + k, a)) {
    // this is the current bound on x
    if (solver->decision_level == solver->base_level) {
      return true_literal;
    }
    if (solver->bstack.tag[k] == ARITH_AXIOM_UB) {
      return true_literal;
    }
    if (solver->bstack.tag[k] == ARITH_ASSERTED_UB) {
      return solver->bstack.expl[k].lit;
    }
  }

  // in all other case, create a new atom
  l = mk_dynamic_le_atom(solver, x, is_int, a);
  reset_prop_ptr(solver);

  return l;
}



/*
 * Add a Gomory cut
 * - simplex->buffer contains a polynomial p
 * - the cut is (p >= 0)
 * - this cut is implied by bounds on the variables stored in *g
 *
 * In general, we add a clause of the form
 *   (x_1 >= l_1) /\ ... /\ (x_k >= l_k) /\ ... (x_n <= u_n) => (p >= 0).
 *
 */
static void add_gomory_cut(simplex_solver_t *solver, gomory_vector_t *g) {
  ivector_t *v;
  uint32_t i, n, x;
  bool is_int;
  literal_t l, cut;

  cut = mk_gomory_atom(solver);

#if TRACE
  printf("---> cut atom:\n");
  printf("     ");
  print_simplex_atomdef(stdout, solver, var_of(cut));
  printf("\n");
#endif

  v = &solver->expl_vector;
  ivector_reset(v);

  if (solver->decision_level > solver->base_level) {
    n = g->nelems;
    for (i=0; i<n; i++) {
      x = g->var[i];
      is_int = gomory_var_is_int(g, i);
      assert(is_int == arith_var_is_int(&solver->vtbl, x));
      if (gomory_bound_is_lb(g, i)) {
	l = assumed_lb(solver, x, is_int, g->bound + i);
      } else {
	l = assumed_ub(solver, x, is_int, g->bound + i);
      }
      if (l != true_literal) {
	ivector_push(v, not(l));
      }
    }
  }

  ivector_push(v, cut);

  add_clause(solver->core, v->size, v->data);

#if TRACE
  printf("---> cut atom:\n");
  printf("     ");
  print_simplex_atomdef(stdout, solver, var_of(cut));
  printf("\n");
  printf("---> New clause:\n");
  printf("     ");
  print_litarray(stdout, v->size, v->data);
  printf("\n");
  n = v->size - 1;
  if (n > 0) {
    for (i=0; i<n; i++) {
      printf("     ");
      print_simplex_atomdef(stdout, solver, var_of(v->data[i]));
    }
  }
  fflush(stdout);
#endif

}


/*
 * Try a Gomory cut based on basic variable x
 * - x must be an integer variable with a non-integer value
 */
static bool try_gomory_cut_for_var(simplex_solver_t *solver, gomory_vector_t *g, thvar_t x) {
  arith_vartable_t *vtbl;
  row_t *row;
  rational_t *a;
  xrational_t *val;
  uint32_t i, n;
  int32_t r;
  thvar_t y;
  bool is_int;
  bool is_lb, is_ub;

  assert(arith_var_is_int(&solver->vtbl, x) &&
	 !arith_var_value_is_int(&solver->vtbl, x));

  vtbl = &solver->vtbl;

  r = matrix_basic_row(&solver->matrix, x);
  assert(r >= 0);
  row = matrix_row(&solver->matrix, r);

#if TRACE
  printf("\n--- Try Gomory cut for ");
  print_simplex_var(stdout, solver, x);
  printf(" ---\n");
  print_simplex_row(stdout, solver, row);
  printf("\n\n");
  print_simplex_var(stdout, solver, x);
  printf(" = ");
  print_simplex_var_value(stdout, solver, x);
  printf("; ");
  print_simplex_var_bounds(stdout, solver, x);
  printf("\n");
  fflush(stdout);
#endif

  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 0) {
      a = &row->data[i].coeff;
      is_int = arith_var_is_int(vtbl, y);
      if (! (is_int && q_is_integer(a))) {
	/*
	 * Process term a * y where either y is not an integer variable
	 * or a is not an integer constant.
	 */
	assert(y != x);

	/*
         * Check whether y's value is equal to its lower or upper bound.
	 * If not, we could still generate a Gomory cut with y >= val as
	 * antecedent.
	 */
	val = arith_var_value(vtbl, y);
	is_lb = variable_at_lower_bound(solver, y);
	is_ub = variable_at_upper_bound(solver, y);
	if (! xq_is_rational(val) ||
	    ! (is_lb || is_ub)) {
	  // can't handle non-rational bounds
	  // also skip the case where y is not at one of its bound
	  return false;
	}
	assert(is_lb || is_ub);
	gomory_vector_add_elem(g, y, a, &val->main, is_int, is_lb);

#if TRACE
	print_simplex_var(stdout, solver, y);
	printf(" = ");
	print_simplex_var_value(stdout, solver, y);
	printf("; ");
	print_simplex_var_bounds(stdout, solver, y);
	fflush(stdout);
#endif
      }
    }
  }

  /*
   * Build the cut: terms >= bound
   * - terms are stored in solver->buffer
   * - the bound is stored in solver->aux
   */
  if (make_gomory_cut(g, &solver->buffer)) {
#if TRACE
    printf("\n---> Gomory cut:\n");
    print_simplex_buffer(stdout, solver);
    printf(" >= 0\n\n");
    fflush(stdout);
#endif
    // deal with it
    add_gomory_cut(solver, g);
  }

  // cleanup
  reset_poly_buffer(&solver->buffer);

  return true;
}

/*
 * Scan variables of v and try a Gomory cut for them
 * - each element of v must be a basic integer variable
 *   with a non-integer value.
 * - max_cuts = bound on the total number of cuts
 * - return the number of cuts added
 */
static uint32_t try_gomory_cuts(simplex_solver_t *solver, ivector_t *v, uint32_t max_cuts) {
  gomory_vector_t cut;
  uint32_t i, n, num_cuts;

#if TRACE
  printf("\nTRY GOMORY CUTS: dlevel = %"PRIu32", base_level = %"PRIu32"\n", solver->decision_level, solver->base_level);
  fflush(stdout);
#endif

  init_gomory_vector(&cut);
  num_cuts = 0;
  n = v->size;
  for (i=0; i<n; i++) {
    num_cuts += try_gomory_cut_for_var(solver, &cut, v->data[i]);
    if (num_cuts >= max_cuts) break;
  }
  delete_gomory_vector(&cut);

  return num_cuts;
}


/*
 * Variant: focus on variable x
 */
static bool gomory_cut_for_var(simplex_solver_t *solver, thvar_t x) {
  gomory_vector_t cut;
  bool result;

  init_gomory_vector(&cut);
  result = try_gomory_cut_for_var(solver, &cut, x);
  delete_gomory_vector(&cut);

  return result;
}

#endif




/*
 * FINAL CHECK
 */

/*
 * Each step (implemented by the wrapper functions) starts from
 * a feasible tableau. It then tests for integer infeasibility using
 * one of the techniques above, possibly generates new bounds,
 * then attempt to restore the tableau to be feasible.
 */

/*
 * Generic wrapper:
 * - f is a check function
 * - name is the proceduce name
 *
 * Assumptions on f:
 * - f(solver) returns false if there's a conflict and generates
 *   a conflict explanation.
 * - f may also generate new bounds and set solver->recheck to true
 * - in such a case, the wrapper attempts to restore a feasible tableau.
 */
static bool intfeas_wrapper(simplex_solver_t *solver, const char *name, bool (*f)(simplex_solver_t *)) {
  uint32_t nbounds;

  nbounds = solver->bstack.top;
  solver->recheck = false;
  if (! f(solver)) {
    trace_printf(solver->core->trace, 10, "(unsat by %s)\n", name);
    solver->stats.num_bound_conflicts ++;
    return false;
  } else {
    trace_printf(solver->core->trace, 10, "(%s: %"PRIu32" new bounds)\n", name, solver->bstack.top - nbounds);
    if (solver->recheck) {
      /*
       * Strengthened bounds require rechecking feasibility
       */
      simplex_fix_nonbasic_assignment(solver);
      if (! simplex_make_feasible(solver) ) {
	trace_printf(solver->core->trace, 10, "(infeasible after bound strengthening)\n");
	solver->stats.num_bound_recheck_conflicts ++;
	return false;
      }

      // Since pivoting may have occurred we need to prepare for the next step
      prepare_for_integer_solving(solver);
    } else {
      /*
       * There may be strengthened bounds but everything is still feasible
       * - we force fix_ptr to bstack.top (otherwise, things may break
       *   because the invariant fix_ptr == top is expected to hold)
       */
      solver->bstack.fix_ptr = solver->bstack.top;
    }
  }

  return true;
}


/*
 * Bound strengthening
 */
static bool simplex_intfeas_strengthening(simplex_solver_t *solver) {
  return intfeas_wrapper(solver, "strengthening", simplex_strengthen_bounds);
}

/*
 * Cheap integrality test
 */
static bool simplex_intfeas_integrality_constraints(simplex_solver_t *solver) {
  return intfeas_wrapper(solver, "integrality check", simplex_integrality_check);
}

/*
 * Dioophantine solver
 */
static bool simplex_intfeas_diophantine_check(simplex_solver_t *solver) {
  return intfeas_wrapper(solver, "diophantine solver", simplex_dsolver_check);
}

#if 0
// NOT USED
/*
 * Iterated bound strengthening
 */
static bool simplex_intfeas_iter_strengthening(simplex_solver_t *solver) {
  return intfeas_wrapper(solver, "strengthening", simplex_strengthen_bounds_iter);
}
#endif

/*
 * Check whether the current set of constraints is integer feasible
 * - return true if it is
 * - if it is not, do something about it and return false.
 * - the system must be feasible (in the reals)
 */
static bool simplex_make_integer_feasible(simplex_solver_t *solver) {
  ivector_t *v;
  thvar_t x;
  uint32_t nbounds, bb_score, n;

#if TRACE_BB
  printf("\n--- make integer feasible [dlevel = %"PRIu32", decisions = %"PRIu64"]: %"PRId32
         " integer-invalid vars\n", solver->core->decision_level, solver->core->stats.decisions,
         simplex_num_integer_invalid_vars(solver));
#endif

#if DEBUG
  check_assignment(solver);
  check_vartags(solver);
#endif

  if (simplex_assignment_integer_valid(solver)) {
    return true;
  }

  solver->stats.num_make_intfeasible ++;

  trace_printf(solver->core->trace, 10, "(testing integer feasibility)\n");

#if TRACE_INTFEAS
  printf("\nMAKE INTEGER FEASIBLE %"PRIu32" [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	 solver->stats.num_make_intfeasible, solver->core->decision_level, solver->core->stats.decisions);
  print_simplex_vars(stdout, solver);
  printf("\n");
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif

  prepare_for_integer_solving(solver);

  /*
   * Try bound strengthening + integrality test + diophantine check
   */
  nbounds = solver->bstack.top;
  if (false && !simplex_intfeas_strengthening(solver)) return false;
  if (!simplex_intfeas_integrality_constraints(solver)) return false;
  if (false && !simplex_intfeas_diophantine_check(solver)) return false;
  if (false && !simplex_intfeas_strengthening(solver)) return false;

  /*
   * TRY OUR LUCK
   */
  if (underconstrained(solver)) {
    if (simplex_try_naive_integer_search(solver)) {
      trace_printf(solver->core->trace, 10, "(feasible by naive search)\n");
      solver->bstack.prop_ptr = solver->bstack.fix_ptr;
      return true;
    }
  }

  /*
   * If we've learned new bounds in the previous phases,
   * try more rounds of bound strengthening.
   */
  if (false && solver->bstack.top > nbounds && !simplex_intfeas_strengthening(solver)) {
    return false;
  }


  /*
   * BRANCH
   */

  /*
   * At this point: no unsat detected. But bounds may have been strengthened
   * All integer basic variables have an integer value.
   */

  // collect the integer basic variables that have a non-integer value
  v = &solver->aux_vector;
  assert(v->size == 0);
  collect_non_integer_basic_vars(solver, v);
  if (v->size == 0) {
    if (! simplex_assignment_integer_valid(solver)){
      abort();
    }
    solver->bstack.prop_ptr = solver->bstack.fix_ptr;
    return true;
  }

#if TRACE_INTFEAS
  printf("\nMAKE INTEGER FEASIBLE %"PRIu32" [dlevel = %"PRIu32", decisions = %"PRIu64"]\n\n",
	 solver->stats.num_make_intfeasible, solver->core->decision_level, solver->core->stats.decisions);
  printf("BRANCHING REQUIRED\n");
  print_simplex_vars(stdout, solver);
  printf("\n");
  print_simplex_matrix(stdout, solver);
  print_simplex_bounds(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif

  /*
   * Create a branch atom or create Gomory cuts
   */
  x = select_branch_variable(solver, v, &bb_score);
  trace_printf(solver->core->trace, 3,
	       "(branch & bound: %"PRIu32" candidates, branch variable = i!%"PRId32", score = %"PRIu32")\n",
	       v->size, x, bb_score);

  if (solver->stats.num_branch_atoms >= 20) {
    if (false && v->size > 1 && bb_score > 200000000 && solver->stats.num_gomory_cuts < 100) {
      n = try_gomory_cuts(solver, v, 100);
      solver->stats.num_gomory_cuts += n;
      trace_printf(solver->core->trace, 3, "(Gomory cuts: %"PRIu32" cuts created)\n", n);
      if (n > 0) goto done;
      solver->core->stats.conflicts += 1000;
    } else if (bb_score > 100000000) {
      n = gomory_cut_for_var(solver, x);
      solver->stats.num_gomory_cuts ++;
      if (n > 0) {
	trace_printf(solver->core->trace, 3, "(Created Gomory cut on var i!%"PRId32")\n", x);
      } else {
	trace_printf(solver->core->trace, 3, "(Failed to create Gomory cut on var i!%"PRId32")\n", x);
      }
      if (n > 0) goto done;
      //      solver->core->stats.conflicts += 1000;
    }
  }

  create_branch_atom(solver, x);
  solver->core->stats.conflicts += 40;

#if TRACE_INTFEAS
  print_branch_candidates(stdout, solver, v);
  printf("\n\nDONE\n");
  fflush(stdout);
#endif

 done:
  ivector_reset(v);

  assert(x != null_thvar);

  return false;
}






/*********************************
 *   PROCESS EGRAPH ASSERTIONS   *
 ********************************/

/*
 * When assertions in egraph_queue are processed, we know that the egraph
 * has not found a conflict.
 */

/*
 * Construct a conflict when we have bound k ==> (x1 != x2)
 * after the egraph propagated that (x1 == x2)
 * - id = egraph edge that triggered (x1 == x2)
 */
static void record_egraph_eq_conflict(simplex_solver_t *solver, int32_t k, thvar_t x1, thvar_t x2, int32_t id) {
  ivector_t *v;
  eterm_t t1, t2;

  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_explain_bound(solver, k, v); // conjunction of literals that imply k

  t1 = arith_var_eterm(&solver->vtbl, x1);
  t2 = arith_var_eterm(&solver->vtbl, x2);
  egraph_explain_term_eq(solver->egraph, t1, t2, id, v); // add literals that imply (x1 == x2)

  // turn v into a conflict clause
  convert_expl_to_clause(v);
  ivector_push(v, null_literal); // end-marker

#if 0
  printf("\n---> SIMPLEX CONFLICT on g!%"PRId32" == g!%"PRId32" (conflict with bound)\n",
	 arith_var_eterm(&solver->vtbl, x1), arith_var_eterm(&solver->vtbl, x2));
#endif
  record_theory_conflict(solver->core, v->data);

  solver->stats.num_conflicts ++;
}


/*
 * Process (x1 == x2)
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become equal in the egraph
 * - id = egraph edge that triggered merge of x1 and x2's classes
 * - return false if there's a conflict, true otherwise
 */
static bool simplex_process_var_eq(simplex_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id) {
  rational_t *c;
  egraph_expl_triple_t *triple;
  literal_t l;
  thvar_t y;
  int32_t k, cmp_lb, cmp_ub;

  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2) && x1 != x2);

#if TRACE
  printf("---> Simplex: process egraph equality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" = ");
  print_simplex_var(stdout, solver, x2);
  printf(" [dlevel = %"PRIu32"]\n", solver->core->decision_level);
  if (!arith_var_is_free(&solver->vtbl, x1)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x1);
  }
  if (!arith_var_is_free(&solver->vtbl, x2)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x2);
  }
  fflush(stdout);
#endif

  /*
   * build p such that p = 0 is equivalent to x1 = x2
   * p is in solver->buffer
   * l is a simplification code:
   * can be false_literal if x1 = x2 is unsat
   * l should never be true_literal
   */
  l = simplify_dynamic_vareq(solver, x1, x2);
  if (l == false_literal) {
    // p = 0 is false, we force a conflict by turning this into 1 = 0
    y = const_idx;
    q_clear(&solver->constant);
    c = &solver->constant;
    reset_poly_buffer(&solver->buffer);
  } else {
    assert(l != true_literal);
    // get y and c such that y = c is equivalent to p = 0
    y = decompose_and_get_dynamic_var(solver); // store c in solver-constant and reset buffer
    c = &solver->constant;
  }

#if TRACE
  printf("     asserting ");
  print_simplex_var(stdout, solver, y);
  printf(" == ");
  q_print(stdout, c);
  printf("\n");
  if (! arith_var_is_free(&solver->vtbl, y)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, y);
  }
#endif


  /*
   * assert (y >= c) and (y <= c) but check for conflicts first
   * we use cmp_lb and cmp_ub as indicators:
   *
   *   cmp_lb < 0  if lower bound on y < c (y >= c is asserted)
   *   cmp_lb = 0  if lower bound on y = c (y >= c is redundant)
   *   cmp_lb > 0  if lower bound on y > c (conflict)
   *
   *   cmp_ub < 0  if upper bound on y < c (conflict)
   *   cmp_ub = 0  if upper bound on y = c (y <= c is redundant)
   *   cmp_ub > 0  if upper bound on y > c (y <= c is asserted)
   */
  cmp_lb = -1;
  cmp_ub = +1;

  k = arith_var_lower_index(&solver->vtbl, y);
  if (k >= 0) {
    cmp_lb = xq_cmp_q(solver->bstack.bound + k, c);
    if (cmp_lb > 0) {
      record_egraph_eq_conflict(solver, k, x1, x2, id);

#if TRACE
      printf("     conflict with bound ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif
      return false;
    }
  }

  k = arith_var_upper_index(&solver->vtbl, y);
  if (k >= 0) {
    cmp_ub = xq_cmp_q(solver->bstack.bound + k, c);
    if (cmp_ub < 0) {
      record_egraph_eq_conflict(solver, k, x1, x2, id);

#if TRACE
      printf("     conflict with bound ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif

      return false;
    }
  }

  triple = NULL; // otherwise GCC gives a warning
  if (cmp_lb < 0 || cmp_ub > 0) {
    triple = (egraph_expl_triple_t *) arena_alloc(&solver->arena, sizeof(egraph_expl_triple_t));
    triple->var[0] = x1;
    triple->var[1] = x2;
    triple->id = id;
  }
  if (cmp_lb < 0) {
    push_lb_egraph(solver, y, c, triple);
  }
  if (cmp_ub > 0) {
    push_ub_egraph(solver, y, c, triple);
  }

  assert(simplex_fixed_variable(solver, y) && q_eq(fixed_variable_value(solver, y), c));

  return true;
}



/*
 * Return a literal and atom equivalent to (y > c)
 */
static literal_t create_pos_atom(simplex_solver_t *solver, thvar_t y, rational_t *c) {
  int32_t new_idx;
  literal_t l;

  assert(y != const_idx);

  // get the atom (y <= c)
  l = get_literal_for_le_atom(&solver->atbl, y, arith_var_is_int(&solver->vtbl, y), c, &new_idx);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, y, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, y, new_idx);
  }
  return not(l);
}

/*
 * Return literal/atom equivalent to (y < c)
 */
static literal_t create_neg_atom(simplex_solver_t *solver, thvar_t y, rational_t *c) {
  int32_t new_idx;
  literal_t l;

  assert(y != const_idx);

  // get atom (y >= c)
  l = get_literal_for_ge_atom(&solver->atbl, y, arith_var_is_int(&solver->vtbl, y), c, &new_idx);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, y, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, y, new_idx);
  }
  return not(l);
}


/*
 * Create the lemma (eq t1 t2) or (x1 - x2 > 0) or (x1 - x2 < 0)
 * - x1 and x2 must be two distinct variables, attached to the eterms t1 and t2
 * - return the number of lemmas created (which is either 1 or
 * - if the lemma already exist (i.e. no need to generate it again), return 0
 * - otherwise create the lemma and return 1
 */
static uint32_t simplex_trichotomy_lemma(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  cache_t *cache;
  cache_elem_t *e;
  rational_t *c;
  thvar_t y;
  eterm_t t1, t2;
  literal_t l, l0, l1, l2;

  assert(x1 != x2);

  // normalize: we want x1 < x2
  if (x2 < x1) {
    y = x1; x1 = x2; x2 = y;
  }

#if TRACE
  t1 = arith_var_eterm(&solver->vtbl, x1);
  t2 = arith_var_eterm(&solver->vtbl, x2);
  printf("---> Simplex: trichotomy lemma:\n");
  printf("     x1 = ");
  print_simplex_var(stdout, solver, x1);
  printf(", t1 = ");
  print_eterm_id(stdout, t1);
  printf("\n");
  printf("     x2 = ");
  print_simplex_var(stdout, solver, x2);
  printf(", t2 = ");
  print_eterm_id(stdout, t2);
  printf("\n");
  if (!arith_var_is_free(&solver->vtbl, x1)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x1);
  }
  if (!arith_var_is_free(&solver->vtbl, x2)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x2);
  }
#endif

  cache = simplex_get_cache(solver);
  e = cache_get(cache, TRICHOTOMY_LEMMA, x1, x2);
  if (e->flag != NEW_CACHE_ELEM) {
    // trichotomy instance already exists for x1 and x2
#if TRACE
    printf("     redundant\n");
#endif
    return 0;
  }

  e->flag = ACTIVE_ARITH_LEMMA;

  /*
   * create the egraph equality l := (eq t1 t2)
   */
  t1 = arith_var_eterm(&solver->vtbl, x1);
  t2 = arith_var_eterm(&solver->vtbl, x2);
  assert(t1 != null_eterm && t2 != null_eterm);
  l = egraph_make_simple_eq(solver->egraph, pos_occ(t1), pos_occ(t2));

#if TRACE
  printf("     trichotomy lemma: egraph atom: ");
  print_literal(stdout, l);
  printf(" := ");
  print_egraph_atom_of_literal(stdout, solver->egraph, l);
  printf("\n");
#endif

  /*
   * build p such that p=0 is equivalent to (x1 = x2)
   * p is stored in solver->buffer
   * l0 = simplification code
   */
  l0 = simplify_dynamic_vareq(solver, x1, x2);
  if (l0 == false_literal) {
    /*
     * x1 = x2 is false: add (not (eq t1 t2)))) as an axiom for the egraph
     */
#if TRACE
    printf("     reduced to 1 != 0\n");
    printf("     add unit clause: ");
    print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
    printf("\n");
#endif
    add_unit_clause(solver->core, not(l));
    reset_poly_buffer(&solver->buffer);

#if 0
    printf("---> SIMPLEX: trichotomy lemma for ");
    print_simplex_var(stdout, solver, x1);
    printf(" ");
    print_simplex_var(stdout, solver, x2);
    printf(" (axiom)\n");
#endif
    solver->stats.num_reduced_tricho ++;

  } else {
    assert(l0 != true_literal); // since x1 != x2

    /*
     * get y and c such that y = c is equivalent to x1 = x2
     */
    y = decompose_and_get_dynamic_var(solver); // store c in solver->constant and reset buffer
    c = &solver->constant;

    l1 = create_pos_atom(solver, y, c);   // l1 := y > c
    l2 = create_neg_atom(solver, y, c);   // l2 := y < c

#if TRACE
    printf("     reduced to: ");
    print_simplex_var(stdout, solver, y);
    printf(" != ");
    q_print(stdout, c);
    printf("\n");
    if (! arith_var_is_free(&solver->vtbl, y)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, y);
    }
    printf("     simplex atom:\n      ");
    print_literal(stdout, l1);
    printf(" := ");
    print_simplex_atom_of_literal(stdout, solver, l1);
    printf("\n      ");
    print_literal(stdout, l2);
    printf(" := ");
    print_simplex_atom_of_literal(stdout, solver, l2);
    printf("\n");

    printf("     trichotomy clauses:\n");
    printf("     (OR ");
    print_egraph_atom_of_literal(stdout, solver->egraph, l);
    printf(" ");
    print_simplex_atom_of_literal(stdout, solver, l1);
    printf(" ");
    print_simplex_atom_of_literal(stdout, solver, l2);
    printf(")\n");
    printf("     (OR ");
    print_simplex_atom_of_literal(stdout, solver, not(l1));
    printf(" ");
    print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
    printf(")\n");
    printf("     (OR ");
    print_simplex_atom_of_literal(stdout, solver, not(l2));
    printf(" ");
    print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
    printf(")\n");
#endif

    add_ternary_clause(solver->core, l, l1, l2);

    /*
     * The following two clauses encode
     *   (t1 = t2) => (x1 - x2) <= 0
     *   (t1 = t2) => (x1 - x2) >= 0
     * They are redundant but adding them improves performance.
     */
    add_binary_clause(solver->core, not(l), not(l1));
    add_binary_clause(solver->core, not(l), not(l2));

    solver->stats.num_tricho_lemmas ++;
#if 0
    printf("---> SIMPLEX: trichotomy lemma for ");
    print_simplex_var(stdout, solver, x1);
    printf(" ");
    print_simplex_var(stdout, solver, x2);
    printf(" (trichotomy)\n");
#endif
  }

  return 1;
}



/*
 * Process (x1 != x2)
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this does nothing: all disequalities are handled lazily in reconcile_model
 */
static void simplex_process_var_diseq(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2) && x1 != x2);

#if TRACE
  printf("---> Simplex: egraph disequality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" != ");
  print_simplex_var(stdout, solver, x2);
  printf(" [dlevel = %"PRIu32", decisions = %"PRIu64"]\n", solver->core->decision_level, solver->core->stats.decisions);
  if (! arith_var_is_free(&solver->vtbl, x1)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x1);
  }
  print_simplex_var_bounds(stdout, solver, x1);
  if (! arith_var_is_free(&solver->vtbl, x2)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x2);
  }
  print_simplex_var_bounds(stdout, solver, x2);
#endif
}


/*
 * Assert that all variables a[0] ... a[n-1] are pairwise distinct
 * - they are attached to egraph terms t[0] ... t[n-1]
 * - the function is called when (distinct t[0] ... t[n-1]) is asserted in the egraph
 * - this does nothing: just print trace if TRACE is enabled
 */
static void simplex_process_var_distinct(simplex_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
#if TRACE
  uint32_t i, j;

  for (i=0; i<n-1; i++) {
    for (j=i+1; j<n; j++) {
      simplex_process_var_diseq(solver, a[i], a[j]);
    }
  }
#endif
}


/*
 * Process all assertions in the egraph queue
 * - return true if no conflict is found
 * - return false and add a conflict clause to the core otherwise.
 */
static bool simplex_process_egraph_assertions(simplex_solver_t *solver) {
  eassertion_t *a, *end;
  thvar_t x, y, z;
  thvar_t pre_x, pre_y;

  if (eassertion_queue_is_nonempty(&solver->egraph_queue)) {
    /*
     * If the queue is empty, the call to eassertion_queue_end computes NULL + 0,
     * which is undefined behavior (reported when compiled with MODE=sanitize).
     */
    a = eassertion_queue_start(&solver->egraph_queue);
    end = eassertion_queue_end(&solver->egraph_queue);

    pre_x = null_thvar;
    pre_y = null_thvar;

    while (a < end) {
      switch (eassertion_get_kind(a)) {
      case EGRAPH_VAR_EQ:
	if (! simplex_process_var_eq(solver, a->var[0], a->var[1], a->id)) {
#if 0
	  printf("---> SIMPLEX CONFLICT on g!%"PRId32" == g!%"PRId32"\n",
		 arith_var_eterm(&solver->vtbl, a->var[0]),
		 arith_var_eterm(&solver->vtbl, a->var[1]));
#endif
	  reset_eassertion_queue(&solver->egraph_queue);
	  return false;
	}
	break;

      case EGRAPH_VAR_DISEQ:
	x = a->var[0];
	y = a->var[1];
	if (x > y) {
	  z = x; x = y; y = z;
	}
	if (pre_x != x || pre_y != y) {
	  /*
	   * We use pre_x and pre_y as a cache to filter out duplicate
	   * disequalities.  That's imperfect but that filters out a lot
	   * of redundant disequalities, since the egraph tends to send
	   * several times the same disequality in a sequence.
	   */
	  simplex_process_var_diseq(solver, x, y);
	  pre_x = x;
	  pre_y = y;
	}
	break;

      case EGRAPH_VAR_DISTINCT:
	simplex_process_var_distinct(solver, eassertion_get_arity(a), a->var, a->hint);
	break;

      default:
	assert(false);
	break;
      }
      a = eassertion_next(a);
    }

    reset_eassertion_queue(&solver->egraph_queue);
  }

  return true;
}




/*
 * EGRAPH ASSERTIONS RECEIVED BEFORE START SEARCH
 */

/*
 * Process all assertions in the egraph queue within 'base_propagate'
 * - the tableau is not ready when this function is called
 * - we deal only with equalities here. The reconcile_model function
 *   will generate trichotomy axioms lazily if they're needed later on.
 * - return true if no conflict is found
 * - return false otherwise
 */
static bool simplex_process_egraph_base_assertions(simplex_solver_t *solver) {
  eassertion_t *a, *end;

  assert(! solver->tableau_ready &&
         ! solver->unsat_before_search &&
         solver->base_level == solver->decision_level);

  if (eassertion_queue_is_nonempty(&solver->egraph_queue)) {
    a = eassertion_queue_start(&solver->egraph_queue);
    end = eassertion_queue_end(&solver->egraph_queue);

    while (a < end) {
      switch (eassertion_get_kind(a)) {
      case EGRAPH_VAR_EQ:
	/*
	 * Since we're at the base level, we can treat the equality
	 * as an axiom.
	 */
	simplex_assert_vareq_axiom(solver, a->var[0], a->var[1], true);
	if (solver->unsat_before_search) {
	  // record the conflict in core
	  record_empty_theory_conflict(solver->core);
	  reset_eassertion_queue(&solver->egraph_queue);
	  return false;
	}
	break;

      case EGRAPH_VAR_DISEQ:
	simplex_process_var_diseq(solver, a->var[0], a->var[1]);
	break;

      case EGRAPH_VAR_DISTINCT:
	simplex_process_var_distinct(solver, eassertion_get_arity(a), a->var, a->hint);
	break;

      default:
	assert(false);
	break;
      }
      a = eassertion_next(a);
    }

    reset_eassertion_queue(&solver->egraph_queue);
  }

  return true;
}



/***************************
 *  INTERNALISATION START  *
 **************************/

/*
 * This is called before any new atom/variable is created
 * (before start_search).
 * - we reset the tableau and restore the matrix if needed
 */
void simplex_start_internalization(simplex_solver_t *solver) {
  simplex_reset_tableau(solver);
  simplex_restore_matrix(solver);

  assert(solver->matrix_ready && ! solver->tableau_ready);
}



/******************
 *  START SEARCH  *
 *****************/

/*
 * Start search:
 * - simplify the matrix
 * - initialize the tableau
 * - compute the initial assignment
 */
void simplex_start_search(simplex_solver_t *solver) {
  bool feasible;

#if TRACE
  uint32_t i, n;

  printf("---> SIMPLEX START SEARCH\n");
  printf("---> %"PRIu32" initial bounds\n", solver->bstack.top);
  n = solver->bstack.top;
  for (i=0; i<n; i++) {
    printf("     ");
    print_simplex_bound(stdout, solver, i);
    printf("\n");
  }
  printf("\n");
#endif

  // clear the interrupt flag
  solver->interrupted = false;

  /*
   * If start_search is called after pop and without an intervening
   * start_internalization, then matrix_ready and tableau_ready are both false.
   *
   * If start_search is called after push and without an intervening
   * start_internalization, then tableau_ready may be true and matrix_ready
   * false.
   *
   * We force restore reset_tableau and restore_matrix here.
   * This does nothing if the tableau is already reset and the matrix is ready.
   */
  simplex_reset_tableau(solver);
  simplex_restore_matrix(solver);

  assert(solver->matrix_ready && !solver->tableau_ready);

  // reset the search statistics
  simplex_set_initial_stats(solver);

  if (solver->unsat_before_search) {
    record_empty_theory_conflict(solver->core);
    solver->stats.num_conflicts ++;
    goto done;
  }

  // process all level 0 assertions: turn them into bounds
  feasible = simplex_process_assertions(solver);
  if (! feasible) goto done;

  // simplify
  simplex_simplify_matrix(solver);
  assert(good_matrix(&solver->matrix));

  // initialize the propagator here if propagation is enabled
  if (simplex_option_enabled(solver, SIMPLEX_PROPAGATION)) {
    simplex_init_propagator(solver);
  }

  // compute the tableau
  simplex_init_tableau(solver);
  assert(good_matrix(&solver->matrix));

  // set bounds for all fixed variables
  simplex_check_fixed_vars(solver);
  if (solver->unsat_before_search) {
    record_empty_theory_conflict(solver->core);
    solver->stats.num_conflicts ++;
    goto done;
  }

  // compute the initial variable assignment
  reset_int_heap(&solver->infeasible_vars);
  simplex_init_assignment(solver);
  feasible = simplex_make_feasible(solver);
  if (! feasible) goto done;

  solver->last_conflict_row = -1;

  // reset heuristics counters for integer feasibility
  solver->stats.num_branch_atoms = 0;
  solver->stats.num_gomory_cuts = 0;

  // integer solving flags
  // enable_dfeas is used in simplex_dsolver_check
  solver->integer_solving = false;
  solver->enable_dfeas = true;
  if (simplex_has_integer_vars(solver) && simplex_option_enabled(solver, SIMPLEX_ICHECK)) {
#if TRACE
    printf("---> icheck active\n");
    fflush(stdout);
#endif
    solver->check_counter = 0;
  } else {
    solver->check_counter = INT32_MAX;
  }

  // check initial integer feasibility
  if (! simplex_assignment_integer_valid(solver)) {
#if TRACE
    printf("---> initial assignment not integer feasible\n");
    fflush(stdout);
#endif
  }

  // literals implied by toplevel atoms
  simplex_literal_propagation(solver);

  // theory propagation based on all initial bounds
  if (simplex_option_enabled(solver, SIMPLEX_PROPAGATION)) {
    simplex_start_propagator(solver);
  }

 done:
#if DUMP
  dump_state(solver);
#endif

#if 0
  printf("\n\n*** SIMPLEX START ***\n");
  // print_simplex_vars_summary(stdout, solver);
  printf("==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Assignment ====\n");
  print_simplex_assignment(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  printf("\n==== Atoms ====\n");
  print_simplex_atoms(stdout, solver);
  printf("\n");
#endif

  return;
}


/*
 * Stop the search: sets flag solver->interrupted to true and
 * stops the diophantine solver if it's active.
 * - the solver->interrupted flag is set to false by start_search
 * - currently, the interrupted flag is checked in every iteration
 *   of the make feasible procedure
 */
void simplex_stop_search(simplex_solver_t *solver) {
  solver->interrupted = true;
  if (solver->dsolver != NULL) {
    dsolver_stop_search(solver->dsolver);
  }
}



/***************
 *  PROPAGATE  *
 **************/

/*
 * Process all assertions
 * - this function may be called before start_search
 * - if it's called before start_search, the tableau is not ready
 */
bool simplex_propagate(simplex_solver_t *solver) {
  bool feasible;

#if TRACE
  printf("---> SIMPLEX PROPAGATE\n");
#endif

  feasible = true;

  if (! solver->tableau_ready) {
    // start search has not been called yet
    assert(solver->decision_level == solver->base_level);
    if (solver->unsat_before_search) {
      record_empty_theory_conflict(solver->core);
      feasible = false;
      goto done;
    }

    feasible = simplex_process_assertions(solver);
    if (! feasible) goto done;

    feasible = simplex_process_egraph_base_assertions(solver);
    goto done;
  }

  assert(! solver->unsat_before_search);

  /*
   * NOTE: we must check whether there are infeasible_vars here.
   *
   * If we get a conflict, we generate a clause that causes backtracking.
   * But it may happen that nothing is propagated to the simplex after this
   * backtracking (i.e., the assertion_queue does not change and the
   * eassertion_queue is empty). In that case, we could end up with
   * an invalid tableau and variable assignment because nothing will
   * force us to restore feasibility. See issues 251 and 253.
   */
  if (solver->assertion_queue.prop_ptr < solver->assertion_queue.top ||
      eassertion_queue_is_nonempty(&solver->egraph_queue) ||
      !int_heap_is_empty(&solver->infeasible_vars)) {

    // process all assertions
    feasible = simplex_process_assertions(solver);
    if (! feasible) goto done;

    // assertions from the egraph
    feasible = simplex_process_egraph_assertions(solver);
    if (! feasible) goto done;

    // update the assignment for the non-basic variables
    simplex_fix_nonbasic_assignment(solver);

    // check for feasibility
    feasible = simplex_make_feasible(solver);
    if (! feasible) goto done;

    // propagate egraph equalities
    if (solver->eqprop != NULL) {
      simplex_propagate_equalities(solver);
    }

    /*
     * Theory propagation
     * - propagation may strengthen bounds on integer variables,
     *   which may cause a conflict or require a new call to
     *   make_feasible.
     */
    if (simplex_option_enabled(solver, SIMPLEX_PROPAGATION)) {
      solver->recheck = false;

      if (true) {
	feasible = simplex_do_propagation(solver);
      } else {
	feasible = simplex_strengthen_bounds(solver);
      }

      if (! feasible) goto done;

      if (solver->recheck) {
        simplex_fix_nonbasic_assignment(solver);
        feasible = simplex_make_feasible(solver);
        if (! feasible) goto done;
      } else {
        // there may be implied bounds but they don't require fixing the assignment
        solver->bstack.fix_ptr = solver->bstack.top;
      }

#if DEBUG
      check_vartags(solver);
      check_assignment(solver);
      check_integer_bounds(solver);
#endif
    }

    // propagate literals
    simplex_literal_propagation(solver);

  } else if (solver->bstack.prop_ptr < solver->bstack.top) {
    /*
     * We may end up here on the first call to propagate after
     * simplex_final_check if the diophantine solver has strengthened
     * some bounds without causing a conflict.  In such a case, a new
     * branch &bound atom is created but there are no new assertion yet.
     *
     * We must call simplex_literal_propagation to at least force
     * solver->bstack.prop_ptr to be equal to solver->bstack.top.
     * This is required before the next call to increase decision level.
     */
    simplex_literal_propagation(solver);
  }

  /*
   * EXPERIMENTAL: periodically test for integer feasibility
   */
  if (false && solver->check_counter -- <= 0) {
    if (simplex_has_integer_vars(solver)) {
      solver->check_counter = solver->check_period;

      feasible = simplex_assignment_integer_valid(solver);
      if (feasible) goto done;

      solver->recheck = false;
      feasible = simplex_dsolver_check(solver);
      if (! feasible) goto done;

#if TRACE_INTFEAS
      assert(solver->dsolver != NULL);
      printf("--- general solution from dsolver ---\n");
      dsolver_print_gen_solution(stdout, solver->dsolver);
      printf("\n\n");
      fflush(stdout);
#endif

      if (solver->recheck) {
        simplex_fix_nonbasic_assignment(solver);
        feasible = simplex_make_feasible(solver);
        if (! feasible) goto done;
      } else {
        // bounds may have been strengthened
        // but don't require fixing the assignment
        solver->bstack.fix_ptr = solver->bstack.top;
      }

#if DEBUG
      check_vartags(solver);
      check_assignment(solver);
      check_integer_bounds(solver);
#endif

      // the dsolver may have added new bounds
      // check whether we can propagate literals
      simplex_literal_propagation(solver);

    } else {
      solver->check_counter = INT32_MAX; // i.e., infinity
    }
  }

 done:
#if DEBUG
  check_bound_marks(solver);
#endif

  return feasible;
}




/*******************
 *   FINAL CHECK   *
 ******************/

/*
 * Check for integer feasibility
 */
fcheck_code_t simplex_final_check(simplex_solver_t *solver) {
#if DEBUG
  check_assignment(solver);
  check_integer_bounds(solver);
  check_vartags(solver);
  check_bound_marks(solver);
#endif

#if TRACE
  printf("---> SIMPLEX FINAL CHECK [dlevel = %"PRIu32", decisions = %"PRIu64"]\n",
         solver->decision_level, solver->core->stats.decisions);
  fflush(stdout);
#endif

  if (simplex_has_integer_vars(solver)) {
    if (simplex_make_integer_feasible(solver)) {
      return FCHECK_SAT;
    } else {
      return FCHECK_CONTINUE;
    }
  } else {
    assert(simplex_assignment_integer_valid(solver));
    return FCHECK_SAT;
  }
}


/*
 * Clear: nothing to clear.
 */
void simplex_clear(simplex_solver_t *solver) {
}


/*****************************
 *  INCREASE DECISION LEVEL  *
 ***************************/

/*
 * Increase simplex level but don't do it in eqprop
 * - this is needed in simplex_push
 */
static void simplex_increase_dlevel(simplex_solver_t *solver) {
  uint32_t nb, na;

  nb = solver->bstack.top;
  na = solver->assertion_queue.top;
  arith_push_undo_record(&solver->stack, nb, na);
  solver->decision_level ++;

  // new scope in arena
  arena_push(&solver->arena);
}

/*
 * Increase dlevel in simplex and eqprop
 */
void simplex_increase_decision_level(simplex_solver_t *solver) {
  simplex_increase_dlevel(solver);
  if (solver->eqprop != NULL) {
#if 0
    printf("---> eq prop: increase decision level to %"PRIu32"\n", solver->decision_level);
#endif
    offset_manager_increase_decision_level(&solver->eqprop->mngr);
  }
#if TRACE
  printf("\n---> Simplex: increase decision level to %"PRIu32"\n", solver->decision_level);
#endif
}



/******************
 *  BACKTRACKING  *
 *****************/

/*
 * Backtrack to back_level:
 * - remove all bounds and assertions added at levels > back_level
 * - don't propagate the backtrack to eqprop (this is needed for simplex_pop)
 */
static void simplex_go_back(simplex_solver_t *solver, uint32_t back_level) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  arith_undo_record_t *undo;
  int32_t *a;
  uint32_t i, n;
  thvar_t x;
  int32_t k;

  assert(solver->base_level <= back_level && back_level < solver->decision_level);

  /*
   * stack->data[back_level + 1] = record created on entry to back_level + 1
   * so undo->n_bounds = number of bounds processed at back_level
   *    undo->n_assertions = number of assertions processed at back_level
   *
   * When back_level + 1 was entered, simplex_propagate had completed without conflict
   * so bstack->fix_ptr and bstack->prop_ptr were both equal to bstack->top,
   * and assertion_queue->prop_ptr was equal to assertion_queue->top.
   */
  assert(back_level + 1 < solver->stack.top);
  undo = solver->stack.data + back_level + 1;

  vtbl = &solver->vtbl;
  bstack = &solver->bstack;


  /*
   * Remove the bounds and fix the lb/ub tags
   */
  assert(undo->n_bounds <= bstack->prop_ptr && bstack->prop_ptr <= bstack->fix_ptr &&
         bstack->fix_ptr <= bstack->top);

  i = bstack->top;

  /*
   * Bounds in bstack[fix_ptr ... top-1] have not been visited by fix_nonbasic_assignment
   * - so variable assignment and tags are what they were before
   *   all bounds i for bstack->fix_ptr <= i < bstack->top have
   *   been processed
   * ==> we must not touch the lb or ub tags for these bounds
   */
  n = bstack->fix_ptr;
  while (i > n) {
    i --;
    x = bstack->var[i];
    k = bstack->pre[i]; // previous bound of the same kind
    if (constraint_is_lower_bound(bstack, i)) {
      // restore k as lower index
      set_arith_var_lower_index(vtbl, x, k);
    } else {
      // restore k as upper index
      assert(constraint_is_upper_bound(bstack, i));
      set_arith_var_upper_index(vtbl, x, k);
    }
  }


  /*
   * Rest of the bounds: restore previous bound and clear the tags
   */
  n = undo->n_bounds;
  while (i > n) {
    i --;
    x = bstack->var[i];
    k = bstack->pre[i]; // previous bound of the same kind
    if (constraint_is_lower_bound(bstack, i)) {
      clear_arith_var_lb(vtbl, x);
      set_arith_var_lower_index(vtbl, x, k);
    } else {
      assert(constraint_is_upper_bound(bstack, i));
      clear_arith_var_ub(vtbl, x);
      set_arith_var_upper_index(vtbl, x, k);
    }
  }

  bstack->top = n;
  bstack->prop_ptr = n;
  bstack->fix_ptr = n;

  /*
   * Remove the assertions
   */
  assert(undo->n_assertions <= solver->assertion_queue.prop_ptr &&
         solver->assertion_queue.prop_ptr <= solver->assertion_queue.top);

  n = undo->n_assertions;
  a = solver->assertion_queue.data;
  i = solver->assertion_queue.top;
  while (i > n) {
    i --;
    k = atom_of_assertion(a[i]);
    unmark_arith_atom(&solver->atbl, k);
  }
  solver->assertion_queue.top = n;
  solver->assertion_queue.prop_ptr = n;

  /*
   * Backtrack arena
   */
  n = solver->decision_level;
  do {
    arena_pop(&solver->arena);
    n --;
  } while (n > back_level);


  /*
   * Empty the egraph queue
   */
  reset_eassertion_queue(&solver->egraph_queue);

  /*
   * Restore the undo stack and the decision level
   */
  solver->stack.top = back_level + 1;
  solver->decision_level = back_level;
}


/*
 * Full backtrack
 */
void simplex_backtrack(simplex_solver_t *solver, uint32_t back_level) {
#if TRACE
  printf("---> Simplex: backtracking to level %"PRIu32"\n", back_level);
#endif

  simplex_go_back(solver, back_level);
  if (solver->eqprop != NULL) {
#if 0
    printf("---> eq prop: backtrack to level %"PRIu32"\n", back_level);
#endif
    offset_manager_backtrack(&solver->eqprop->mngr, back_level);
  }


#if DEBUG
  if (solver->tableau_ready) {
    /*
     * NOTE: this may give false alarms if backtrack is called
     * within simplex_pop because the context may be known to
     * be UNSAT before make_feasible or init_assignment have
     * been called.
     *
     * TODO: Fix this.
     */
    check_vartags(solver);
    check_nonbasic_assignment(solver);
  }
#endif

#if TRACE
  printf("---> Simplex: end backtracking\n\n");
#endif


}



/********************
 *  PUSH/POP/RESET  *
 *******************/

/*
 * Start a new base level
 */
void simplex_push(simplex_solver_t *solver) {
  uint32_t nv, na, nr, pa, pb;

  assert(solver->decision_level == solver->base_level &&
         solver->bstack.prop_ptr == solver->bstack.fix_ptr &&
         solver->save_rows &&
         eassertion_queue_is_empty(&solver->egraph_queue));

  nv = solver->vtbl.nvars;
  na = solver->atbl.natoms;
  nr = solver->saved_rows.size;
  pa = solver->assertion_queue.prop_ptr;
  pb = solver->bstack.prop_ptr;
  arith_trail_save(&solver->trail_stack, nv, na, nr, pa, pb);

  if (solver->cache != NULL) {
    cache_push(solver->cache);
  }

  solver->base_level ++;

  /*
   * we don't want increase_decision_level here (otherwise,
   * eqprop's decision level would be incremented twice).
   */
  simplex_increase_dlevel(solver);

  // propagate to eqprop if present
  if (solver->eqprop != NULL) {
    simplex_push_eqprop(solver);
  }
}


/*
 * Remove all atoms whose id is >= na from the variable indices
 * - this is called before the atoms are actually removed from
 *   the atom table
 */
static void simplex_detach_dead_atoms(simplex_solver_t *solver, uint32_t na) {
  arith_vartable_t *vtbl;
  arith_atomtable_t *atbl;
  arith_atom_t *atm;
  uint32_t i, n, nv;
  thvar_t x;

  assert(na <= solver->atbl.natoms);

  atbl = &solver->atbl;
  vtbl = &solver->vtbl;

  nv = vtbl->nvars;
  n = atbl->natoms;
  for (i=na; i<n; i++) {
    atm = arith_atom(atbl, i);
    x = var_of_atom(atm);
    if (x < nv) {
      // x is still a good variable
      detach_atom_from_arith_var(vtbl, x, i);
    }
  }
}


/*
 * Remove all eterms whose id is >= nt from the term table
 * - this is required to synchronize the egraph and simplex solver after pop.
 * - the egraph removes the dead eterms first then invoke the pop function
 *   of all satellite solvers.
 * - if arithmetic variable x is kept after pop but the egraph term
 *   eterm[x] is not kept, then we must clear eterm[x]
 *
 * NOTE: this work because the 'pop' function in the egraph removes
 * its own dead terms before calling the 'pop' function of all
 * satellite solvers.
 */
static void simplex_remove_dead_eterms(simplex_solver_t *solver) {
  uint32_t nterms;

  if (solver->egraph != NULL) {
    nterms = egraph_num_terms(solver->egraph);
    arith_vartable_remove_eterms(&solver->vtbl, nterms);
  }
}


/*
 * Number of active variables = all variables x whose
 * definition p is not a simple polynomial.
 * For all these variables, the matrix contains a row of
 * the form x - p = 0.  If x is alive, this row must be kept
 * when we backtrack.
 */
static uint32_t num_active_vars(arith_vartable_t *vtbl) {
  polynomial_t *p;
  uint32_t a, i, n;

  a = 0;
  n = vtbl->nvars;
  // skip var 0 since it's not a polynomial
  for (i=1; i<n; i++) {
    p = arith_var_def(vtbl, i);
    if (p != NULL && !simple_poly(p)) {
      a++;
    }
  }

  return a;
}


/*
 * Scan the bound stack backward from top to fix_ptr
 * and clear the ub/lb tags of all variables.
 */
static void roll_back_fix_ptr(simplex_solver_t *solver) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  uint32_t i, n;
  thvar_t x;

  vtbl = &solver->vtbl;
  bstack = &solver->bstack;

  i = bstack->top;
  n = bstack->fix_ptr;
  while (i > n) {
    i --;
    x = bstack->var[i];
    if (xq_eq(bstack->bound + i, arith_var_value(vtbl, x))) {
      // value[x] = bound[k]
      if (constraint_is_lower_bound(bstack, i)) {
	clear_arith_var_lb(vtbl, x);
      } else {
	assert(constraint_is_upper_bound(bstack, i));
	clear_arith_var_ub(vtbl, x);
      }
    }
  }
}


/*
 * Return to the previous base level
 */
void simplex_pop(simplex_solver_t *solver) {
  arith_trail_t *top;
  arith_undo_record_t *undo;
  uint32_t nrows, ncolumns;

  assert(solver->base_level > 0 &&
         solver->base_level == solver->decision_level &&
         solver->save_rows);

  solver->unsat_before_search = false;


  /*
   * HACKISH: Backtrack to the previous base_level
   *
   * undo = trail object saved on entry to the current base_level
   * undo->n_bounds = number of bounds in bstack on entry to base_level
   * undo->n_assertions = number of assertions in assertion_queue on
   *                  entry to current base_level
   *
   * If simplex_pop is called without a simplex_check then the
   * preconditions of simplex_backtrack may not hold. We may have
   *     bstack->fix_ptr  < undo->n_bounds
   *     bstack->prop_ptr < undo->n_bounds
   *     assertion_queue->prop_ptr < assertion_queue->n_assertions.
   *
   * In such a case, we fix the fix/prop_ptr before calling
   * backtrack. This does not cause problems since we'll restore
   * fix_ptr/prop_ptr after simplex_backtrack anyway.
   */
  undo = solver->stack.data + solver->base_level;
  solver->base_level --;

  if (solver->bstack.fix_ptr < undo->n_bounds) {
    solver->bstack.fix_ptr = undo->n_bounds;
  }
  if (solver->bstack.prop_ptr < undo->n_bounds) {
    solver->bstack.prop_ptr = undo->n_bounds;
  }
  if (solver->assertion_queue.prop_ptr < undo->n_assertions) {
    solver->assertion_queue.prop_ptr = undo->n_assertions;
  }
  // can't use simplex_backtrack here
  simplex_go_back(solver, solver->base_level);


  /*
   * Remove variables in eqprop. This must be done before we delete
   * variables in solver->vtbl, because polynomials in vtbl->def[x]
   * may occur in the eqprop's data structures.
   */
  if (solver->eqprop != NULL) {
    simplex_pop_eqprop(solver);
  }

  /*
   * Remove saved_rows, variables, and atoms that were
   * created at the current base_level.
   */
  top = arith_trail_top(&solver->trail_stack);
  delete_saved_rows(&solver->saved_rows, top->nsaved_rows);
  arith_vartable_remove_vars(&solver->vtbl, top->nvars);
  simplex_detach_dead_atoms(solver, top->natoms);
  arith_atomtable_remove_atoms(&solver->atbl, top->natoms);
  simplex_remove_dead_eterms(solver);

  if (solver->cache != NULL) {
    cache_pop(solver->cache);
  }

  // restore the propagation pointers
  solver->bstack.prop_ptr = top->bound_ptr;
  solver->bstack.fix_ptr = top->bound_ptr;
  solver->assertion_queue.prop_ptr = top->assertion_ptr;

  /*
   * If bstack->fix_ptr < bstack->top, we must now revisit
   * all bounds in bstack[fix_ptr ... top-1] and clear the
   * lb/ub tags of variables.
   */
  roll_back_fix_ptr(solver);

  // remove trail object
  arith_trail_pop(&solver->trail_stack);

  if (solver->tableau_ready) {
    // delete the tableau
    simplex_reset_tableau(solver);
  } else if (solver->matrix_ready) {
    // push/pop called without check
    // remove dead rows and columns
    nrows = solver->saved_rows.size + num_active_vars(&solver->vtbl);
    ncolumns = num_arith_vars(&solver->vtbl);
    matrix_shrink(&solver->matrix, nrows, ncolumns);
  }

  // cleanup the relevant marks of deleted variables
  // reset propagation pointer in eqprop
  if (solver->eqprop != NULL) {
    simplex_eqprop_cleanup(solver);
  }
}


/*
 * Reset to the empty solver
 */
void simplex_reset(simplex_solver_t *solver) {
  uint32_t n;

  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;
  solver->interrupted = false;

  solver->prng = SPLX_PRNG_SEED;

  reset_simplex_statistics(&solver->stats);

  n = solver->vtbl.nvars;
  if (solver->value != NULL) {
    free_rational_array(solver->value, n);
    solver->value = NULL;
  }
  q_clear(&solver->epsilon);
  q_clear(&solver->factor);
  solver->dprng = DPRNG_DEFAULT_SEED;

  reset_arith_atomtable(&solver->atbl);
  reset_arith_vartable(&solver->vtbl);

  reset_matrix(&solver->matrix);
  solver->tableau_ready = false;
  solver->matrix_ready = true;

  solver->last_conflict_row = -1;
  solver->recheck = false;
  solver->integer_solving = false;
  solver->enable_dfeas = false;

  if (solver->dsolver != NULL) {
    reset_dsolver(solver->dsolver);
  }

  if (solver->cache != NULL) {
    reset_cache(solver->cache);
  }

  if (solver->eqprop != NULL) {
    simplex_reset_eqprop(solver);
  }

  if (solver->propagator != NULL) {
    simplex_reset_propagator(solver);
  }

  reset_int_heap(&solver->infeasible_vars);
  reset_arith_bstack(&solver->bstack);
  reset_arith_astack(&solver->assertion_queue);
  reset_eassertion_queue(&solver->egraph_queue);
  reset_arith_undo_stack(&solver->stack);

  reset_arith_trail(&solver->trail_stack);
  delete_saved_rows(&solver->saved_rows, 0);

  reset_elim_matrix(&solver->elim);
  reset_fvar_vector(&solver->fvars);

  reset_poly_buffer(&solver->buffer);
  q_clear(&solver->constant);
  q_clear(&solver->aux);
  q_clear(&solver->gcd);
  xq_clear(&solver->bound);
  xq_clear(&solver->delta);
  xq_clear(&solver->xq0);

  ivector_reset(&solver->expl_vector);
  ivector_reset(&solver->expl_queue);
  ivector_reset(&solver->expl_aux);

  ivector_reset(&solver->aux_vector);
  ivector_reset(&solver->aux_vector2);
  ivector_reset(&solver->rows_to_process);

  // empty arena
  arena_reset(&solver->arena);

  // add the constant
  simplex_create_constant(solver);

  // push undo record for level 0
  arith_push_undo_record(&solver->stack, 0, 0);
}




/*****************
 *  ASSERT ATOM  *
 ****************/

/*
 * Assertion from the core:
 * - a = simplex atom index (packed into a void* pointer)
 * - l = literal pos(x) or neg(x) where x = boolean variable for x
 * - if l == pos(x) then a must be asserted true
 * - if l == neg(x) then a must be asserted false
 *
 * We skip a if the solver already knows that a is assigned. Otherwise,
 * we just add the corresponding assertion code to the assertion queue.
 */
bool simplex_assert_atom(simplex_solver_t *solver, void *a, literal_t l) {
  int32_t id;

  id = arithatom_tagged_ptr2idx(a);
  assert(boolvar_of_atom(arith_atom(&solver->atbl, id)) == var_of(l));

  if (arith_atom_is_unmarked(&solver->atbl, id)) {
    push_assertion(&solver->assertion_queue, mk_assertion(id, sign_of(l)));
    mark_arith_atom(&solver->atbl, id);

#if TRACE
    printf("---> added atom[%"PRId32"]: ", id);
    print_simplex_atom(stdout, solver, id);
    if (is_pos(l)) {
      printf("  (p!%"PRId32" is true)\n", var_of(l));
    } else {
      printf("  (p!%"PRId32" is false)\n", var_of(l));
    }
  } else {
    printf("---> skipped atom[%"PRId32"]: ", id);
    print_simplex_atom(stdout, solver, id);
    if (is_pos(l)) {
      printf("  (true)\n");
    } else {
      printf("  (false)\n");
    }
#endif
  }

  return true;
}





/*************************
 *  THEORY EXPLANATIONS  *
 ************************/

/*
 * Expand a propagation object into a conjunction of literals
 * - expl is a pointer to a propagation object in solver->arena
 *
 * NOTE: the old APROP_EGRAPH_DISEQ is not used anymore,
 */
void simplex_expand_explanation(simplex_solver_t *solver, literal_t l, aprop_header_t *expl, ivector_t *v) {
  assert(expl->tag == APROP_BOUND);
  simplex_explain_bound(solver, ((aprop_t *) expl)->bound, v);
}




/*************************
 *  SPLITTING HEURISTIC  *
 ************************/

/*
 * Evaluate atom in the current assignment
 */
static bool simplex_eval_atom(simplex_solver_t *solver, arith_atom_t *atom) {
  thvar_t x;
  bool b;

  b = false;   // prevents a GCC warning
  x = var_of_atom(atom);
  switch (tag_of_atom(atom)) {
  case GE_ATM:
    b = xq_ge_q(arith_var_value(&solver->vtbl, x), bound_of_atom(atom));
    break;
  case LE_ATM:
    b = xq_le_q(arith_var_value(&solver->vtbl, x), bound_of_atom(atom));
    break;
  case EQ_ATM:
    b = xq_eq_q(arith_var_value(&solver->vtbl, x), bound_of_atom(atom));
    break;
  }

#if TRACE && ! DEBUG
  printf("---> atom: ");
  print_simplex_atom(stdout, solver, arith_atom_id(&solver->atbl, atom));
  if (b) {
    printf(" is true\n");
  } else {
    printf(" is false\n");
  }
#endif

  return b;
}


/*
 * Return l or (not l)
 * - a = atom attached to l = simplex atom index packed in a void* pointer
 */
literal_t simplex_select_polarity(simplex_solver_t *solver, void *a, literal_t l) {
  arith_atom_t *atom;
  int32_t id;
  bvar_t v;

  id = arithatom_tagged_ptr2idx(a);
  atom = arith_atom(&solver->atbl, id);
  v = var_of(l);

  if (v == solver->last_branch_atom && drand(&solver->dprng) > 0.1) {
    // for a branch & bound atom
    // we branch the opposite of the model
    solver->last_branch_atom = null_bvar;
    if (simplex_eval_atom(solver, atom)) {
      return neg_lit(v);
    } else {
      return pos_lit(v);
    }
  }

  if (simplex_eval_atom(solver, atom)) {
    return pos_lit(v);
  } else {
    return neg_lit(v);
  }
}



/*
 * Select polarity when branching on an egraph equality
 * - l is attached to an egraph atom (eq u1 u2)
 * - x1 and x2 are the theory variables for u1 and u2, respectively
 * - return l if (x1 == x2) in the current assignment
 *   return (not l) otherwise
 */
literal_t simplex_select_eq_polarity(simplex_solver_t *solver, thvar_t x1, thvar_t x2, literal_t l) {
  if (xq_eq(arith_var_value(&solver->vtbl, x1), arith_var_value(&solver->vtbl, x2))) {
    return l;
  } else {
    return not(l);
  }
}




/**********************
 * DELETE THE SOLVER  *
 *********************/

void delete_simplex_solver(simplex_solver_t *solver) {
  uint32_t n;

  n = solver->vtbl.nvars;
  if (solver->value != NULL) {
    free_rational_array(solver->value, n);
    solver->value = NULL;
  }
  q_clear(&solver->epsilon);
  q_clear(&solver->factor);

  delete_arith_atomtable(&solver->atbl);
  delete_arith_vartable(&solver->vtbl);

  if (solver->eqprop != NULL) {
    simplex_delete_eqprop(solver);
  }

  if (solver->propagator != NULL) {
    simplex_delete_propagator(solver);
  }

  if (solver->dsolver != NULL) {
    delete_dsolver(solver->dsolver);
    safe_free(solver->dsolver);
    solver->dsolver = NULL;
  }

  if (solver->cache != NULL) {
    delete_cache(solver->cache);
    safe_free(solver->cache);
    solver->cache = NULL;
  }

  delete_matrix(&solver->matrix);
  delete_int_heap(&solver->infeasible_vars);
  delete_arith_bstack(&solver->bstack);
  delete_arith_astack(&solver->assertion_queue);
  delete_eassertion_queue(&solver->egraph_queue);
  delete_arith_undo_stack(&solver->stack);

  delete_arith_trail(&solver->trail_stack);
  delete_saved_rows(&solver->saved_rows, 0);
  delete_pvector(&solver->saved_rows);

  delete_elim_matrix(&solver->elim);
  delete_fvar_vector(&solver->fvars);

  delete_poly_buffer(&solver->buffer);
  q_clear(&solver->constant);
  q_clear(&solver->aux);
  q_clear(&solver->gcd);
  xq_clear(&solver->bound);
  xq_clear(&solver->delta);
  xq_clear(&solver->xq0);

  delete_ivector(&solver->expl_vector);
  delete_ivector(&solver->expl_queue);
  delete_ivector(&solver->expl_aux);
  delete_ivector(&solver->aux_vector);
  delete_ivector(&solver->aux_vector2);
  delete_ivector(&solver->rows_to_process);

  delete_arena(&solver->arena);
}






/*********************************
 *   INTERFACE WITH THE EGRAPH   *
 ********************************/

/*
 * Save egraph assertions in the assertion queue
 * - x1 and x2: become equal after the egraph merge two classes c1 and c2
 *   such that thvar[c1] = x1 and thvar[c2] = x2
 * - id = index of the egraph edge that caused c1 and c2 to be merged
 */
void simplex_assert_var_eq(simplex_solver_t *solver, thvar_t x1, thvar_t x2, int32_t id) {
  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2));
  eassertion_push_eq(&solver->egraph_queue, x1, x2, id);

#if TRACE
  printf("\n---> Simplex: received egraph equality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" = ");
  print_simplex_var(stdout, solver, x2);
  printf("\n---> ");
  print_simplex_vardef(stdout, solver, x1);
  printf("---> ");
  print_simplex_vardef(stdout, solver, x2);
  printf("---> eterm[");
  print_simplex_var(stdout, solver, x1);
  printf("] = g!%"PRId32"\n", arith_var_get_eterm(&solver->vtbl, x1));
  printf("---> eterm[");
  print_simplex_var(stdout, solver, x2);
  printf("] = g!%"PRId32"\n", arith_var_get_eterm(&solver->vtbl, x2));
#endif
}

void simplex_assert_var_diseq(simplex_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint) {
  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2));
  eassertion_push_diseq(&solver->egraph_queue, x1, x2, hint);

#if TRACE
  printf("---> Simplex: received egraph disequality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" != ");
  print_simplex_var(stdout, solver, x2);
  printf("\n---> ");
  print_simplex_vardef(stdout, solver, x1);
  printf("---> ");
  print_simplex_vardef(stdout, solver, x2);
#endif
}

void simplex_assert_var_distinct(simplex_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
#ifndef NDEBUG
  uint32_t i;
  for (i=0; i<n; i++) {
    assert(arith_var_has_eterm(&solver->vtbl, a[i]));
  }
#endif

  eassertion_push_distinct(&solver->egraph_queue, n, a, hint);
}


/*
 * Check whether x1 and x2 are distinct at the base level
 */
bool simplex_check_disequality(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  poly_buffer_t *b;
  bool diseq;

  assert(valid_arith_var(&solver->vtbl, x1) && valid_arith_var(&solver->vtbl, x2));

  b = &solver->buffer;
  assert(poly_buffer_nterms(b) == 0);
  add_var_or_subst(solver, b, x1);
  sub_var_or_subst(solver, b, x2);
  normalize_poly_buffer(b);

  diseq = poly_buffer_is_nzconstant(b);
  reset_poly_buffer(b);

  return diseq;
}


/*
 * Check whether x is a constant
 */
bool simplex_var_is_constant(simplex_solver_t *solver, thvar_t x) {
  polynomial_t *q;

  if (x == const_idx) {
    return true;
  }
  q = arith_var_def(&solver->vtbl, x);
  return q != NULL && polynomial_is_constant(q);
}




/*
 * MODEL PREPARATION FOR RECONCILE MODEL
 */

/*
 * Support for build model: evaluate polynomial p in the current assignment.
 * - store the result in q
 */
static void simplex_eval_poly(simplex_solver_t *solver, polynomial_t *p, xrational_t *q) {
  uint32_t i, n;
  thvar_t x;

  xq_clear(q);
  n = p->nterms;
  for (i=0; i<n; i++) {
    x = p->mono[i].var;
    if (x == const_idx) {
      xq_add_q(q, &p->mono[i].coeff);
    } else {
      assert(! trivial_variable(&solver->vtbl, x));
      xq_addmul(q, arith_var_value(&solver->vtbl, x), &p->mono[i].coeff);
    }
  }
}


/*
 * Build model: compute the value of trivial variables
 * - for a trivial variable x, we have x := p where p is a simple polynomial
 * - p is either a constant k or (a.y) or (k + a.y) where y is not a trivial
 *   variable so the value of y is known.
 * - if x is a trivial variable and has an eterm attached, then its value is
 *   important
 */
static void simplex_prepare_model(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  polynomial_t *p;
  uint32_t i, n;

  assert(simplex_assignment_integer_valid(solver));
#if DEBUG
  check_assignment(solver);
  check_integer_bounds(solver);
  check_vartags(solver);
  check_bound_marks(solver);
#endif

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) { // skip const_idx
    p = arith_var_def(vtbl, i);
    if (p != NULL && simple_poly(p)) {
      assert(trivial_variable(vtbl, i));
      // i is a trivial variable: compute its value = evaluate p
      simplex_eval_poly(solver, p, arith_var_value(vtbl, i));
    }
  }
}



/*
 * Check whether x1 and x2 are equal in the model
 */
static bool simplex_var_equal_in_model(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  xrational_t *v1, *v2;

  v1 = arith_var_value(&solver->vtbl, x1);
  v2 = arith_var_value(&solver->vtbl, x2);
  return xq_eq(v1, v2);
}



/*
 * Hash function used in the integer partition used below
 * - x and y match if they have the same value in the model
 */
static uint32_t simplex_model_hash(simplex_solver_t *solver, thvar_t x) {
  xrational_t *vx;
  uint32_t a, b, c, d;

  vx = arith_var_value(&solver->vtbl, x);
  q_hash_decompose(&vx->main, &a, &b);
  q_hash_decompose(&vx->delta, &c, &d);
  return jenkins_hash_quad(a, b, c, d, 0xab2eaf25);
}


/*
 * Check whether x is a root variable:
 * - x is root if it has an egraph term t and x is the theory
 *   variable in the class of t.
 */
static bool is_root_var(simplex_solver_t *solver, thvar_t x) {
  egraph_t *egraph;
  eterm_t t;

  t = arith_var_get_eterm(&solver->vtbl, x);
  egraph = solver->egraph;
  return (t != null_eterm) &&
    (egraph_class_thvar(egraph, egraph_term_class(egraph, t)) == x);
}



/*
 * MODEL ADJUSTMENT
 */

/*
 * Check whether x is a non-constant, trivial variable
 * - i.e. x's definition is either x := b y or x := a + b y
 */
static bool simple_dependent_var(arith_vartable_t *tbl, thvar_t x) {
  polynomial_t *q;
  uint32_t n;

  assert(arith_var_kind(tbl, x) == AVAR_FREE ||
         arith_var_kind(tbl, x) == AVAR_POLY);

  q = arith_var_def(tbl, x);
  if (q != NULL) {
    n = q->nterms;
    return (n == 1 && q->mono[0].var != const_idx) // q is b.y
      || (n == 2 && q->mono[0].var == const_idx);  // q is a + b.y
  }
  return false;
}


/*
 * Get the monomial b.y in x's definition
 * - x must be a simple dependent variable
 */
static monomial_t *simple_depvar_mono(arith_vartable_t *tbl, thvar_t x) {
  polynomial_t *q;

  assert(simple_dependent_var(tbl, x));

  q = arith_var_poly_def(tbl, x);
  return q->mono + (q->nterms - 1); // b.y is the last monomial of q
}


/*
 * Get the variable y in the definition of x
 * - x must be a simple dependent variable
 */
static thvar_t simple_depvar_source(arith_vartable_t *tbl, thvar_t x) {
  return simple_depvar_mono(tbl, x)->var;
}


/*
 * Get the coefficient b in x's definition
 * - x must be a simple dependent variable
 */
static rational_t *simple_depvar_coeff(arith_vartable_t *tbl, thvar_t x) {
  return &simple_depvar_mono(tbl, x)->coeff;
}


/*
 * Given a trivial variable x := a + b y.
 * record the dependency y --> x into dtbl
 */
static void record_simple_var_dep(arith_vartable_t *tbl, dep_table_t *dep, thvar_t x) {
  thvar_t y;

  y = simple_depvar_source(tbl, x);
  add_dependent(dep, y, x); // add x as a dependent of y
}


/*
 * Update the value of x: add delta to it
 * - x must be a root variable
 * - record the effect in hmap
 */
static void model_adjust_var(xq_hmap_t *hmap, arith_vartable_t *tbl, thvar_t x, rational_t *delta) {
  xq_hmap_shift_entry(hmap, arith_var_value(tbl, x), delta);
}


/*
 * Update the value of x's dependents when x's value is shifted by delta
 * - record the effect in hmap
 */
static void model_adjust_var_dependents(xq_hmap_t *hmap, arith_vartable_t *tbl, dep_table_t *deps,
                                        thvar_t x, rational_t *delta) {
  int32_t *v;
  uint32_t i, n;
  thvar_t y;

  v = get_dependents(deps, x);
  if (v != NULL) {
    n = iv_size(v);
    for (i=0; i<n; i++) {
      y = v[i]; // y depends on x
      assert(simple_depvar_source(tbl, y) == x);
      xq_hmap_addmul_entry(hmap, arith_var_value(tbl, y), simple_depvar_coeff(tbl, y), delta);
    }
  }
}


/*
 * Update the value of all basic variables that depend on x when x's value is
 * shifted by delta. This is done only for basic variables that are roots (e.g,.
 * they have an attached egraph term and that term is root of its equivalence
 * class in the egraph).
 * - x must be a non-basic variable
 * - record the effect in hmap
 */
static void model_adjust_var_base_dependents(simplex_solver_t *solver, xq_hmap_t *hmap, dep_table_t *deps,
                                             thvar_t x, rational_t *delta) {
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  column_t *col;
  rational_t a;
  uint32_t i, n;
  int32_t r, j;
  thvar_t y;

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  assert(matrix_is_nonbasic_var(matrix, x));

  col = matrix_column(matrix, x);

  if (col != NULL) {
    q_init(&a);

    n = col->size;
    for (i=0; i<n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0) {
        // x occurs in row r
        y = matrix_basic_var(matrix, r); // y = basic variable for row r
        assert(y != null_thvar);
        if (is_root_var(solver, y)) {
          /*
           * Adjust y:
           * - let c be the coefficient of x in row r
           * - the row is (y + .... + c.x + ... = 0)
           * - so new_val[y] must be val[y] - c * delta
           */
          j = col->data[i].r_ptr;
          q_set_neg(&a, matrix_coeff(matrix, r, j)); // - c
          q_mul(&a, delta);  // -c * delta

          model_adjust_var(hmap, vtbl, y, &a); // Update y
          model_adjust_var_dependents(hmap, vtbl, deps, y, &a); // Update y's dependents
        }
      }
    }

    q_clear(&a);
  }
}


/*
 * Full adjustment for variable x:
 * - adjust x itself if it's a root variable
 * - adjust x's dependents
 * - adjust all the basic variables that depend on x
 *
 * x must not be a basic variable
 */
static void simplex_full_adjust_var(simplex_solver_t *solver, xq_hmap_t *hmap, dep_table_t *deps,
                                    thvar_t x, rational_t *delta) {
  if (is_root_var(solver, x)) {
    model_adjust_var(hmap, &solver->vtbl, x, delta);
  }
  model_adjust_var_dependents(hmap, &solver->vtbl, deps, x, delta);
  model_adjust_var_base_dependents(solver, hmap, deps, x, delta);
}


/*
 * Check whether adjusting x can make a difference:
 * - i.e., x or one of its dependent variables is a root variable
 */
static bool simplex_useful_adjust_var(simplex_solver_t *solver, dep_table_t *deps, thvar_t x) {
  matrix_t *matrix;
  column_t *col;
  uint32_t i, n;
  int32_t r;

  if (is_root_var(solver, x) || get_dependents(deps, x) != NULL) {
    return true;
  }

  matrix = &solver->matrix;
  col = matrix_column(matrix, x);
  if (col != NULL) {
    n = col->size;
    for (i=0; i<n; i++) {
      r  = col->data[i].r_idx;
      if (r >= 0 && is_root_var(solver, matrix_basic_var(matrix, r))) {
        // the basic variable in row r is root
        return true;
      }
    }
  }

  return false;
}


/*
 * Compute the safe delta interval for x
 * - x must be a non-basic variable
 * - store the result in s
 */
static void simplex_safe_adjust_interval(simplex_solver_t *solver, interval_t *s, thvar_t x) {
  xrational_t aux;
  rational_t inv_a;
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  column_t *col;
  uint32_t i, n;
  int32_t r, j;
  thvar_t y;

  vtbl = &solver->vtbl;
  matrix = &solver->matrix;

  assert(matrix_is_nonbasic_var(matrix, x));

  xq_init(&aux);


  /*
   * Initialize s using the bounds on x
   */
  reset_interval(s);
  j = arith_var_lower_index(vtbl, x);
  if (j >= 0) {
    /*
     * x has a lower bound L:
     * to ensure x + delta >= L, we want delta >= L - val[x]
     */
    xq_set(&aux, &solver->bstack.bound[j]);
    xq_sub(&aux, arith_var_value(vtbl, x));
    interval_update_lb(s, &aux);
  }

  j = arith_var_upper_index(vtbl, x);
  if (j >= 0) {
    /*
     * we want delta <= U - val[x]
     */
    xq_set(&aux, &solver->bstack.bound[j]);
    xq_sub(&aux, arith_var_value(vtbl, x));
    interval_update_ub(s, &aux);
  }

  if (arith_var_is_int(vtbl, x)) {
    // delta must be an integer
    q_set_one(&s->period);
  }


  /*
   * Check the bounds on all variables that depend on x
   */
  col = matrix_column(matrix, x);
  if (col != NULL) {
    q_init(&inv_a);

    n = col->size;
    for (i=0; i<n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0) {
        /*
         * x occurs in row r with coefficient a (a != 0)
         * store 1/a in inv_a
         */
        j = col->data[i].r_ptr;
        q_set(&inv_a, matrix_coeff(matrix, r, j)); // coefficient of x in row r
        assert(q_is_nonzero(&inv_a));
        q_inv(&inv_a);

        y = matrix_basic_var(matrix, r); // basic variable in row r
        assert(y != x);

        /*
         * Update the interval using the bounds on y + the type of y:
         * when val[x] is moved to val[x] + delta
         *      val[y] shifts to val[y] - a * delta
         */
        j = arith_var_lower_index(vtbl, y);
        if (j >= 0) {
          /*
           * y has a lower bound L:
           * if a > 0, we want delta <= (val[y] - L)/a
           * if a < 0, we want delta >= (val[y] - L)/a
           */
          xq_set(&aux, arith_var_value(vtbl, y));
          xq_sub(&aux, &solver->bstack.bound[j]);
          xq_mul(&aux, &inv_a);   // aux := (val[y] - L)/a
          if (q_is_pos(&inv_a)) {
            interval_update_ub(s, &aux);
          } else {
            interval_update_lb(s, &aux);
          }
        }

        j = arith_var_upper_index(vtbl, y);
        if (j >= 0) {
          /*
           * y has an upper bound U:
           * if a > 0, we want delta >= (val[y] - U)/a
           * if a < 0, we want delta <= (val[y] - U)/a
           */
          xq_set(&aux, arith_var_value(vtbl, y));
          xq_sub(&aux, &solver->bstack.bound[j]);
          xq_mul(&aux, &inv_a);   // aux := (val[y] - U)/a
          if (q_is_pos(&inv_a)) {
            interval_update_lb(s, &aux);
          } else {
            interval_update_ub(s, &aux);
          }
        }

        if (arith_var_is_int(vtbl, y)) {
          /*
           * We want a * delta to be an integer so
           * delta must be a multiple of 1/a
           */
          interval_update_period(s, &inv_a);
        }
      }
    }

    q_clear(&inv_a);
  }

  xq_clear(&aux);
}



/*
 * Update the value of all trivial variables in deps[x]
 * - delta = shift on x
 */
static void simplex_shift_var_dependents(arith_vartable_t *tbl, dep_table_t *deps, thvar_t x, rational_t *delta) {
  int32_t *v;
  uint32_t i, n;
  thvar_t y;

  v = get_dependents(deps, x);
  if (v != NULL) {
    n = iv_size(v);
    for (i=0; i<n; i++) {
      y = v[i];
      assert(simple_depvar_source(tbl, y) == x);
      xq_addmul_q(arith_var_value(tbl, y), simple_depvar_coeff(tbl, y), delta);
    }
  }
}


/*
 * Shift the value of x by delta and propagate to all dependent variables
 * - this modifies the variable assignments in vartable
 *
 * NOTE: this does not update the values of trivial variables that
 * depend on x but are not in x's dependent vectors.
 */
static void simplex_shift_var_value(simplex_solver_t *solver, dep_table_t *deps, thvar_t x, rational_t *delta) {
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  column_t *col;
  rational_t a;
  uint32_t i, n;
  int32_t r, j;
  thvar_t y;

  vtbl = &solver->vtbl;

  xq_add_q(arith_var_value(vtbl, x), delta); // value[x] := value[x] + delta
  simplex_set_bound_flags(solver, x);

  assert(value_satisfies_bounds(solver, x));

  simplex_shift_var_dependents(vtbl, deps, x, delta); // simple dependents

  matrix = &solver->matrix;
  col = matrix_column(matrix, x);
  if (col != NULL) {
    q_init(&a);

    n = col->size;
    for (i=0; i<n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0) {
        y = matrix_basic_var(matrix, r);   // y = basic var in row r
        assert(y != null_thvar);

        // delta on y = - delta * coeff of x in row r
        j = col->data[i].r_ptr;
        q_set_neg(&a, matrix_coeff(matrix, r, j));
        q_mul(&a, delta);

        // value[y] := value[y] + delta on y
        xq_add_q(arith_var_value(vtbl, y), &a);
        assert(value_satisfies_bounds(solver, y));

#if DEBUG
        check_equation_satisfied(solver, r);
#endif
        simplex_shift_var_dependents(vtbl, deps, y, &a); // shift y's dependents
      }
    }
  }
}



/*
 * Parameter used by the candidate selection heuristics below:
 * - max number of candidates to try
 */
#define MAX_SHIFT_CANDIDATES 5


/*
 * Select a possible delta in the specified interval
 * - i = selection index (i.e., the function must return a sequence
 *   of distinct delta_i with indices i=0, 1, 2, ...)
 * - prng = state of a pseudo random number generator (cf. dprng.h)
 * - return value = true if delta_i exists (then its value is stored in delta)
 * - return false otherwise.
 */
static bool simplex_get_shift_candidate(rational_t *delta, double *prng, interval_t *interval, uint32_t i) {
  int64_t w;
  int32_t k;

  w = (int64_t) interval->k_max - (int64_t) interval->k_min;
  if (w <= MAX_SHIFT_CANDIDATES + 1) {
    k = i;
    k += interval->k_min;
    if (k > interval->k_max) return false;
  } else if (w < 1000 * MAX_SHIFT_CANDIDATES) {
    k = irand(prng, w);
    k += interval->k_min;
  } else {
    k = irand(prng, 1000 * MAX_SHIFT_CANDIDATES);
    if (interval->k_min > -500 * MAX_SHIFT_CANDIDATES) {
      k += interval->k_min;
    } else if (interval->k_max < 500 * MAX_SHIFT_CANDIDATES) {
      k = interval->k_max - k;
    } else {
      k -= 500 * MAX_SHIFT_CANDIDATES;
    }
  }

  assert(interval->k_min <= k && k <= interval->k_max);
  q_set32(delta, k);
  q_mul(delta, &interval->period);

  return !interval->has_ub || xq_ge_q(&interval->ub, delta);
}



/*
 * Compute the best adjustment for variable x:
 * - deps = dependency table
 * - hmap = partition for the current variable assignment
 * - aux = auxiliary hmap for computations
 * - interval = adjustment interval for x
 */
static void simplex_adjust_var(simplex_solver_t *solver, dep_table_t *deps, xq_hmap_t *hmap, xq_hmap_t *aux,
                               interval_t *interval, thvar_t x) {
  rational_t delta;
  rational_t best_delta;
  uint32_t best_num_classes;
  uint32_t i, n;

  q_init(&best_delta);
  q_init(&delta);
  best_num_classes = xq_hmap_num_classes(hmap);

  interval_prepare_for_sampling(interval, MAX_SHIFT_CANDIDATES);

  /*
   * Search for delta := shift of x's value that maximizes
   * the number of classes in xq_hmap
   */
  for (i=0; i<MAX_SHIFT_CANDIDATES; i++) { // try at most 5 candidates
    if (! simplex_get_shift_candidate(&delta, &solver->dprng, interval, i)) break;

    assert(sample_in_interval(interval, &delta));

    if (! q_is_zero(&delta)) {
      // aux := the new partition for this delta
      copy_xq_hmap(aux, hmap);
      simplex_full_adjust_var(solver, aux, deps, x, &delta);
      n = xq_hmap_num_classes(aux);

#if TRACE
      printf("    delta = ");
      q_print(stdout, &delta);
      printf(": %"PRIu32" classes\n", n);
#endif

      assert(xq_hmap_num_entries(aux) == xq_hmap_num_entries(hmap));

      if (n > best_num_classes) {
        q_set(&best_delta, &delta);
        best_num_classes = n;
        if (n == xq_hmap_num_entries(aux)) {
          // n is optimal
          break;
        }
      }
    }
  }

  /*
   * Apply the best shift to the current model and
   * to hmap.
   */
  if (! q_is_zero(&best_delta)) {
#if TRACE
    printf("    adjustment: delta = ");
    q_print(stdout, &best_delta);
    printf(": %"PRIu32" classes\n", best_num_classes);
#endif
    // We must adjust hmap first
    simplex_full_adjust_var(solver, hmap, deps, x, &best_delta);
    assert(xq_hmap_num_classes(hmap) == best_num_classes);

    // shift x and update its dependents
    simplex_shift_var_value(solver, deps, x, &best_delta);
  }

  q_clear(&delta);
  q_clear(&best_delta);
}



/*
 * Attempt to modify the current assignment
 * - deps = dependency table
 * - hmap = current partition table
 */
static void simplex_adjust_assignment(simplex_solver_t *solver, dep_table_t *deps, xq_hmap_t *hmap) {
  interval_t interval;
  xq_hmap_t aux;
  uint32_t i, n;

#if DEBUG
  check_assignment(solver);
  check_integer_bounds(solver);
  check_vartags(solver);
  check_bound_marks(solver);
#endif

  init_xq_hmap(&aux, 0);
  init_interval(&interval);

  n = solver->vtbl.nvars;
  for (i=1; i<n; i++) {
    /*
     * Skip all the dependent variables (i.e.. basic variable
     * and trivial variables) and all variables that have
     * equal lower and upper bounds.
     */
    if (matrix_is_nonbasic_var(&solver->matrix, i) &&
        !trivial_variable(&solver->vtbl, i) &&
        !simplex_fixed_variable(solver, i) &&
        simplex_useful_adjust_var(solver, deps, i)) {

      // compute the safe interval for i
      simplex_safe_adjust_interval(solver, &interval, i);
      if (! singleton_interval(&interval)) {
        /*
         * Modify the value of x to maximize the number of classes in hmap
         */
#if TRACE
        printf("interval for ");
        print_simplex_var(stdout, solver, i);
        if (interval.has_lb) {
          printf(": lower bound = ");
          xq_print(stdout, &interval.lb);
        } else {
          printf(": no lower bound");
        }

        if (interval.has_ub) {
          printf(", upper bound = ");
          xq_print(stdout, &interval.ub);
        } else {
          printf(", no upper bound");
        }

        printf(", period = ");
        q_print(stdout, &interval.period);
        printf("\n");
#endif

        simplex_adjust_var(solver, deps, hmap, &aux, &interval, i);

#if DEBUG
        check_assignment(solver);
        check_integer_bounds(solver);
        check_vartags(solver);
        check_bound_marks(solver);
#endif

        if (xq_hmap_num_classes(hmap) == xq_hmap_num_entries(hmap)) {
          // no improvement possible
          break;
        }
      }
    }
  }

  delete_interval(&interval);
  delete_xq_hmap(&aux);
}


/*
 * Attempt to modify the current model to minimize the number of
 * conflicts with the egraph classes.
 */
static void simplex_adjust_model(simplex_solver_t *solver) {
  xq_hmap_t hmap;
  dep_table_t deps;
  arith_vartable_t *vtbl;
  uint32_t i, n;

  init_xq_hmap(&hmap, 0);
  init_dep_table(&deps, 0);

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (is_root_var(solver, i)) {
      xq_hmap_add_entry(&hmap, arith_var_value(vtbl, i));
      if (simple_dependent_var(vtbl, i)) {
        record_simple_var_dep(vtbl, &deps, i);
      }
    }
  }

  if (xq_hmap_num_classes(&hmap) < xq_hmap_num_entries(&hmap)) {
#if TRACE
    printf("---> before adjustment: %"PRIu32" entries, %"PRIu32" classes\n",
           xq_hmap_num_entries(&hmap), xq_hmap_num_classes(&hmap));
#endif
    simplex_adjust_assignment(solver, &deps, &hmap);
#if TRACE
    printf("---> after adjustment: %"PRIu32" entries, %"PRIu32" classes\n",
           xq_hmap_num_entries(&hmap), xq_hmap_num_classes(&hmap));
#endif
  }


  delete_dep_table(&deps);
  delete_xq_hmap(&hmap);
}



/*
 * RECONCILE MODEL
 */

/*
 * Replacement for build_model, var_equal_in_model, and release_model
 * - attempt to build a model that's consistent with the egraph
 * - construct at most max_eq interface equalities if that's not possible
 * - return the number of interface equalities generated
 */
uint32_t simplex_reconcile_model(simplex_solver_t *solver, uint32_t max_eq) {
  int_hclass_t hclass;
  int32_t i, x, n;
  uint32_t neq;

  assert(max_eq > 0);

  simplex_prepare_model(solver);

  if (simplex_option_enabled(solver, SIMPLEX_ADJUST_MODEL)) {
    simplex_adjust_model(solver);
  }


#if TRACE
  printf("SIMPLEX: reconcile model\n");
  print_simplex_vars(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif

  init_int_hclass(&hclass, 0, solver, (iclass_hash_fun_t) simplex_model_hash,
                  (iclass_match_fun_t) simplex_var_equal_in_model);

  neq = 0;
  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (is_root_var(solver, i)) {
      x = int_hclass_get_rep(&hclass, i);
      if (x != i) {
        // x and i have the same value in the model
        // but are in different classes in the egraph
        neq += simplex_trichotomy_lemma(solver, x, i);
        if (neq == max_eq) break;
      }
    }
  }

  delete_int_hclass(&hclass);

#if TRACE
  printf("---> reconcile model: %"PRIu32" trichotomy lemmas\n\n", neq);
#endif

  return neq;
}



/*
 * EXPERIMENTAL: MODEL RECONCILIATION INTERFACE
 */

static void simplex_prep_model(simplex_solver_t *solver) {
  simplex_prepare_model(solver);
  if (simplex_option_enabled(solver, SIMPLEX_ADJUST_MODEL)) {
    simplex_adjust_model(solver);
  }
#if TRACE
  printf("SIMPLEX: prepare model\n");
  print_simplex_vars(stdout, solver);
  printf("\n");
  print_simplex_assignment(stdout, solver);
  printf("\n\n");
  fflush(stdout);
#endif
}

static void simplex_release_model(simplex_solver_t *solver) {
  // nothing to do
}

// var equal in model is already defined

/*
 * Add the lemma l => x1 != x2
 * - if equiv is true, also generate the reverse implication
 */
static void simplex_gen_interface_lemma(simplex_solver_t *solver, literal_t l, thvar_t x1, thvar_t x2, bool equiv) {
  rational_t *c;
  thvar_t y;
  literal_t l0, l1, l2;

  assert(x1 != x2);

  /*
   * build p such that p=0 is equivalent to (x1 = x2)
   * p is stored in solver->buffer
   * l0 = simplification code
   */
  l0 = simplify_dynamic_vareq(solver, x1, x2);
  if (l0 == false_literal) {
    /*
     * x1 = x2 is false: add (not l) as an axiom for the egraph
     */
    add_unit_clause(solver->core, not(l));
    solver->stats.num_reduced_inter_lemmas ++;

#if 0
    printf("---> SIMPLEX: interface lemma for ");
    print_simplex_var(stdout, solver, x1);
    printf(" ");
    print_simplex_var(stdout, solver, x2);
    printf(" (axiom)\n");
#endif

#if TRACE
    printf("---> Simplex: reconciliation lemma for ");
    print_simplex_var(stdout, solver, x1);
    printf(" /= ");
    print_simplex_var(stdout, solver, x2);
    printf(" ----\n");
    if (!arith_var_is_free(&solver->vtbl, x1)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, x1);
    }
    if (!arith_var_is_free(&solver->vtbl, x2)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, x2);
    }
    printf("     Antecedent:\n");
    printf("      ");
    print_literal(stdout, l);
    printf(" := ");
    print_egraph_atom_of_literal(stdout, solver->egraph, l);
    printf("\n");
    printf("     equality is false\n");
    printf("     add unit clause: ");
    print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
    printf("\n");
#endif

  } else {
    assert(l0 != true_literal); // because x1 != x2

    /*
     * get y and c such that (y = c) is equivalent to (x1 = x2)
     */
    y = decompose_and_get_dynamic_var(solver);
    c = &solver->constant;

    l1 = create_pos_atom(solver, y, c); // l1 is (y > c)
    l2 = create_neg_atom(solver, y, c); // l2 is (y < c)

    add_ternary_clause(solver->core, not(l), l1, l2); // clause: (not l) or (y > c) or (y < c))
    if (equiv) {
      add_binary_clause(solver->core, l, not(l1)); // y > c => t1 /= t2
      add_binary_clause(solver->core, l, not(l2)); // y < c => t1 /= t2
    }

    solver->stats.num_interface_lemmas ++;

#if 0
    printf("---> SIMPLEX: interface lemma for ");
    print_simplex_var(stdout, solver, x1);
    printf(" ");
    print_simplex_var(stdout, solver, x2);
    printf(" (trichotomy)\n");
#endif


#if TRACE
    printf("---> Simplex: reconciliation lemma for ");
    print_simplex_var(stdout, solver, x1);
    printf(" /= ");
    print_simplex_var(stdout, solver, x2);
    printf(" ----\n");
    if (!arith_var_is_free(&solver->vtbl, x1)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, x1);
    }
    if (!arith_var_is_free(&solver->vtbl, x2)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, x2);
    }
    printf("     Antecedent:\n");
    printf("      ");
    print_literal(stdout, l);
    printf(" := ");
    print_egraph_atom_of_literal(stdout, solver->egraph, l);
    printf("\n");
    printf("     Equality is reduced to\n");
    printf("       ");
    print_simplex_var(stdout, solver, y);
    printf(" != ");
    q_print(stdout, c);
    printf("\n");
    if (! arith_var_is_free(&solver->vtbl, y)) {
      printf("     ");
      print_simplex_vardef(stdout, solver, y);
    }
    printf("     simplex atom:\n      ");
    print_literal(stdout, l1);
    printf(" := ");
    print_simplex_atom_of_literal(stdout, solver, l1);
    printf("\n      ");
    print_literal(stdout, l2);
    printf(" := ");
    print_simplex_atom_of_literal(stdout, solver, l2);
    printf("\n");
    printf("     add clause: (OR ");
    print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
    printf(" ");
    print_simplex_atom_of_literal(stdout, solver, l1);
    printf(" ");
    print_simplex_atom_of_literal(stdout, solver, l2);
    printf(")\n\n");
#endif

  }

}


/*
 * Build the variable partition for the current model
 */
static ipart_t *simplex_build_model_partition(simplex_solver_t *solver) {
  ipart_t *partition;
  uint32_t i, n;

  partition = (ipart_t *) safe_malloc(sizeof(ipart_t));
  init_int_partition(partition, 0, solver, (ipart_hash_fun_t) simplex_model_hash,
                     (ipart_match_fun_t) simplex_var_equal_in_model);

  n = solver->vtbl.nvars;
  for (i=1; i<n; i++) {
    if (is_root_var(solver, i)) {
      int_partition_add(partition, i);
    }
  }

  return partition;
}


/*
 * Free the partition
 */
static void simplex_release_model_partition(simplex_solver_t *solver, ipart_t *p) {
  delete_int_partition(p);
  safe_free(p);
}





/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * If the egraph is present, then reconcile model ensures that
 * for all variables x_i and x_j, if x_i is attached to egraph term t1,
 * and x_j is attached to egraph term t2, and t1 != t2, then
 * value[x_i] != value[x_j] where the values are extended rationals.
 *
 * We want to preserve this property after value[x_i] and value[x_j]
 * are concretized to rational numbers.
 *
 * If value[x_i] = a_i + b_i \delta  and value[x_j] = a_j + b_j \delta
 * and x_i and x_j are attached to distinct eterms, then we want
 *  (a_i + b_i epsilon) != (a_j + b_j epsilon).
 *
 * It is enough to ensure epsilon < (a_j - a_i)/(b_i - b_j) whenever
 * (a_j > a_i) and (b_i > b_j) and x_i and x_j are attached to egraph terms.
 */

/*
 * Adjust epsilon to ensure concretization of (a1 + b1 \delta) != concretization of (a2 + b2 \delta)
 * - q1 = a1 + b1 \delta
 * - q2 = a2 + b2 \delta
 */
static void epsilon_for_diseq(simplex_solver_t *solver, xrational_t *q1, xrational_t *q2) {
  rational_t *aux, *factor;
  int main_cmp, delta_cmp;

  main_cmp = q_cmp(&q1->main, &q2->main);
  delta_cmp = q_cmp(&q1->delta, &q2->delta);

  if ((main_cmp < 0 && delta_cmp > 0) || (main_cmp > 0 && delta_cmp < 0)) {
    // (a1 < a2) and (b1 > b2)  or  (a1 > a2) and (b1 < b2)
    factor = &solver->factor;
    q_set(factor, &q1->delta);
    q_sub(factor, &q2->delta); // factor = b1 - b2
    aux = &solver->aux;
    q_set(aux, &q2->main);
    q_sub(aux, &q1->main);     // aux = a2 - a1
    q_div(aux, factor);        // aux = (a2 - a1)/(b1 - b2)
    assert(q_is_pos(aux));
    if (q_le(aux, &solver->epsilon)) {
      // force 0 < epsilon < (a2 - a1)/(b1 - b2)
      q_set_int32(factor, 1, 2);
      q_set(&solver->epsilon, aux);
      q_mul(&solver->epsilon, factor);
      assert(q_is_pos(&solver->epsilon) && q_lt(&solver->epsilon, aux));
    }
  }
}


/*
 * Force epsilon < (a_j - a_i)/(b_i - b_j) for all pairs of variables
 * x_i, x_j attached to egraph terms.
 */
static void epsilon_for_egraph(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  xrational_t *q1, *q2;
  uint32_t i, j, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    if (arith_var_has_eterm(vtbl, i)) {
      q1 = arith_var_value(vtbl, i);
      for (j=i+1; j<n; j++) {
        if (arith_var_has_eterm(vtbl, j)) {
          q2 = arith_var_value(vtbl, j);
          epsilon_for_diseq(solver, q1, q2);
        }
      }
    }
  }
}


/*
 * Adjust epsilon to ensure concretization of q1 <= concretization of q2
 * - q1 is a + b \delta  --> concrete rational value = a + b * epsilon
 * - q2 is c + d \delta  --> concrete rational value = c + d * epsilon
 * - epsilon must be positive
 *
 * We assume a + b \delta <= c + d \delta in the extended rationals,
 * that is we have either (a < c) or (a = c and b <= d).
 *
 * To ensure a + b * epsilon <= c + d * epsilon, we need
 *     epsilon <= (c - a)/(b - d) when  b > d.
 * If b <= d, any positive epsilon works (since a <= c).
 */
static void epsilon_for_le(simplex_solver_t *solver, xrational_t *q1, xrational_t *q2) {
  rational_t *aux, *factor;

  assert(xq_le(q1, q2));

  if (q_gt(&q1->delta, &q2->delta)) {
    factor = &solver->factor;
    q_set(factor, &q1->delta);
    q_sub(factor, &q2->delta);  // factor = b - d
    aux = &solver->aux;
    q_set(aux, &q2->main);
    q_sub(aux, &q1->main);      // aux = c - a
    q_div(aux, factor);         // aux = (c - a)/(b - d)
    assert(q_is_pos(aux));
    if (q_lt(aux, &solver->epsilon)) {
      q_set(&solver->epsilon, aux);
    }
  }
}


/*
 * Adjust solver->epsilon to ensure that the rational value of x
 * is between the lower and upper bounds on x
 */
static void simplex_adjust_epsilon(simplex_solver_t *solver, thvar_t x) {
  xrational_t *vx;
  int32_t k;

  vx = arith_var_value(&solver->vtbl, x);
  k = arith_var_lower_index(&solver->vtbl, x);
  if (k >= 0) {
    // ensure lower bound on x <= value of x
    epsilon_for_le(solver, solver->bstack.bound + k, vx);
  }
  k = arith_var_upper_index(&solver->vtbl, x);
  if (k >= 0) {
    // ensure value of x <= upper bound on x
    epsilon_for_le(solver, vx, solver->bstack.bound + k);
  }
}



/*
 * Mark the eliminated variables (i.e., base variables in the elimination matrix)
 */
static void simplex_mark_eliminated_vars(simplex_solver_t *solver, byte_t *mark) {
  elim_matrix_t *elim;
  uint32_t i, n;
  int32_t x;

  elim = &solver->elim;
  n = elim->nrows;
  for (i=0; i<n; i++) {
    x = elim->base_var[i];
    assert(! tst_bit(mark, x) && 0 <= x && x < solver->vtbl.nvars);
    set_bit(mark, x);
  }
}


/*
 * Mark the trivial variables (whose definition in arith table is a simple polynomial).
 */
static void simplex_mark_trivial_vars(simplex_solver_t *solver, byte_t *mark) {
  arith_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    if (trivial_variable(vtbl, i)) {
      assert(! tst_bit(mark, i));
      set_bit(mark, i);
    }
  }
}


/*
 * Mark and set the value of all variables in the fvar vector
 * also set the value of the constant (const_idx = 0 has value 1)
 */
static void simplex_model_for_fvars(simplex_solver_t *solver, byte_t *mark) {
  fvar_vector_t *v;
  uint32_t i, n;
  int32_t x;

  assert(solver->value != NULL);

  v = &solver->fvars;
  n = v->nvars;
  for (i=0; i<n; i++) {
    x = v->fvar[i].var;
    assert(! tst_bit(mark, x) && 0 <= x && x < solver->vtbl.nvars);
    set_bit(mark, x);
    q_set(solver->value + x, &v->fvar[i].value);
  }

  // deal with the constant
  if (! tst_bit(mark, 0)) {
    set_bit(mark, 0);
    q_set_one(solver->value); // i.e., value[0]
  }
  assert(q_is_one(solver->value));
}


/*
 * Compute a rational value for all unmarked variables.
 * - the value for x is a + b * epsilon where (a + b \delta) is
 *   the current simplex assignment for x
 */
static void simplex_model_for_unmarked_vars(simplex_solver_t *solver, byte_t *mark) {
  arith_vartable_t *vtbl;
  rational_t *epsilon, *v;
  xrational_t *vx;
  uint32_t i, n;

  epsilon = &solver->epsilon;
  assert(q_is_pos(epsilon) && solver->value != NULL);

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) { // skip the constant
    if (! tst_bit(mark, i)) {
      vx = arith_var_value(vtbl, i); // vx = a + b\delta
      v = solver->value + i;
      q_set(v, &vx->main);
      q_addmul(v, &vx->delta, epsilon); // v = a  + b * epsilon
    }
  }
}


/*
 * Auxiliary function: compute value of polynomial p
 * - value is an array of rational (value[x] = value of variable x)
 * - the value is stored in v
 */
static void simplex_eval_rational_poly(rational_t *value, polynomial_t *p, rational_t *v) {
  uint32_t i, n;
  thvar_t x;

  assert(value != NULL && p != NULL && q_is_one(&value[0]));

  q_clear(v);
  n = p->nterms;
  for (i=0; i<n; i++) {
    x = p->mono[i].var;
    q_addmul(v, &p->mono[i].coeff, value + x); // v := coeff * value[x]
  }
}


/*
 * Assign a rational value to all eliminated variables
 * - process the elimination matrix in reverse order
 */
static void simplex_model_for_eliminated_vars(simplex_solver_t *solver) {
  elim_matrix_t *elim;
  rational_t *aux;
  uint32_t n;
  int32_t x;

  aux = &solver->aux;
  elim = &solver->elim;
  n = elim->nrows;
  while (n > 0) {
    n --;
    x = elim->base_var[n];
    assert(0 <= x && x < solver->vtbl.nvars);
    /*
     * row[n] is a polynomial p that contains x.
     * x has coefficient 1 in p and we want val[x] to ensure p == 0
     */
    assert(q_is_zero(solver->value + x)); // x should not have been touched
    simplex_eval_rational_poly(solver->value, elim->row[n], aux);
    q_set_neg(solver->value + x, aux);

#ifndef NDEBUG
    simplex_eval_rational_poly(solver->value, elim->row[n], aux);
    assert(q_is_zero(aux));
#endif
  }
}


/*
 * Assign a rational value to all trivial variables.
 */
static void simplex_model_for_trivial_vars(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  polynomial_t *p;
  rational_t *aux;
  uint32_t i, n;

  aux = &solver->aux;
  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=1; i<n; i++) {
    p = arith_var_def(vtbl, i);
    if (p != NULL && simple_poly(p)) {
      assert(trivial_variable(vtbl, i));
      simplex_eval_rational_poly(solver->value, p, aux);
      q_set(solver->value + i, aux);
    }
  }
}



#ifndef NDEBUG

/*
 * DEBUGGING OF MODEL CONSTRUCTION
 */

/*
 * Evaluate a row: store result in *v
 */
static void simplex_eval_rational_row(rational_t *value, row_t *row, rational_t *v) {
  uint32_t i, n;
  thvar_t x;

  q_clear(v);
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      q_addmul(v, value + x, &row->data[i].coeff);
    }
  }
}


/*
 * Evaluate an atom: return true or false
 */
static bool simplex_eval_atom_in_model(rational_t *value, arith_atom_t *atom) {
  thvar_t x;
  bool b;

  b = false;   // prevents GCC warning
  x = var_of_atom(atom);
  switch (tag_of_atom(atom)) {
  case GE_ATM:
    b = q_ge(value + x, bound_of_atom(atom));
    break;
  case LE_ATM:
    b = q_le(value + x, bound_of_atom(atom));
    break;
  case EQ_ATM:
    b = q_eq(value + x, bound_of_atom(atom));
    break;
  }
  return b;
}


/*
 * Check whether the model satisfies all equations in the tableau
 */
static bool equations_hold_in_model(simplex_solver_t *solver) {
  row_t *row;
  rational_t check;
  uint32_t i, n;

  q_init(&check);
  n = solver->matrix.nrows;
  for (i=0; i<n; i++) {
    row = matrix_row(&solver->matrix, i);
    simplex_eval_rational_row(solver->value, row, &check);
    if (q_is_nonzero(&check)) {
      printf("---> BUG: invalid Simplex model: equation not satisfied\n");
      printf("   row[%"PRIu32"]: ", i);
      print_simplex_row(stdout, solver, row);
      printf("\n");
      fflush(stdout);
      return false;
    }
  }

  q_clear(&check);

  return true;
}


/*
 * Check whether the model satisfies all the assertions
 */
static bool assertions_hold_in_model(simplex_solver_t *solver) {
  arith_atomtable_t *atbl;
  arith_atom_t *atom;
  thvar_t x;
  bvar_t v;
  bool truth;
  uint32_t i, n;

  atbl = &solver->atbl;
  n = atbl->natoms;
  for (i=0; i<n; i++) {
    atom = arith_atom(atbl, i);
    v = boolvar_of_atom(atom);
    x = var_of_atom(atom);
    truth = simplex_eval_atom_in_model(solver->value, atom);

    switch (bvar_value(solver->core, v)) {
    case VAL_FALSE:
      if (truth) {
        printf("---> BUG: invalid Simplex model\n");
        print_simplex_atomdef(stdout, solver, v);
        printf("  value[");
        print_bvar(stdout, v);
        printf("] = false\n");
        printf("  value[");
        print_simplex_var(stdout, solver, x);
        printf("] = ");
        q_print(stdout, solver->value + x);
        printf("\n");
        fflush(stdout);

        return false;
      }
      break;
    case VAL_UNDEF_FALSE:
    case VAL_UNDEF_TRUE:
      // should not happen??
      break;
    case VAL_TRUE:
      if (! truth) {
        printf("---> BUG: invalid Simplex model\n");
        print_simplex_atomdef(stdout, solver, v);
        printf("  value[");
        print_bvar(stdout, v);
        printf("] = true\n");
        printf("  value[");
        print_simplex_var(stdout, solver, x);
        printf("] = ");
        q_print(stdout, solver->value + x);
        printf("\n");
        fflush(stdout);
      }
      break;
    }
  }

  return true;
}


/*
 * Check that all integer variables have an integer value
 */
static bool model_is_integer_feasible(simplex_solver_t *solver) {
  arith_vartable_t *vtbl;
  uint32_t i, n;

  vtbl = &solver->vtbl;
  n = vtbl->nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(vtbl, i) && ! q_is_integer(solver->value + i)) {
      printf("---> BUG: invalid Simplex model\n");
      printf("  integer variable ");
      print_simplex_var(stdout, solver, i);
      printf(" does not have an integer value\n");
      printf("  value[");
      print_simplex_var(stdout, solver, i);
      printf("] = ");
      q_print(stdout, solver->value + i);
      printf("\n");
      return false;
    }
  }

  return true;
}


/*
 * Check that the model is consistent with the egraph
 */
static bool model_is_consistent_with_egraph(simplex_solver_t *solver) {
  egraph_t *egraph;
  arith_vartable_t *vtbl;
  uint32_t i, j, n;
  eterm_t t, u;

  egraph = solver->egraph;
  if (egraph != NULL) {
    vtbl = &solver->vtbl;
    n = vtbl->nvars;
    for (i=0; i<n; i++) {
      t = arith_var_get_eterm(vtbl, i);
      if (t != null_eterm) {
        for (j=i+1; j<n; j++) {
          u = arith_var_get_eterm(vtbl, j);
          if (u != null_eterm && !egraph_equal_terms(egraph, t, u)) {
            // t != u in the egraph so we want value[i] != value[j]
            if (q_eq(solver->value + i, solver->value + j)) {
              printf("---> BUG: invalid Simplex model\n");
              printf("The model is not consistent with the egraph\n");
              printf(" ");
              print_simplex_var(stdout, solver, i);
              printf(" is attached to egraph term: ");
              print_eterm_id(stdout, t);
              printf("\n ");
              print_simplex_var(stdout, solver, j);
              printf(" is attached to egraph term: ");
              print_eterm_id(stdout, u);
              printf("\n");

              printf(" value[");
              print_simplex_var(stdout, solver, i);
              printf("] = ");
              q_print(stdout, solver->value + i);
              printf("\n");
              printf(" value[");
              print_simplex_var(stdout, solver, j);
              printf("] = ");
              q_print(stdout, solver->value + j);
              printf("\n");

              printf(" but ");
              print_eterm_id(stdout, t);
              printf(" != ");
              print_eterm_id(stdout, u);
              printf(" in the egraph\n");

              return false;
            }
          }
        }
      }
    }
  }

  return true;
}

/*
 * Check that the model is valid
 */
static bool good_simplex_model(simplex_solver_t *solver) {
  return equations_hold_in_model(solver) && assertions_hold_in_model(solver) &&
    model_is_integer_feasible(solver) && model_is_consistent_with_egraph(solver);
}


#endif



/*
 * Model construction
 */
void simplex_build_model(simplex_solver_t *solver) {
  byte_t *mark;
  uint32_t i, n;

#if DEBUG
  check_assignment(solver);
#endif

  n = solver->vtbl.nvars;
  solver->value = new_rational_array(n);

  /*
   * Deal with fixed, eliminated, trivial variables.
   */
  mark = allocate_bitvector0(n);         // all variables initially unmarked
  simplex_model_for_fvars(solver, mark); // fixed vars have a value and are marked
  simplex_mark_eliminated_vars(solver, mark);
  simplex_mark_trivial_vars(solver, mark);

  /*
   * Compute a safe value for epsilon
   */
  q_set_one(&solver->epsilon); // default positive value
  if (solver->egraph != NULL) {
    // remove epsilon values that would cause a conflict with the egraph model.
    epsilon_for_egraph(solver);
  }
  for (i=1; i<n; i++) {
    if (! tst_bit(mark, i)) {
      simplex_adjust_epsilon(solver, i);
    }
  }

  /*
   * Compute values: for unmarked, eliminated, then trivial variables
   */
  simplex_model_for_unmarked_vars(solver, mark);
  simplex_model_for_eliminated_vars(solver);
  simplex_model_for_trivial_vars(solver);

  delete_bitvector(mark);

  assert(good_simplex_model(solver));
}


/*
 * Free the model
 */
void simplex_free_model(simplex_solver_t *solver) {
  uint32_t n;

  assert(solver->value != NULL);
  n = solver->vtbl.nvars;
  free_rational_array(solver->value, n);
  solver->value = NULL;
  q_clear(&solver->epsilon);
  q_clear(&solver->factor);
}


/*
 * Value of variable x in the model
 */
bool simplex_value_in_model(simplex_solver_t *solver, int32_t x, arithval_in_model_t* res) {
  assert(solver->value != NULL && 0 <= x && x < solver->vtbl.nvars);
  assert(res->tag == ARITHVAL_RATIONAL);
  q_set(&res->val.q, solver->value + x);
  return true;
}



/*
 * Get the type of variable x
 */
bool simplex_var_is_integer(simplex_solver_t *solver, int32_t x) {
  return arith_var_is_int(&solver->vtbl, x);
}



/****************
 *  STATISTICS  *
 ***************/

/*
 * To get end-of-search statistics: set end_rows, end_atoms
 */
void simplex_collect_statistics(simplex_solver_t *solver) {
  solver->stats.num_end_rows = solver->matrix.nrows;
  solver->stats.num_end_atoms = solver->atbl.natoms;
}



/******************************
 *  INTERFACE TO THE CONTEXT  *
 *****************************/


static arith_interface_t simplex_context = {
  (create_arith_var_fun_t) simplex_create_var,
  (create_arith_const_fun_t) simplex_create_const,
  (create_arith_poly_fun_t) simplex_create_poly,
  (create_arith_pprod_fun_t) simplex_create_pprod,
  (create_arith_rdiv_fun_t) simplex_create_rdiv,

  (create_arith_atom_fun_t) simplex_create_eq_atom,
  (create_arith_atom_fun_t) simplex_create_ge_atom,
  (create_arith_patom_fun_t) simplex_create_poly_eq_atom,
  (create_arith_patom_fun_t) simplex_create_poly_ge_atom,
  (create_arith_vareq_atom_fun_t) simplex_create_vareq_atom,

  (assert_arith_axiom_fun_t) simplex_assert_eq_axiom,
  (assert_arith_axiom_fun_t) simplex_assert_ge_axiom,
  (assert_arith_paxiom_fun_t) simplex_assert_poly_eq_axiom,
  (assert_arith_paxiom_fun_t) simplex_assert_poly_ge_axiom,
  (assert_arith_vareq_axiom_fun_t) simplex_assert_vareq_axiom,
  (assert_arith_cond_vareq_axiom_fun_t) simplex_assert_cond_vareq_axiom,
  (assert_arith_clause_vareq_axiom_fun_t) simplex_assert_clause_vareq_axiom,

  (attach_eterm_fun_t) simplex_attach_eterm,
  (eterm_of_var_fun_t) simplex_eterm_of_var,

  (build_model_fun_t) simplex_build_model,
  (free_model_fun_t) simplex_free_model,
  (arith_val_in_model_fun_t) simplex_value_in_model,

  (arith_var_is_int_fun_t) simplex_var_is_integer,
};


/*
 * Return the interface descriptor
 */
arith_interface_t *simplex_arith_interface(simplex_solver_t *solver) {
  return &simplex_context;
}




/********************************
 *  SMT AND CONTROL INTERFACES  *
 *******************************/

static th_ctrl_interface_t simplex_control = {
  (start_intern_fun_t) simplex_start_internalization,
  (start_fun_t) simplex_start_search,
  (propagate_fun_t) simplex_propagate,
  (final_check_fun_t) simplex_final_check,
  (increase_level_fun_t) simplex_increase_decision_level,
  (backtrack_fun_t) simplex_backtrack,
  (push_fun_t) simplex_push,
  (pop_fun_t) simplex_pop,
  (reset_fun_t) simplex_reset,
  (clear_fun_t) simplex_clear,
};

static th_smt_interface_t simplex_smt = {
  (assert_fun_t) simplex_assert_atom,
  (expand_expl_fun_t) simplex_expand_explanation,
  (select_pol_fun_t) simplex_select_polarity,
  NULL,
  NULL,
};


/*
 * Get the control and smt interfaces
 */
th_ctrl_interface_t *simplex_ctrl_interface(simplex_solver_t *solver) {
  return &simplex_control;
}

th_smt_interface_t *simplex_smt_interface(simplex_solver_t *solver) {
  return &simplex_smt;
}





/*********************************************
 *  SATELLITE SOLVER INTERFACE (FOR EGRAPH)  *
 ********************************************/

static th_egraph_interface_t simplex_egraph = {
  (assert_eq_fun_t) simplex_assert_var_eq,
  (assert_diseq_fun_t) simplex_assert_var_diseq,
  (assert_distinct_fun_t) simplex_assert_var_distinct,
  (check_diseq_fun_t) simplex_check_disequality,
  (is_constant_fun_t) simplex_var_is_constant,
  (expand_eq_exp_fun_t) simplex_expand_th_explanation,
  (reconcile_model_fun_t) simplex_reconcile_model,
  (prepare_model_fun_t) simplex_prep_model,
  (equal_in_model_fun_t) simplex_var_equal_in_model,
  (gen_inter_lemma_fun_t) simplex_gen_interface_lemma,
  (release_model_fun_t) simplex_release_model,
  (build_partition_fun_t) simplex_build_model_partition,
  (free_partition_fun_t) simplex_release_model_partition,
  (attach_to_var_fun_t) simplex_attach_eterm,
  (get_eterm_fun_t) simplex_eterm_of_var,
  (select_eq_polarity_fun_t) simplex_select_eq_polarity,
};


static arith_egraph_interface_t simplex_arith_egraph = {
  (make_arith_var_fun_t) simplex_create_var,
  (arith_val_fun_t) simplex_value_in_model,
};


/*
 * Get the egraph interfaces
 */
th_egraph_interface_t *simplex_egraph_interface(simplex_solver_t *solver) {
  return &simplex_egraph;
}

arith_egraph_interface_t *simplex_arith_egraph_interface(simplex_solver_t *solver) {
  return &simplex_arith_egraph;
}





/***************************
 *   DEBUGGING FUNCTIONS   *
 **************************/

#if DUMP

static void print_simplex(FILE *f, simplex_solver_t *solver) {
  fprintf(f, "\n==== Variables ====\n");
  print_simplex_vars(f, solver);
  fprintf(f, "\n==== Tableau ====\n");
  print_simplex_matrix(f, solver);
  fprintf(f, "\n==== Fixed vars ====\n");
  print_fixed_var_vector(f, &solver->vtbl, &solver->fvars);
  fprintf(f, "\n==== Eliminated rows ====\n");
  print_elim_matrix(f, &solver->vtbl, &solver->elim);
  fprintf(f, "\n==== Bounds  ====\n");
  print_simplex_bounds(f, solver);
  fprintf(f, "\n==== Assignment ====\n");
  print_simplex_assignment(f, solver);
  fprintf(f, "\n==== Atoms ====\n");
  print_simplex_atoms(f, solver);
  fprintf(f, "\n==== Boolean gates ====\n");
  print_gate_table(f, &solver->gate_manager->htbl);
}

static void print_core(FILE *f, smt_core_t *core) {
  fprintf(f, "\n==== Clauses ====\n");
  print_clauses(f, core);
  fprintf(f, "\n==== Boolean assignment ====\n");
  print_boolean_assignment(f, core);
}

static void dump_state(simplex_solver_t *solver) {
  FILE *dump;

  dump = fopen("simplex.dmp", "w");
  if (dump == NULL) return;
  print_simplex(dump, solver);
  print_core(dump, solver->core);
  fclose(dump);
}

#endif



#if DEBUG

/*
 * Error messages about variable x
 */
static void print_var_value(simplex_solver_t *solver, thvar_t x) {
  printf("     val[");
  print_simplex_var(stdout, solver, x);
  printf("] = ");
  xq_print(stdout, arith_var_value(&solver->vtbl, x));
  printf("\n");
}

static void print_var_lower_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t j;

  printf("     lb[");
  print_simplex_var(stdout, solver, x);
  printf("] = ");
  j = arith_var_lower_index(&solver->vtbl, x);
  if (j < 0) {
    printf(" - infinity\n");
  } else {
    xq_print(stdout, &solver->bstack.bound[j]);
    printf("\n");
  }
}

static void print_var_upper_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t j;

  printf("     ub[");
  print_simplex_var(stdout, solver, x);
  printf("] = ");
  j = arith_var_upper_index(&solver->vtbl, x);
  if (j < 0) {
    printf(" + infinity\n");
  } else {
    xq_print(stdout, &solver->bstack.bound[j]);
    printf("\n");
  }
}

static void print_var_lower_tag(simplex_solver_t *solver, thvar_t x) {
  printf("     lb_flag[");
  print_simplex_var(stdout, solver, x);
  if (arith_var_at_lower_bound(&solver->vtbl, x)) {
    printf("] = true\n");
  } else {
    printf("] = false\n");
  }
}

static void print_var_upper_tag(simplex_solver_t *solver, thvar_t x) {
  printf("     ub_flag[");
  print_simplex_var(stdout, solver, x);
  if (arith_var_at_upper_bound(&solver->vtbl, x)) {
    printf("] = true\n");
  } else {
    printf("] = false\n");
  }
}

/*
 * Check whether assertion a is satisfied
 */
static void check_assertion(simplex_solver_t *solver, int32_t a) {
  arith_atom_t *atom;
  uint32_t i;
  bool b;

  i = atom_of_assertion(a);
  atom = arith_atom(&solver->atbl, i);
  b = simplex_eval_atom(solver, atom);
  if (b != assertion_is_true(a)) {
    printf("---> ERROR: assertion not satisfied\n");
    printf("     Atom ");
    print_simplex_atom(stdout, solver, i);
    if (assertion_is_true(a)) {
      printf(" asserted true\n");
    } else {
      printf(" asserted false\n");
    }
    print_var_value(solver, var_of_atom(atom));
  }

  switch (bvar_value(solver->core, boolvar_of_atom(atom))) {
  case VAL_FALSE:
    if (assertion_is_true(a)) {
      printf("---> ERROR: truth assignment mismatch\n");
      printf("     atom %"PRId32" asserted true\n", i);
      printf("     var ");
      print_bvar(stdout, boolvar_of_atom(atom));
      printf(" is false\n");
    }
    break;
  case VAL_UNDEF_TRUE:
  case VAL_UNDEF_FALSE:
    printf("---> ERROR: truth assignment mismatch\n");
    printf("     atom %"PRId32" asserted\n", i);
    printf("     atom %"PRId32" is ", i);
    print_simplex_atom(stdout, solver, i);
    printf("\n");
    printf("     var ");
    print_bvar(stdout, boolvar_of_atom(atom));
    printf(" not assigned\n");
    break;
  case VAL_TRUE:
    if (assertion_is_false(a)) {
      printf("---> ERROR: truth assignment mismatch\n");
      printf("     atom %"PRId32" asserted false\n", i);
      printf("     var ");
      print_bvar(stdout, boolvar_of_atom(atom));
      printf(" is true\n");
    }
    break;
  }
}


/*
 * Check whether all assertions are satisfied by the current assignment
 */
static void check_all_assertions_satisfied(simplex_solver_t *solver) {
  arith_astack_t *stack;
  uint32_t i, n;

  stack = &solver->assertion_queue;
  n = stack->top;
  for (i=0; i<n; i++) {
    check_assertion(solver, stack->data[i]);
  }
}



/*
 * Check whether the current assignment satisfies all the bounds
 */
static void check_all_bounds_satisfied(simplex_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (! value_satisfies_bounds(solver, i)) {
      printf("---> ERROR: val[");
      print_simplex_var(stdout, solver, i);
      printf("] not within bounds\n");
      print_var_value(solver, i);
      print_var_lower_bound(solver, i);
      print_var_upper_bound(solver, i);
      fflush(stdout);
    }
  }
}


/*
 * Check whether the current assignment satisfies all bounds on non-basic
 * variables.
 */
static void check_all_nonbasic_bounds_satisfied(simplex_solver_t *solver) {
  uint32_t i, n;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (matrix_is_nonbasic_var(&solver->matrix, i) &&
        ! value_satisfies_bounds(solver, i)) {
      printf("---> ERROR: non-basic val[");
      print_simplex_var(stdout, solver, i);
      printf("] not within bounds\n");
      print_var_value(solver, i);
      print_var_lower_bound(solver, i);
      print_var_upper_bound(solver, i);
      fflush(stdout);
    }
  }
}

/*
 * Check whether equation in row r is satisfied
 */
static void check_equation_satisfied(simplex_solver_t *solver, uint32_t r) {
  row_t *row;
  xrational_t check;
  uint32_t i, n;
  thvar_t x;

  xq_init(&check);
  row = matrix_row(&solver->matrix, r);
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 0) {
      xq_addmul(&check, arith_var_value(&solver->vtbl, x), &row->data[i].coeff);
    }
  }

  if (! xq_is_zero(&check)) {
    printf("---> ERROR: row[%"PRIu32"] not satisfied\n", r);
    fflush(stdout);
  }
  xq_clear(&check);
}


/*
 * Check whether all equations in matrix are satisfied
 */
static void check_all_equations_satisfied(simplex_solver_t *solver) {
  uint32_t i, n;

  n = solver->matrix.nrows;
  for (i=0; i<n; i++) {
    check_equation_satisfied(solver, i);
  }
}


/*
 * Check whether the current assignment satisfies all the constraints
 */
static void check_assignment(simplex_solver_t *solver) {
  check_all_bounds_satisfied(solver);
  check_all_equations_satisfied(solver);
  check_all_assertions_satisfied(solver);
}


/*
 * Check whether the current assignment satisfies all equality constraints
 * and all bounds on non-basic variables.
 */
static void check_nonbasic_assignment(simplex_solver_t *solver) {
  check_all_nonbasic_bounds_satisfied(solver);
  check_all_equations_satisfied(solver);
}


/*
 * Check whether the ub/lb tags on non-basic variables are correct
 */
static void check_vartags(simplex_solver_t *solver) {
  uint32_t i, n;
  bool at_bound, tag;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (matrix_is_nonbasic_var(&solver->matrix, i)) {
      at_bound = variable_at_lower_bound(solver, i);
      tag = arith_var_at_lower_bound(&solver->vtbl, i);
      if (at_bound != tag) {
        printf("---> ERROR: wrong tag for variable ");
        print_simplex_var(stdout, solver, i);
        printf("\n");
        print_var_value(solver, i);
        print_var_lower_bound(solver, i);
        print_var_lower_tag(solver, i);
        fflush(stdout);
      }

      at_bound = variable_at_upper_bound(solver, i);
      tag = arith_var_at_upper_bound(&solver->vtbl, i);
      if (at_bound != tag) {
        printf("---> ERROR: wrong tag for variable ");
        print_simplex_var(stdout, solver, i);
        printf("\n");
        print_var_value(solver, i);
        print_var_upper_bound(solver, i);
        print_var_upper_tag(solver, i);
        fflush(stdout);
      }
    }
  }
}


/*
 * Check that all infeasible basic variables are in the heap
 */
static void check_infeasible_vars(simplex_solver_t *solver) {
  uint32_t i, n;
  thvar_t x;

  n = solver->matrix.nrows;
  for (i=0; i<n; i++) {
    x = matrix_basic_var(&solver->matrix, i);
    if (! (value_satisfies_bounds(solver, x) || int_heap_member(&solver->infeasible_vars, x))) {
      printf("---> ERROR: infeasible variable ");
      print_simplex_var(stdout, solver, x);
      printf(" not in the heap\n");
      fflush(stdout);
    }
  }
}



/*
 * Check that all bounds on integer variables are integer constants
 */
static void check_integer_bounds(simplex_solver_t *solver) {
  uint32_t i, n;
  int32_t k;

  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    if (arith_var_is_int(&solver->vtbl, i)) {
      k = arith_var_upper_index(&solver->vtbl, i);
      if (k >= 0 && ! xq_is_integer(solver->bstack.bound + k)) {
        printf("---> ERROR: non-integer bound on an integer variable ");
        print_simplex_var(stdout, solver, i);
        printf("\n");
        print_var_upper_bound(solver, i);
        fflush(stdout);
      }

      k = arith_var_lower_index(&solver->vtbl, i);
      if (k >= 0 && ! xq_is_integer(solver->bstack.bound + k)) {
        printf("---> ERROR: non-integer bound on an integer variable ");
        print_simplex_var(stdout, solver, i);
        printf("\n");
        print_var_lower_bound(solver, i);
        fflush(stdout);
      }
    }
  }
}


/*
 * All indices should be unmarked, except within theory/conflict explanation
 */
static void check_bound_marks(simplex_solver_t *solver) {
  arith_bstack_t *bstack;
  uint32_t i, n;

  bstack = &solver->bstack;
  n = bstack->top;
  for (i=0; i<n; i++) {
    if (arith_cnstr_is_marked(bstack, i)) {
      printf("---> ERROR: mark on bound %"PRIu32" is not cleared\n", i);
      fflush(stdout);
    }
  }
}


#endif



#if TRACE

/*
 * Show the list of infeasible variables (bounds not satisfied)
 * - these variables are stored in the heap after a call to
 *   simplex_fix_nonbasic_assingment
 */
static void show_heap(FILE *f, simplex_solver_t *solver) {
  uint32_t i, n;

  n = solver->matrix.nrows;
  fprintf(f, "Infeasible vars:");
  for (i=0; i<n; i++) {
    if (int_heap_member(&solver->infeasible_vars, i)) {
      fprintf(f, " x_%"PRIu32, i);
    }
  }
  fprintf(f, "\n");
}

#endif
