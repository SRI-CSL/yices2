/*
 * SIMPLEX SOLVER
 *
 * Version 3: started 2008/11/03
 */

#include "prng.h"
#include "bitvectors.h"

#include "int_hash_classes.h"
#include "hash_functions.h"

#include "simplex.h"


/*
 * To enable trace, set TRACE to 1
 * To enable the debugging code, set DEBUG to 1
 * To dump the initial tableau, set DUMP to 1
 * To export the initial problem for Yices1, set YEXPORT to 1
 * To trace simplifications and tableau initialization set TRACE_INIT to 1
 */
#define TRACE   0
#define DEBUG   1
#define DUMP    0
#define YEXPORT 0

#define TRACE_INIT 0
#define TRACE_PROPAGATION 0
#define TRACE_THEORY 0
#define TRACE_BB 0


#if TRACE || DEBUG || TRACE_INIT || DUMP || YEXPORT || TRACE_PROPAGATION || TRACE_BB || !defined(NDEBUG) || 1

#include <stdio.h>
#include <inttypes.h>

#include "term_printer.h"
#include "dsolver_printer.h"
#include "egraph_printer.h"
#include "gates_printer.h"
#include "smt_core_printer.h"
#include "simplex_printer.h"

#endif

#if TRACE_THEORY
#include "theory_tracer.h"
#endif

#if YEXPORT
#include "solver_export.h"
#endif



/*
 * Debuggging functions are defined at the end of this file
 */
#if DUMP

static void print_simplex(FILE *f, simplex_solver_t *solver);
static void dump_state(simplex_solver_t *solver);

#endif

#if YEXPORT

static void export_state(simplex_solver_t *solver);

#endif

#if DEBUG

static void check_assignment(simplex_solver_t *solver);
static void check_nonbasic_assignment(simplex_solver_t *solver);
static void check_vartags(simplex_solver_t *solver);
static void check_infeasible_vars(simplex_solver_t *solver);
static void check_integer_bounds(simplex_solver_t *solver);
static void check_bound_marks(simplex_solver_t *solver);

#endif




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
 *   (all bound of index fix_prt to top-1 are to be processed)
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
 * The following functions convert betwen atom_id+sign and 32bit code
 */
static inline int32_t mk_true_assertion(int32_t atom_id) {
  return atom_id << 1;
}

static inline int32_t mk_false_assertion(int32_t atom_id) {
  return (atom_id << 1) | 1;
}

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

static inline bool assertion_is_true(int32_t a) {
  return sign_of_assertion(a) == 0;
}

static inline bool assertion_is_false(int32_t a) {
  return sign_of_assertion(a) == 1;
}




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
 * Get the top record
 */
static inline arith_undo_record_t *arith_undo_stack_top(arith_undo_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data + (stack->top - 1);
}



/*
 * Empty the stack
 */
static inline void reset_arith_undo_stack(arith_undo_stack_t *stack) {
  stack->top = 0;
}



/*
 * Delete the stack
 */
static inline void delete_arith_undo_stack(arith_undo_stack_t *stack) {
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
 * - nx = number of active variables saved
 * - pa = propagation pointer in the assertion stack
 * - pb = propagation pointer in the bound stack
 */
static void arith_trail_save(arith_trail_stack_t *stack, uint32_t nv, uint32_t na, 
			     uint32_t nr, uint32_t nx, uint32_t pa, uint32_t pb) {
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
  stack->data[i].nsaved_vars = nx;
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
static inline void arith_trail_pop(arith_trail_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}

/*
 * Delete the stack
 */
static inline void delete_arith_trail(arith_trail_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}


/*
 * Empty the stack
 */
static inline void reset_arith_trail(arith_trail_stack_t *stack) {
  stack->top = 0;
}





/**************************************
 *  SAVED ROWS AND ACTIVE VARIABLES   *
 *************************************/

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


/*
 * Clear the active marks on all variables in v->data[n ... v->size - 1]
 * where v = saved_vars, then resize v to n
 */
static void deactivate_saved_vars(simplex_solver_t *solver, uint32_t n) {
  arith_vartable_t *vtbl;
  ivector_t *v;
  uint32_t i, k;
  thvar_t x;

  vtbl = &solver->vtbl;
  v = &solver->saved_vars;
  k = v->size;
  assert(n <= k);

  for (i=n; i<k; i++) {
    x = v->data[i];
    assert(arith_var_is_active(vtbl, x));
    mark_arith_var_inactive(vtbl, x);
  }

  ivector_shrink(v, n);
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
  stat->num_make_feasible = 0;
  stat->num_pivots = 0;
  stat->num_blands = 0;
  stat->num_conflicts = 0;
  stat->num_make_intfeasible = 0;
  stat->num_branch_atoms = 0;
  stat->num_extended_branch = 0;
  stat->num_gcd_conflicts = 0;
  stat->num_dioph_checks = 0;
  stat->num_dioph_conflicts = 0;
  stat->num_bound_conflicts = 0;
  stat->num_recheck_conflicts = 0;
}


static inline void reset_simplex_statistics(simplex_stats_t *stat) {
  init_simplex_statistics(stat);
}




/*************************
 *  FRESHVAL STRUCTURE   *
 ************************/

/*
 * Allocate the structure
 * - all bits in used_val are 0
 * - low is initialized to NVAL, high to HVAL
 * - max_used is initialized to HVAL
 */
static simplex_freshval_t *simplex_new_freshval_set(void) {
  simplex_freshval_t *tmp;

  tmp = (simplex_freshval_t *) safe_malloc(sizeof(simplex_freshval_t));
  tmp->used_val = allocate_bitvector0(SIMPLEX_NVAL);
  tmp->used_val_idx = 0;
  tmp->low = SIMPLEX_NVAL;
  tmp->high = SIMPLEX_HVAL;
  q_init(&tmp->max_used);
  q_set32(&tmp->max_used, SIMPLEX_HVAL);

  return tmp;
}


/*
 * Delete set
 */
static void simplex_free_freshval_set(simplex_freshval_t *set) {
  delete_bitvector(set->used_val);
  q_clear(&set->max_used);
  safe_free(set);
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



// assertion x <= c with x1 and x2 as explanation (implied by the egraph)
static void push_ub_egraph(simplex_solver_t *solver, thvar_t x, rational_t *c, thvar_t x1, thvar_t x2) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set_q(stack->bound + k, c);
  stack->var[k] = x;
  stack->pre[k] = arith_var_upper_index(&solver->vtbl, x);
  stack->expl[k].v[0] = x1;
  stack->expl[k].v[1] = x2;
  stack->tag[k] = ARITH_EGRAPHEQ_UB;
  set_arith_var_upper_index(&solver->vtbl, x, k);  
}


// assertion x >= c with x1 and x2 as explanation (implied by the egraph)
static void push_lb_egraph(simplex_solver_t *solver, thvar_t x, rational_t *c, thvar_t x1, thvar_t x2) {
  arith_bstack_t *stack;
  int32_t k;

  stack = &solver->bstack;
  k = arith_bstack_new_constraint(stack);

  xq_set_q(stack->bound + k, c);
  stack->var[k] = x;
  stack->pre[k] = arith_var_lower_index(&solver->vtbl, x);
  stack->expl[k].v[0] = x1;
  stack->expl[k].v[1] = x2;
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
static inline bool simplex_eliminable_variable(simplex_solver_t *solver, thvar_t x) {
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
  solver->use_blands_rule = false;
  solver->bland_threshold = SIMPLEX_DEFAULT_BLAND_THRESHOLD;
  solver->prop_row_size = SIMPLEX_DEFAULT_PROP_ROW_SIZE;
  solver->last_conflict_row = -1;
  solver->recheck = false;

  solver->integer_solving = false;
  solver->check_counter = 0;
  solver->check_period = SIMPLEX_DEFAULT_CHECK_PERIOD;
  solver->dsolver = NULL;     // allocated later if needed

  solver->cache = NULL;       // allocated later if needed

  init_simplex_statistics(&solver->stats);

  init_arith_atomtable(&solver->atbl, core);
  init_arith_vartable(&solver->vtbl);

  solver->propagator = NULL; // allocated if needed in start search

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
  init_ivector(&solver->saved_vars, 0);

  init_elim_matrix(&solver->elim);
  init_fvar_vector(&solver->fvars);

  init_poly_buffer(&solver->buffer);
  q_init(&solver->constant);
  q_init(&solver->aux);
  q_init(&solver->gcd);
  xq_init(&solver->bound);
  xq_init(&solver->delta);

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
  solver->freshval = NULL;

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
 */
static void build_binary_lemmas_for_atom(simplex_solver_t *solver, thvar_t x, int32_t id) {
  arith_atomtable_t *atbl;
  int32_t *atom_vector;
  arith_atom_t *atom1, *atom2;
  uint32_t i, n;
  int32_t id2;

  if (simplex_option_enabled(solver, SIMPLEX_EAGER_LEMMAS)) {
    atom_vector = arith_var_atom_vector(&solver->vtbl, x);
    if (atom_vector != NULL) {
      atbl = &solver->atbl;
      atom1 = arith_atom(atbl, id);
      assert(var_of_atom(atom1) == x);
      n = iv_size(atom_vector);
      for (i=0; i<n; i++) {
	id2 = atom_vector[i];
	assert(id != id2);
	atom2 = arith_atom(atbl, id2);
	create_binary_lemma(solver, atom1, atom2);
      }
    }
  }
}





/*****************************
 *  POLYNOMIAL CONSTRUCTION  *
 ****************************/

/*
 * Check whether p is a simple polynomial (cheap to substitute)
 * - return true if p is either (c + b.y) or c or b.y or 0
 */
static bool simple_poly(polynomial_t *p) {
  uint32_t n;

  n = p->nterms;
  return (n <= 1) || (n <= 2 && p->mono[0].var == const_idx);
}


/*
 * Check whether to substitute x by its definition in polynomials or atoms
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
  matrix_add_column(&solver->matrix);
  return create_arith_var(&solver->vtbl, is_int);
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
  }

  reset_poly_buffer(b);

  assert(trivial_variable(&solver->vtbl, x));

  return x;
}



/*
 * Get a variable x whose definition is equal to the buffer then reset the buffer
 * - if x is a new variable, add a column to the matrix
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
    }
  }
  reset_poly_buffer(b);

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
 * Attach egraph term t to a variable v
 * - v must not have an eterm attached already
 */
void simplex_attach_eterm(simplex_solver_t *solver, thvar_t v, eterm_t t) {
  attach_eterm_to_arith_var(&solver->vtbl, v, t);
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
 * Activate variable x if necessary
 * - if x is a free variable, nothing to do
 * - if x is attached to a polynomial p and is not active already
 *   add the row x - p == 0 to the matrix
 */
static void activate_variable(simplex_solver_t *solver, thvar_t x) {
  arith_vartable_t *vtbl;
  polynomial_t *p;

  assert(! trivial_variable(&solver->vtbl, x));

  vtbl = &solver->vtbl;
  p = arith_var_def(vtbl, x);
  if (p != NULL && arith_var_is_inactive(vtbl, x)) {
    matrix_add_eq(&solver->matrix, x, p->mono, p->nterms);
    mark_arith_var_active(vtbl, x);

    if (solver->base_level > 0) {
      /*
       * save_rows is true if  multichek or push/pop are enabled.
       * if x was created at an earlier base level, then we 
       * add it to saved_vars so it can be deactivated on the next 'pop'
       */
      assert(solver->save_rows && solver->trail_stack.top == solver->base_level);
      if (x >= arith_trail_top(&solver->trail_stack)->nvars) {
	// x was created at level k < n and 
	// activated as level n = the current base level
	ivector_push(&solver->saved_vars, x);
      }
    }
  }

}


/*
 * Create the atom (x >= c) or (x <= c)
 * - is_int indicates whether x is an integer variable or not
 * - activate x
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
    activate_variable(solver, x);
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
    activate_variable(solver, x);
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
    }
  }
  reset_poly_buffer(b);
  return x;
}



/*
 * Create the atom x >= 0
 * - this attach the atom to the smt_core
 */
literal_t simplex_create_ge_atom(simplex_solver_t *solver, thvar_t x) {
  poly_buffer_t *b;
  bool negated, is_int;

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

  activate_variable(solver, x);
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

  activate_variable(solver, x);
  push_ub_axiom(solver, x, b);
}



/*
 * Add the axiom p == 0 where p is stored in the solver's buffer
 * - if p == 0 simplifies to false, set the 'unsat_before_search' flag
 * - if p == 0 simplifies to true, do nothing
 * - otherwise, add the row p == 0 to the matrix
 */
static void add_eq_axiom(simplex_solver_t *solver) {
  poly_buffer_t *b;

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
      q_floor(&solver->constant);
      if (tt) {
	// (p >= 0) is equivalent to (x <= constant)
	add_ub_axiom(solver, x, &solver->constant, false);
      } else {
	// not (p >= 0) is equivalent to (x >= constant + 1)
	q_add_one(&solver->constant);
	add_lb_axiom(solver, x, &solver->constant, false);
      }
    } else {
      q_ceil(&solver->constant);
      if (tt) {
	// (p >= 0) is equivalent to (x >= constant)
	add_lb_axiom(solver, x, &solver->constant, false);
      } else {
	// not (p >= 0) is equivalent to (x <= constant - 1)
	q_sub_one(&solver->constant);
	add_ub_axiom(solver, x, &solver->constant, false);
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



/*
 * Assert a top-level inequality (either x >= 0 or x < 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x >= 0
 *   tt == false --> assert x < 0
 */
void simplex_assert_ge_axiom(simplex_solver_t *solver, thvar_t x, bool tt){
  arith_vartable_t *vtbl;
  polynomial_t *q;
  poly_buffer_t *b;

  assert(arith_var_kind(&solver->vtbl, x) == AVAR_FREE ||
	 arith_var_kind(&solver->vtbl, x) == AVAR_POLY);

#if TRACE
  printf("\n---> simplex_assert_ge_axiom: ");
  print_simplex_var(stdout, solver, x);
  if (tt) {
    printf(" >= 0\n");
  } else {
    printf(" < 0\n");
  }
#endif  

  vtbl = &solver->vtbl;
  q = arith_var_def(vtbl, x);
  if (q == NULL || arith_var_is_active(vtbl, x)) {
    /*
     * Directly add the bound on x
     */
    q_clear(&solver->constant);
    if (tt) {
      // add bound x >= 0
      add_lb_axiom(solver, x, &solver->constant, false);
    } else if (arith_var_is_int(vtbl, x)) {
      // add bound x <= -1
      q_set_minus_one(&solver->constant);
      add_ub_axiom(solver, x, &solver->constant, false);
    } else {
      // x < 0
      add_ub_axiom(solver, x, &solver->constant, true);
    }
    
  } else {
    /*
     * Replace x byt its definition:
     * - assert q >= 0 or (q < 0)
     */
    b = &solver->buffer;
    assert(poly_buffer_nterms(b) == 0);
    poly_buffer_add_poly(b, q);
    normalize_poly_buffer(b);
    add_ge_axiom(solver, tt);
  }

}




/*
 * Assert a top-level equality constraint (either x == 0 or x != 0)
 * - tt indicates whether the constraint or its negation must be asserted
 *   tt == true  --> assert x == 0
 *   tt == false --> assert x != 0
 */
void simplex_assert_eq_axiom(simplex_solver_t *solver, thvar_t x, bool tt) {
  arith_vartable_t *vtbl;
  polynomial_t *q;
  poly_buffer_t *b;
  literal_t l, l1, l2;
  bool is_int;

  assert(arith_var_kind(&solver->vtbl, x) == AVAR_FREE ||
	 arith_var_kind(&solver->vtbl, x) == AVAR_POLY);


#if TRACE
  printf("\n---> simplex_assert_eq_axiom: ");
  print_simplex_var(stdout, solver, x);
  if (tt) {
    printf(" == 0\n");
  } else {
    printf(" != 0\n");
  }
#endif


  vtbl = &solver->vtbl;
  q = arith_var_def(vtbl, x);
  if (q == NULL || arith_var_is_active(vtbl, x)) {
    q_clear(&solver->constant);
    if (tt) {
      /*
       * Add the bounds (x <= 0) and (x >= 0) on x
       */
      add_lb_axiom(solver, x, &solver->constant, false);
      add_ub_axiom(solver, x, &solver->constant, false);      
    } else {
      /*
       * Create the atoms (x >= 0) and (x <= 0)
       * and add the clause (or (not (x >= 0)) (not (x <= 0)))
       */
      is_int = arith_var_is_int(vtbl, x);
      l1 = get_ge_atom(solver, x, is_int, &solver->constant);  // x >= 0
      l2 = get_le_atom(solver, x, is_int, &solver->constant);  // x <= 0
      add_binary_clause(solver->core, not(l1), not(l2));

#if TRACE
      printf("---> adding clause: ");
      print_binary_clause(stdout, not(l1), not(l2));
      printf("\n");
      print_simplex_atomdef(stdout, solver, var_of(l1));
      print_simplex_atomdef(stdout, solver, var_of(l2));
#endif
    }

  } else {
    /*
     * Replace x by its definition q
     */
    b = &solver->buffer;
    assert(poly_buffer_nterms(b) == 0);
    poly_buffer_add_poly(b, q);
    normalize_poly_buffer(b);
    
    if (tt) {
      /*
       * Assert q == 0
       */
      add_eq_axiom(solver);

    } else {
      /*
       * Assert (or (not (q >= 0) (not (q <= 0))))
       */
      l = simplify_eq_atom(solver, &l1, &l2);
      if (l == null_literal) {
	// l1 is (q >= 0), l2 is (q <= 0): assert (or (not l1) (not l2))
	add_binary_clause(solver->core, not(l1), not(l2));

#if TRACE
	printf("---> adding clause: ");
	print_binary_clause(stdout, not(l1), not(l2));
	printf("\n");
	print_simplex_atomdef(stdout, solver, var_of(l1));
	print_simplex_atomdef(stdout, solver, var_of(l2));
#endif

      } else if (l == true_literal) {
	// q == 0 is true
	solver->unsat_before_search = true;
      } // if l == false, q != 0 is true 
    }
  }
}


/*
 * If tt == true --> assert (x - y == 0)
 * If tt == false --> assert (x - y != 0)
 */
void simplex_assert_vareq_axiom(simplex_solver_t *solver, thvar_t x, thvar_t y, bool tt) {
  poly_buffer_t *b;
  literal_t l, l1, l2;

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

  if (tt) {
    add_eq_axiom(solver);
  } else {
    l = simplify_eq_atom(solver, &l1, &l2);
    if (l == null_literal) {

#if TRACE
      printf("---> adding clause: ");
      print_binary_clause(stdout, not(l1), not(l2));
      printf("\n");
      print_simplex_atomdef(stdout, solver, var_of(l1));
      print_simplex_atomdef(stdout, solver, var_of(l2));
#endif

      // l1 is (p >= 0), l2 is (p <= 0): assert (or (not l1) (not l2))
      add_binary_clause(solver->core, not(l1), not(l2));
    } else if (l == true_literal) {
      // p == 0 is true
      solver->unsat_before_search = true;
    } // if l == false_literal, p != 0 is true
  }
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
 

/*****************************************
 *  SIMPLIFICATION/TABLEAU CONSTRUCTION  *
 ****************************************/

/*
 * Record the initial statistics
 */
static inline void simplex_set_initial_stats(simplex_solver_t *solver) {
  solver->stats.num_init_vars = solver->vtbl.nvars;
  solver->stats.num_init_rows = solver->matrix.nrows;
  solver->stats.num_atoms = solver->atbl.natoms;
}


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
  printf("\n**** SIMPIFYING THE MATRIX ****\n\n");
  print_simplex_matrix(stdout, solver);
#endif

  /*
   * Mark the variables to keep
   */
  vtbl = &solver->vtbl;
  n = solver->vtbl.nvars;
  keep = allocate_bitvector0(n);  // default: all bits are 0

  for (i=1; i<n; i++) { // skip the constant
    if (!simplex_free_variable(solver, i) || arith_var_num_atoms(vtbl, i) > 0) {
      // i is constrained or has atoms attached: keep it
      set_bit(keep, i);
    } else if (arith_var_has_eterm(vtbl, i)) {
      // i has an egraph term: keep it
      // also if i is trivial then all variables in i's definition
      // must be kept too
      set_bit(keep, i);
      if (trivial_variable(vtbl, i)) {
	mark_vars_of_poly(keep, arith_var_def(vtbl, i));
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
#endif

  ivector_reset(aux);

  delete_bitvector(keep);
  delete_bitvector(ivars);
}



/*
 * Compute the initial tableau
 */
static void simplex_init_tableau(simplex_solver_t *solver) {
  markowitz_tableau_construction(&solver->matrix, &solver->fvars);
  solver->stats.num_rows = solver->matrix.nrows;
  solver->stats.num_fixed_vars = solver->fvars.nvars;  

#if TRACE_INIT
  printf("---> %"PRIu32" rows in initial tableau\n", solver->matrix.nrows);
  printf("---> %"PRIu32" fixed variables detected:\n\n", solver->fvars.nvars);
  print_fixed_var_vector(stdout, &solver->vtbl, &solver->fvars);
#endif

#if TRACE_THEORY
  trace_tableau();
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
 * This invariant must hold before make_feasible is called.
 */

/*
 * Set the ub/lb flags for a variable x
 */
static void simplex_set_bound_flags(simplex_solver_t *solver, thvar_t x) {
  uint32_t t;

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
	xq_clear(v);
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

  // mark that the tableau is ready
  solver->tableau_ready = true;
  solver->matrix_ready = false;
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





/******************
 *  EXPLANATIONS  *
 *****************/

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


/*
 * Add the explanation for (x1 == x2) to vector v
 * then remove duplicate literals from v.
 */
static void collect_egraph_eq_expl(simplex_solver_t *solver, thvar_t x1, thvar_t x2, ivector_t *v) {
  eterm_t t1, t2;
  uint32_t n;

  t1 = arith_var_eterm(&solver->vtbl, x1);
  t2 = arith_var_eterm(&solver->vtbl, x2);
  n = v->size;
  egraph_explain_term_eq(solver->egraph, t1, t2, v);
  if (n > 0) {
    ivector_remove_duplicates(v);
  }
}


/*
 * Expand the explanation queue: convert it to a conjunction of literals
 * - solver->expl_queue must contain a set of constraint indices
 * - a list of literals that explain all these constraints is added to v
 * - the queue is emptied
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
      collect_egraph_eq_expl(solver, bstack->expl[i].v[0], bstack->expl[i].v[1], aux);
      break;

    default:
      abort();
      break;
    }
  }

  // add literals of aux into v
  ivector_add(v, aux->data, aux->size);
  ivector_reset(aux);

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
 * - this expanded first into a conjuncion of literals (inconsistent)
 * - then this is turned into a clause
 */
static void simplex_build_conflict_clause(simplex_solver_t *solver, ivector_t *v) {
  assert(v->size == 0);
  simplex_build_explanation(solver, v);
  convert_expl_to_clause(v);
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
static inline bool possible_entering_var_for_increase(arith_vartable_t *vtbl, thvar_t y, rational_t *a) {
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
	  if (random_uint(k) == 0) {
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
static inline bool possible_entering_var_for_decrease(arith_vartable_t *vtbl, thvar_t y, rational_t *a) {
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
	  if (random_uint(k) == 0) {
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
 * Generate a conflict explanation for an infeasible row:
 * - case 1: base-variable x is below its lower bound and there are no
 *   entering variable in the row.
 * - the explanation is stored in expl_vector
 */
static void build_conflict_for_increase(simplex_solver_t *solver, row_t *row, thvar_t x) {
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

  // translate the queue into a conjunction of literals (stored in expl_vector);
  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_build_conflict_clause(solver, v);

  // record expl_vector as a conflict (first add the null-literal terminator)  
  ivector_push(v, null_literal);
  record_theory_conflict(solver->core, v->data);

#if TRACE_THEORY
  trace_simplex_conflict(row, v->data);
#endif

  solver->stats.num_conflicts ++;
}


/*
 * Generate a conflict explanation for an infeasible row:
 * - case 2: base-variable x is above its upper bound and there are no
 *   entering variable in the row.
 * - the explanation is stored in expl_vector
 */
static void build_conflict_for_decrease(simplex_solver_t *solver, row_t *row, thvar_t x) {
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

  // translate the queue into a conjunction of literals (stored in expl_vector);
  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_build_conflict_clause(solver, v);

  // record expl_vector as a conflict (first add the null-literal terminator)
  ivector_push(v, null_literal);
  record_theory_conflict(solver->core, v->data);

#if TRACE_THEORY
  trace_simplex_conflict(row, v->data);
#endif

  solver->stats.num_conflicts ++;
}



/*
 * Check for feasibility:
 * - search for an assignment that satisfies all constraints
 * - the infeasible basic variables must be stored in solver->infeasible_vars
 * - return true if such an assignment is found
 * - return false if a conflict is detected
 */
static bool simplex_make_feasible(simplex_solver_t *solver) {
  matrix_t *matrix;
  arith_vartable_t *vtbl;
  ivector_t *leaving_vars;
  row_t *row;
  thvar_t x;
  int32_t r, k;
  uint32_t repeats;
  bool feasible;

#if TRACE
  printf("---> Simplex: make feasible\n");
#endif

#if DEBUG
  check_nonbasic_assignment(solver);
  check_vartags(solver);
  check_infeasible_vars(solver);
  check_integer_bounds(solver);
  check_bound_marks(solver);
#endif

  solver->stats.num_make_feasible ++;

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

  for (;;) {
    x = int_heap_get_min(&solver->infeasible_vars);
    if (x < 0) {
      feasible = true;
      break;
    }

    r = matrix_basic_row(matrix, x);
    row = matrix_row(matrix, r);
    k = -1;

    if (variable_below_lower_bound(solver, x)) {
      // find an entering variable that allows x to increase
      k = find_entering_var_for_increase(solver, row, x);
      if (k < 0) {
	// no entering variable ==> conflict
	build_conflict_for_increase(solver, row, x);
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
	build_conflict_for_decrease(solver, row, x);
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
	if (repeats > solver->bland_threshold) {
	  solver->use_blands_rule = true;
	  solver->stats.num_blands ++;
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

#if TRACE
  if (feasible) {
    printf("---> Simplex: make feasible succeeded\n");
  } else {
    printf("---> Simplex: arithmetic conflict\n");
  }
#endif

#if DEBUG
  check_vartags(solver);
  check_bound_marks(solver);
  if (feasible) {
    check_assignment(solver);
  } else {
    check_nonbasic_assignment(solver);
  }
#endif

  return feasible;
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

  // add the end marker
  ivector_push(v, null_literal);
  record_theory_conflict(solver->core, v->data);

  solver->stats.num_conflicts ++;

#if TRACE_THEORY
  trace_simplex_assertion_conflict(k, l, v->data);
#endif

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
#endif

  }
#if TRACE
  else {
    printf("---> redundant\n");
  }
#endif

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
#endif

  }

#if TRACE
  else {
    printf("---> redundant\n");
  }
#endif

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

#if TRACE_THEORY
  trace_simplex_implied_literal(i, l);
#endif
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

#if TRACE_THEORY
    trace_simplex_derived_lb_conflict(k, x, b, v, solver->expl_vector.data);
#endif

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

#if TRACE_THEORY
    trace_simplex_derived_ub_conflict(k, x, b, v, solver->expl_vector.data);
#endif

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




/******************************
 *  PROPAGATOR INCLUDED HERE  *
 *****************************/

#include "simplex_propagator1.h"






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
 *   start_search (modulo reordering, the rows may be permuted)
 */
static void simplex_restore_matrix(simplex_solver_t *solver) {
  pvector_t *v;
  polynomial_t *p;
  uint32_t i, n;

  if (! solver->matrix_ready) {
    assert(solver->save_rows && solver->matrix.nrows == 0 && 
	   solver->matrix.ncolumns == 0);

    // rebuild n empty columns in the matrix
    matrix_add_columns(&solver->matrix, solver->vtbl.nvars);

    // restore all the saved rows
    v = &solver->saved_rows;
    n = v->size;
    for (i=0; i<n; i++) {
      p = v->data[i];
      matrix_add_row(&solver->matrix, p->mono, p->nterms);
    }

    // restore the definitions of all active variables
    n = solver->vtbl.nvars;
    for (i=0; i<n; i++) {
      if (arith_var_is_active(&solver->vtbl, i)) {
	p = arith_var_poly_def(&solver->vtbl, i);
	assert(!simple_poly(p));
	matrix_add_eq(&solver->matrix, i, p->mono, p->nterms);
      }
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
  x = poly_buffer_nonconstant_convert_to_var(b);     // check whether p is a variable
  if (x < 0) {
    x = get_var_for_poly_offset(&solver->vtbl, poly_buffer_mono(b), poly_buffer_nterms(b), &new_var);
    if (new_var) {
      matrix = &solver->matrix;
      // add a new column to the matrix
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

#if TRACE || 1
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
static inline bool simplex_has_integer_vars(simplex_solver_t *solver) {
  return num_integer_vars(&solver->vtbl) > 1;
}

/*
 * Check whether the system mixes integer and non-integer variables
 */
static inline bool simplex_is_mixed_system(simplex_solver_t *solver) {
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
       * (since value[i] is not an integer and upper bound on i is an integer,
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
 * BRANCH & BOUND
 */

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
    if (arith_var_is_int(vtbl, i) && matrix_is_basic_var(&solver->matrix, i) &&
	! arith_var_value_is_int(vtbl, i)) {
      ivector_push(v, i);
    }
  }
}

/*
 * Create branch & bound atom for a variable x.
 * - we use (x >= ceil(value[x])), which must be a new atom
 */
static void create_branch_atom(simplex_solver_t *solver, thvar_t x) {
  xrational_t *bound;
  int32_t new_idx;
  literal_t l;

  assert(arith_var_is_int(&solver->vtbl, x) & ! arith_var_value_is_int(&solver->vtbl, x));

  bound = &solver->bound;
  xq_set(bound, arith_var_value(&solver->vtbl, x));
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
  /*
   * BD: TEMPORATY HACK (to support periodic calls to make_integer_feasible)
   * - we don't always call make_feasible in final check 
   * - so we can't assume the branch atom is new anymore
   */
  // assert(new_idx >= 0);
  if (new_idx >= 0) {
    build_binary_lemmas_for_atom(solver, x, new_idx);
    attach_atom_to_arith_var(&solver->vtbl, x, new_idx);

#if TRACE_BB
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
#define MAX_BRANCH_SCORE 20000
#define HALF_MAX_BRANCH_SCORE 10000

static uint32_t simplex_branch_score(simplex_solver_t *solver, thvar_t x) {
  rational_t *diff;
  int32_t l, u;
  uint32_t s;

  diff = &solver->aux;
  l = arith_var_lower_index(&solver->vtbl, x);
  u = arith_var_upper_index(&solver->vtbl, x);
  if (l < 0 || u < 0) {
    return MAX_BRANCH_SCORE;
  }
  q_set(diff, &solver->bstack.bound[u].main);
  q_sub(diff, &solver->bstack.bound[l].main);
  // diff = upper bound - lower bound
  if (q_is_smallint(diff)) {
    s = q_get_smallint(diff);
    if (s < HALF_MAX_BRANCH_SCORE) {
      return s;
    }
  }

  return HALF_MAX_BRANCH_SCORE;
}


/*
 * Select a branch variable of v: pick the one with smallest score.
 * Break ties randomly.
 */
static thvar_t select_branch_variable(simplex_solver_t *solver, ivector_t *v) {
  uint32_t i, n, best_score, score, k;
  thvar_t x, best_var;

  best_score = MAX_BRANCH_SCORE + 1;
  best_var = null_thvar;
  k = 0;

  n = v->size;
  for (i=0; i<n; i++) {
    x = v->data[i];
    score = simplex_branch_score(solver, x);
    if (score < best_score) {
      best_score = score;
      best_var = x;
      k = 1;
    } else if (score == best_score) {
      // break ties randomly
      k ++;
      if (random_uint(k) == 0) {
	best_var = x;
      }
    }
  }

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

  solver->stats.num_gcd_conflicts ++;

#if TRACE_THEORY
  trace_simplex_gcd_conflict(row, v->data);
#endif
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

#if TRACE_THEORY
  trace_simplex_dsolver_conflict(v, w->data);
#endif
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

static inline bool not_in_vector(ivector_t *q, int32_t k) {
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

#if TRACE_THEORY
    trace_dsolver_var_phase_and_period(x, gcd, constant);
#endif

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

#if TRACE_THEORY
	if (ok) trace_simplex_derived_lb(x, bound, q);
#endif

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

#if TRACE_THEORY
	if (ok) trace_simplex_derived_lb(x, bound, q);
#endif

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
	solver->stats.num_bound_conflicts ++;
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
static inline bool matrix_row_is_integral(simplex_solver_t *solver, row_t *row) {
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
 * - set solver->recheck to true if bound-stregthening requires a call to make_feasible
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


  solver->stats.num_dioph_checks ++;

  // run the diophantine solver
  dsolver_simplify(dioph);
  if (! dsolver_is_feasible(dioph)) {
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

  }

  // Try to strengthen the bounds
  dsolver_build_general_solution(dioph);
  return strengthen_integer_bounds(solver, dioph);
}




/*
 * For testing: run the dsolver on the initial system
 * - store a trace in init.dmp file
 */
static bool simplex_dsolver_check_at_start(simplex_solver_t *solver) {
  //  FILE *trace;
  dsolver_t *dioph;
  matrix_t *matrix;
  row_t *row;
  ivector_t *v;
  uint32_t i, n;
  //  int32_t r;
  bool pure_integer;
  bool feasible;

#if 0
  trace = fopen("init.dmp", "w");
  if (trace != NULL) {
    fprintf(trace, "Initial check using diophantine solver\n");
  }
#endif

  dioph = simplex_get_dsolver(solver);
  reset_dsolver(dioph);

  pure_integer = ! simplex_is_mixed_system(solver);

  matrix = &solver->matrix;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (pure_integer || matrix_row_is_integral(solver, row)) {
      if (! simplex_dsolver_add_row(solver, dioph, i, row)) {
#if 0
	// row i is not integer feasible (GCD test failed)
	if (trace != NULL) {
	  fprintf(trace, "\nUnsat row detected\n");
	  dsolver_print_rows(trace, dioph);
	  dsolver_print_status(trace, dioph);
	  fclose(trace);
	}
#endif
	build_gcd_conflict(solver, row);
	return false;
      }
    }
  }
  
  // run the diophantine solver
  dsolver_simplify(dioph);
  feasible = dsolver_is_feasible(dioph);

#if 0
  if (trace != NULL) {
    fprintf(trace, "\n*** Diophantine system ***\n");
    dsolver_print_elim_rows(trace, dioph);
    fprintf(trace, "\n");
    dsolver_print_main_rows(trace, dioph);
    fprintf(trace, "\n");
    dsolver_print_sol_rows(trace, dioph);
    fprintf(trace, "\n");
    dsolver_print_status(trace, dioph);
    fprintf(trace, "\n");
  }
#endif

  if (feasible) {
    dsolver_build_general_solution(dioph);

#if 0
    if (trace != NULL) {
      dsolver_print_gen_solution(trace, dioph);
      fprintf(trace, "\n");
      dsolver_build_solution(dioph);
      dsolver_print_solution(trace, dioph);
      fprintf(trace, "\n\n*** Bounds ***\n");
      print_simplex_bounds2(trace, solver);
      fprintf(trace, "\n");
    }
#endif

    feasible = strengthen_integer_bounds(solver, dioph);

#if 0
    if (trace != NULL) {
      fprintf(trace, "\n\n*** Strengthened bounds ***\n");
      print_simplex_bounds2(trace, solver);
      fprintf(trace, "\n");

      if (feasible) {
	fprintf(trace, "\nFeasible after bound strengthening\n");
	if (solver->recheck) {
	  fprintf(trace, "Recheck required\n");
	}
      } else {
	fprintf(trace, "\nInfeasible after bound strengthening\n");	
      }

      fclose(trace);
    }
#endif 

  } else {
    // UNSAT: print the explanation
    v = &solver->aux_vector;
    assert(v->size == 0);
    dsolver_unsat_rows(dioph, v);

#if 0
    if (trace != NULL) {
      fprintf(trace, "\n*** Conflict rows ***\n");
      n = v->size;
      for (i=0; i<n; i++) {
	r = v->data[i];
	row = matrix->row[r];
	fprintf(trace, "  row[%"PRId32"]: ", r);
	print_simplex_row(trace, solver, row);
	fprintf(trace, "\n");
	fclose(trace);
      }
    }
#endif

    build_dsolver_conflict(solver, v);
    ivector_reset(v);
  }

  return feasible;
}



#if 0
/*
 * Create and open a trace file:
 * - name = final<x>.dmp
 */
static FILE *open_final_trace(simplex_solver_t *solver) {
  char name[30];

  if (solver->stats.num_make_intfeasible < 0) {
    sprintf(name, "final%"PRIu32".dmp", solver->stats.num_make_intfeasible);
    return fopen(name, "w");
  } else {
    return NULL;
  }
}

#endif

/*
 * For testing: run dsolver_check and keep a trace in a file
 */
static bool simplex_dsolver_final_check(simplex_solver_t *solver) {
  //  FILE *trace;
  dsolver_t *dioph;
  matrix_t *matrix;
  row_t *row;
  ivector_t *v;
  uint32_t i, n;
  // int32_t r;
  bool pure_integer;
  bool feasible;

#if DEBUG
  check_assignment(solver);
#endif

#if 0
  trace = open_final_trace(solver);
  if (trace != NULL) {
    fprintf(trace, "Final check using diophantine solver\n");   
  }
#endif

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
#if 0
	if (trace != NULL) {
	  fprintf(trace, "\nUnsat row detected\n");
	  dsolver_print_rows(trace, dioph);
	  dsolver_print_status(trace, dioph);
	  fclose(trace);
	}
#endif
	build_gcd_conflict(solver, row);
	return false;
      }
    }
  }

  solver->stats.num_dioph_checks ++;
  
  // run the diophantine solver
  dsolver_simplify(dioph);
  feasible = dsolver_is_feasible(dioph);

#if 0
  if (trace != NULL) {
    fprintf(trace, "\n*** Solved system ***\n");
    dsolver_print_elim_rows(trace, dioph);
    fprintf(trace, "\n");
    dsolver_print_main_rows(trace, dioph);
    fprintf(trace, "\n");
    dsolver_print_sol_rows(trace, dioph);
    fprintf(trace, "\n");
    dsolver_print_status(trace, dioph);
    fprintf(trace, "\n");
  }
#endif

  if (feasible) { 
    dsolver_build_general_solution(dioph);

#if 0
    if (trace != NULL) {
      dsolver_print_gen_solution(trace, dioph);
      fprintf(trace, "\n*** Bounds ***\n");
      print_simplex_bounds2(trace, solver);
      fprintf(trace, "\n");
    }
#endif

    feasible = strengthen_integer_bounds(solver, dioph);

#if 0
    if (trace != NULL) {
      fprintf(trace, "\n\n*** Strengthened bounds ***\n");
      print_simplex_bounds2(trace, solver);
      fprintf(trace, "\n");

      if (feasible) {
	fprintf(trace, "\nFeasible after bound strengthening\n");
	if (solver->recheck) {
	  fprintf(trace, "Recheck required\n");
	}
      } else {
	fprintf(trace, "\nInfeasible after bound strengthening\n");	
      }

      fclose(trace);
    }
#endif 


  } else {
    // UNSAT: print the explanation
    v = &solver->aux_vector;
    assert(v->size == 0);
    dsolver_unsat_rows(dioph, v);

#if 0
    if (trace != NULL) {
      fprintf(trace, "\n*** Conflict rows ***\n");
      n = v->size;
      for (i=0; i<n; i++) {
	r = v->data[i];
	row = matrix->row[r];
	fprintf(trace, "  row[%"PRId32"]: ", r);
	print_simplex_reduced_row(trace, solver, row);
	fprintf(trace, "\n");
      }
      fclose(trace);
    }
#endif

    build_dsolver_conflict(solver, v);
    ivector_reset(v);
  }
  
  return feasible;
}



/*
 * FINAL CHECK
 */

/*
 * Check whether the current set of constraints is integer feasible
 * - return true if it is
 * - if it is not, do something about it and return false.
 * - the system must be feasible (in the reals)
 */
static bool simplex_make_integer_feasible(simplex_solver_t *solver) {
  ivector_t *v;
  thvar_t x;


#if TRACE_BB
  printf("\n---> make integer feasible [dlevel = %"PRIu32", decisions = %"PRIu64"]: %"PRId32
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

  // move non-integer variables to the basis
  if (simplex_is_mixed_system(solver)) {
    make_integer_vars_nonbasic(solver);
  }
  // assign an integer value to all non-basic variables
  if (! assign_integers_to_nonbasic_vars(solver)) {
    abort();
  }

#if DEBUG
  check_assignment(solver);
  check_vartags(solver);
#endif

  // check for unsatisfiability using dsolver
  solver->recheck = false;
  if (! simplex_dsolver_final_check(solver)) {
    // unsat detected by diophantine solver

#if TRACE_BB
    printf("---> unsat by diophantine solver\n");
    fflush(stdout);
#endif
    
    return false;
  } else if (solver->recheck) {
    /*
     * need to recheck feasibility 
     */
    simplex_fix_nonbasic_assignment(solver);
    if (! simplex_make_feasible(solver) ) {

#if TRACE_BB
      printf("---> unsat after recheck\n");
      fflush(stdout);
#endif
    
      solver->stats.num_recheck_conflicts ++;
      return false;

    } else {
      // Since pivoting may have occurred we need to prepare for b&b

      // move non-integer variables to the basis
      if (simplex_is_mixed_system(solver)) {
	make_integer_vars_nonbasic(solver);
      }
      // assign an integer value to all non-basic variables
      if (! assign_integers_to_nonbasic_vars(solver)) {
	abort();
      }
    }
  }



#if 0
  // EXPERIMENT:
  // add a checkpoint so that branch atoms can be deleted
  if (! solver->integer_solving) {
    solver->integer_solving = true;
    assert(solver->stats.num_atoms == solver->atbl.natoms);
    smt_checkpoint(solver->core);
  }
#endif


  /*
   * At this point: no unsat detected. But bounds may have been strengthened
   * All integer basic variables have an integer value.
   */

  // collect the integer basic variables that have a non-integer value
  v = &solver->aux_vector;
  assert(v->size == 0);
  collect_non_integer_basic_vars(solver, v);

#if TRACE_BB
  printf("---> %"PRIu32" branch candidates\n", v->size);
#endif

  if (v->size == 0) {
    return true;
  }

  x = select_branch_variable(solver, v);
  ivector_reset(v);

  assert(x != null_thvar);
  create_branch_atom(solver, x);

  return false;
}




/*
 * DELETE BRANCH ATOMS VIA CHECKPOINTS MECHANISM
 */

/*
 * Delete branch atoms when backtracking beyond the checkpoint 
 */
static void simplex_delete_branch_atom(simplex_solver_t *solver, void *atom) {
  int32_t id;
  thvar_t x;

  assert(solver->integer_solving);
  id = arithatom_tagged_ptr2idx(atom);
#if TRACE_BB
  printf("---> delete branch atom: ");
  print_simplex_atom(stdout, solver, id);
  printf("\n");
#endif
  x = var_of_atom(arith_atom(&solver->atbl, id));
  detach_atom_from_arith_var(&solver->vtbl, x, id);
}


/*
 * End of atom deletion
 */
static void simplex_end_atom_deletion(simplex_solver_t *solver) {
  assert(solver->integer_solving);
#if TRACE_BB
  printf("---> end delete branch atom: keeping %"PRIu32" atoms out of %"PRIu32"\n", 
	 solver->stats.num_atoms, solver->atbl.natoms);
#endif
  arith_atomtable_remove_atoms(&solver->atbl, solver->stats.num_atoms);
  solver->integer_solving = false;
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
 */
static void record_egraph_eq_conflict(simplex_solver_t *solver, int32_t k, thvar_t x1, thvar_t x2) {
  ivector_t *v;
  eterm_t t1, t2;

  v = &solver->expl_vector;
  ivector_reset(v);
  simplex_explain_bound(solver, k, v); // conjuntion of literals that imply k

  t1 = arith_var_eterm(&solver->vtbl, x1);
  t2 = arith_var_eterm(&solver->vtbl, x2);
  egraph_explain_term_eq(solver->egraph, t1, t2, v); // add literals that imply (x1 == x2)

  // turn v into a conflict clause
  convert_expl_to_clause(v);
  ivector_push(v, null_literal); // end-marker

  record_theory_conflict(solver->core, v->data);

  solver->stats.num_conflicts ++;

#if TRACE_THEORY
  trace_simplex_egraph_eq_conflict(k, x1, x2, v->data);
#endif
}


/*
 * Process (x1 == x2)
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become equal in the egraph
 * - return false if there's a conflict, true otherwise
 */
static bool simplex_process_var_eq(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  rational_t *c;
  literal_t l;
  thvar_t y;
  int32_t k, cmp_lb, cmp_ub;

  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2) && x1 != x2);

#if TRACE || 1
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

#if TRACE || 1
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
      record_egraph_eq_conflict(solver, k, x1, x2);

#if TRACE || 1
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
      record_egraph_eq_conflict(solver, k, x1, x2);

#if TRACE || 1
      printf("     conflict with bound ");
      print_simplex_bound(stdout, solver, k);
      printf("\n");
#endif
    
      return false;
    }
  }

  if (cmp_lb < 0) {
    push_lb_egraph(solver, y, c, x1, x2);
  }
  if (cmp_ub > 0) {
    push_ub_egraph(solver, y, c, x1, x2);
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
 */
static void simplex_trichotomy_lemma(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
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

#if TRACE || 1
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
  if (e->flag == NEW_CACHE_ELEM) {
    e->flag = ACTIVE_ARITH_LEMMA; 

    /*
     * create the egraph equality l := (eq t1 t2)
     */
    t1 = arith_var_eterm(&solver->vtbl, x1);
    t2 = arith_var_eterm(&solver->vtbl, x2);
    assert(t1 != null_eterm && t2 != null_eterm);
    l = egraph_make_simple_eq(solver->egraph, pos_occ(t1), pos_occ(t2));

#if TRACE || 1
    printf("     trichotomy lemma: egraph atom: ");
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
      // x1 = x2 is false: add (not (eq t1 t2)))) as an axiom for the egraph
#if TRACE || 1
      printf("     reduced to 1 != 0\n");
      printf("     add unit clause: ");
      print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
      printf("\n");
#endif
      add_unit_clause(solver->core, not(l));
      reset_poly_buffer(&solver->buffer);

    } else {
      assert(l0 != true_literal); // since x1 != x2

      // get y and c such that y = c is equivalent to x1 = x2
      y = decompose_and_get_dynamic_var(solver); // store c in solver->constant and reset buffer
      c = &solver->constant;

      l1 = create_pos_atom(solver, y, c);
      l2 = create_neg_atom(solver, y, c);

#if TRACE || 1
      printf("     reduced to: ");
      print_simplex_var(stdout, solver, y);
      printf(" != ");
      q_print(stdout, c);
      printf("\n");
      if (! arith_var_is_free(&solver->vtbl, y)) {
	printf("     ");
	print_simplex_vardef(stdout, solver, y);	
      }
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
      add_binary_clause(solver->core, not(l), not(l1));
      add_binary_clause(solver->core, not(l), not(l2));
    }
  }
}



#if 0

// DISABLE THIS: DEAL WITH TRICHOTOMY IN RECONCILE MODEL

/*
 * Process (x1 != x2)
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 * - this function is called when t1 and t2 become distinct in the egraph
 * - it creates a trichotomy clause equivalent to 
 *         ((eq t2 t2) or (x1 - x2 > 0) or (x1 - x2 < 0))
 */
static void simplex_process_var_diseq(simplex_solver_t *solver, thvar_t x1, thvar_t x2, composite_t *hint) {
  cache_t *cache;
  cache_elem_t *e;
  aprop_egraph_diseq_t *expl;
  rational_t *c;
  thvar_t y;
  eterm_t t1, t2, aux;
  literal_t l, l0, l1, l2;

  assert(x1 != x2);

#if TRACE
  printf("\n---> Simplex: process egraph disequality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" != ");
  print_simplex_var(stdout, solver, x2);
  printf(" [dlevel = %"PRIu32"]\n", solver->core->decision_level);
#endif

  t1 = arith_var_eterm(&solver->vtbl, x1);
  t2 = arith_var_eterm(&solver->vtbl, x2);

  // normalize: we want t1 <= t2
  if (t2 < t1) {
    aux = t1; t1 = t2; t2 = aux;
  }

  l = egraph_make_eq(solver->egraph, pos_occ(t1), pos_occ(t2));  // egraph atom (eq t1 t2)

#if TRACE
  printf("---> corresponding egraph atom: ");
  print_egraph_atom_of_literal(stdout, solver->egraph, l);
  printf("\n");
#endif

  cache = simplex_get_cache(solver);
  e = cache_get(cache, TRICHOTOMY_LEMMA, t1, t2);
  if (e->flag == NEW_CACHE_ELEM) {
    // create the trichotomy clause
    e->flag = ACTIVE_ARITH_LEMMA; 

    // build p such that p=0 is equivalent to (x1 = x2)
    // p is stored in solver->buffer
    // l0 = simplification code
    l0 = simplify_dynamic_vareq(solver, x1, x2);

    if (l0 == false_literal) {
      // x1 = x2 is false: add (not (eq t1 t2)))) as an axiom
#if TRACE
      printf("---> constraint: 1 != 0\n");
      printf("---> add unit clause: ");
      print_egraph_atom_of_literal(stdout, solver->egraph, not(l));
      printf("\n");
#endif
      add_unit_clause(solver->core, not(l));
      reset_poly_buffer(&solver->buffer);

    } else {
      assert(l0 != true_literal);

      // get y and c such that y = c is equivalent to x1 = x2
      y = decompose_and_get_dynamic_var(solver); // store c in solver->constant and reset buffer
      c = &solver->constant;

      l1 = create_pos_atom(solver, y, c);
      l2 = create_neg_atom(solver, y, c);

#if TRACE
      printf("---> constraint: ");
      print_simplex_var(stdout, solver, y);
      printf(" != ");
      q_print(stdout, c);
      printf("\n");
      printf("---> add trichotomy clause:\n");
      printf("     (OR ");
      print_egraph_atom_of_literal(stdout, solver->egraph, l);
      printf(" ");
      print_simplex_atom_of_literal(stdout, solver, l1);
      printf(" ");
      print_simplex_atom_of_literal(stdout, solver, l2);
      printf(")\n");
#endif

      add_ternary_clause(solver->core, l, l1, l2);
    }
  }

  /*
   * propagate (not l) to the core if it's not already false
   * TODO: check whether it's safe to skip this
   */
  if (literal_value(solver->core, l) == VAL_UNDEF) {
#if TRACE
    printf("---> propagating ");
    print_literal(stdout, not(l));
    printf("\n");
#endif

    expl = make_egraph_diseq_prop_object(solver, x1, x2, hint);
    propagate_literal(solver->core, not(l), expl);
    solver->stats.num_props ++;
  }

  assert(literal_value(solver->core, l) == VAL_FALSE);
}


/*
 * Assert that all variables a[0] ... a[n-1] are pairwise distinct
 * - they are attached to egraph terms t[0] ... t[n-1]
 * - the function is called when (distinct t[0] ... t[n-1]) is asserted in the egraph
 * - always return true: conflict are detected later
 */
static void simplex_process_var_distinct(simplex_solver_t *solver, uint32_t n, thvar_t *a, composite_t *hint) {
  uint32_t i, j;

  for (i=0; i<n-1; i++) {
    for (j=i+1; j<n; j++) {
      simplex_process_var_diseq(solver, a[i], a[j], hint);
    }
  }
}

#endif


/*
 * Process (x1 != x2)
 * - x1 and x2 are two variables attached to two egraph terms t1 and t2
 */
static void simplex_process_var_diseq(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2) && x1 != x2);

#if TRACE || 1
  printf("---> Simplex: egraph disequality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" != ");
  print_simplex_var(stdout, solver, x2);
  printf(" [dlevel = %"PRIu32"]\n", solver->core->decision_level);
  if (! arith_var_is_free(&solver->vtbl, x1)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x1);
  }
  if (! arith_var_is_free(&solver->vtbl, x2)) {
    printf("     ");
    print_simplex_vardef(stdout, solver, x2);
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

  a = eassertion_queue_start(&solver->egraph_queue);
  end = eassertion_queue_end(&solver->egraph_queue);

  while (a < end) {
    switch (eassertion_get_kind(a)) {
    case EGRAPH_VAR_EQ:
      if (! simplex_process_var_eq(solver, a->var[0], a->var[1])) {
	reset_eassertion_queue(&solver->egraph_queue);
	return false;
      }
      break;
    case EGRAPH_VAR_DISEQ:
      simplex_process_var_diseq(solver, a->var[0], a->var[1]);
      break;
    case EGRAPH_VAR_DISTINCT:
      //      simplex_process_var_distinct(solver, eassertion_get_arity(a), a->var, a->hint);
      break;
    default:
      assert(false);
      break;
    }
    a = eassertion_next(a);
  }

  reset_eassertion_queue(&solver->egraph_queue);
  return true;
}



/**************************
 *  INTENALIZATION START  *
 *************************/

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

  // compute the initial assignment
  simplex_init_assignment(solver);
  feasible = simplex_make_feasible(solver);
  if (! feasible) goto done;
  solver->last_conflict_row = -1;

  // integer solving flags
  solver->integer_solving = false;
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

#if YEXPORT
  export_state(solver);
#endif

#if 0
  //  printf("\n\n*** SIMPLEX START ***\n");
  printf("==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  //  printf("\n==== Assignment ====\n");
  //  print_simplex_assignment(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  //  printf("\n==== Atoms ====\n");
  //  print_simplex_atoms(stdout, solver);
  //  printf("\n");
#endif
  return;
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
    // start seach has not been called yet
    assert(solver->decision_level == solver->base_level);
    if (solver->unsat_before_search) {
      record_empty_theory_conflict(solver->core);
      feasible = false;
      goto done;
    }

    feasible = simplex_process_assertions(solver);
    goto done;
  }
  
  assert(! solver->unsat_before_search);

  if (solver->assertion_queue.prop_ptr < solver->assertion_queue.top || 
      eassertion_queue_is_nonempty(&solver->egraph_queue)) {

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
    
    /*
     * Theory propagation
     * - propagation may strengthen bounds on integer variables,
     *   which may detect a conflict or require a new call to
     *   make_feasible.
     */
    if (simplex_option_enabled(solver, SIMPLEX_PROPAGATION)) {
      solver->recheck = false;

      feasible = simplex_do_propagation(solver);
      if (! feasible) goto done;

      if (solver->recheck) {
	simplex_fix_nonbasic_assignment(solver);
	feasible = simplex_make_feasible(solver);
	if (! feasible) goto done;
      } else {
	// implied bounds don't require fixing the assignment
	solver->bstack.fix_ptr = solver->bstack.top;
      }

#if DEBUG
      check_vartags(solver);
      check_assignment(solver);
      check_integer_bounds(solver);
#endif
    }

    // propagate to literals
    simplex_literal_propagation(solver);

  }

  /*
   * EXPERIMENTAL: periodically test for integer feasibility
   */
  if (solver->check_counter -- <= 0) {
    if (simplex_has_integer_vars(solver)) {
      solver->check_counter = solver->check_period;

      feasible = simplex_assignment_integer_valid(solver);
      if (feasible) goto done;

      solver->recheck = false;
      if (solver->core->stats.decisions == 0) {
	feasible = simplex_dsolver_check_at_start(solver);
      } else {
	//	printf(".");
	//	fflush(stdout);
	feasible = simplex_dsolver_check(solver);
      }
      if (! feasible) {
	//	printf("D");
	//	fflush(stdout);
	goto done;
      }

      if (solver->recheck) {
	simplex_fix_nonbasic_assignment(solver);
	feasible = simplex_make_feasible(solver);
	if (! feasible) {
	  //	  printf("R");
	  //	  fflush(stdout);
	  goto done;
	}
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

#if 1
  if (simplex_has_integer_vars(solver)) {
    if (simplex_make_integer_feasible(solver)) {
      return FCHECK_SAT;
    } else {
      printf("---> not integer feasible\n");
      return FCHECK_CONTINUE;
    }
  } else {
    assert(simplex_assignment_integer_valid(solver));
    return FCHECK_SAT;
  }
#endif

#if 0
  if (! simplex_assignment_integer_valid(solver)) {
    printf("---> INCOMPLETENESS: simplex assignment is not integer feasible\n");
    fflush(stdout);
    return FCHECK_UNKNOWN;
  } else {
    return FCHECK_SAT;
  }
#endif
}




/*****************************
 *  INCREASE DECISION LEVEL  *
 ***************************/

void simplex_increase_decision_level(simplex_solver_t *solver) {
  uint32_t nb, na;

  nb = solver->bstack.top;
  na = solver->assertion_queue.top;
  arith_push_undo_record(&solver->stack, nb, na);
  solver->decision_level ++;

  // new scope in arena
  arena_push(&solver->arena);

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
 */
void simplex_backtrack(simplex_solver_t *solver, uint32_t back_level) {
  arith_bstack_t *bstack;
  arith_vartable_t *vtbl;
  arith_undo_record_t *undo;
  int32_t *a;
  uint32_t i, n;
  thvar_t x;
  int32_t k;

#if TRACE
  printf("---> Simplex: backtracking to level %"PRIu32"\n", back_level);
#endif

  assert(solver->base_level <= back_level && back_level < solver->decision_level);

  /*
   * stack->data[back_level + 1] = record created on entry to back_level + 1
   */
  assert(back_level + 1 < solver->stack.top);
  undo = solver->stack.data + back_level + 1;

  vtbl = &solver->vtbl;
  bstack = &solver->bstack;

  /*
   * Remove the bounds and fix the lb/ub tags
   */
  i = bstack->top;

  /*
   * Bounds in bstack[fix_ptr ... top-1] have not been visited by fix_nonbasic_assignment
   * - so variable assigment and tags are what they were before 
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

#if DEBUG
  check_vartags(solver);
  check_nonbasic_assignment(solver);
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
  uint32_t nv, na, nr, nx, pa, pb;

  assert(solver->decision_level == solver->base_level && 
	 solver->save_rows);

  nv = solver->vtbl.nvars;
  na = solver->atbl.natoms;
  nr = solver->saved_rows.size;
  nx = solver->saved_vars.size;
  pa = solver->assertion_queue.prop_ptr;
  pb = solver->bstack.prop_ptr;
  arith_trail_save(&solver->trail_stack, nv, na, nr, nx, pa, pb);

  if (solver->cache != NULL) {
    cache_push(solver->cache);
  }

  solver->base_level ++;
  simplex_increase_decision_level(solver);
}


/*
 * Return to the previous base level
 */
void simplex_pop(simplex_solver_t *solver) {
  arith_trail_t *top;

  assert(solver->base_level > 0 && 
	 solver->base_level == solver->decision_level && 
	 solver->save_rows);

  solver->base_level --;
  simplex_backtrack(solver, solver->base_level);

  top = arith_trail_top(&solver->trail_stack);
  arith_vartable_remove_vars(&solver->vtbl, top->nvars);
  arith_atomtable_remove_atoms(&solver->atbl, top->natoms);  
  delete_saved_rows(&solver->saved_rows, top->nsaved_rows);
  deactivate_saved_vars(solver, top->nsaved_vars);

  if (solver->cache != NULL) {
    cache_pop(solver->cache);
  }

  // restore the propagation pointers
  solver->bstack.prop_ptr = top->bound_ptr;
  solver->assertion_queue.prop_ptr = top->assertion_ptr;

  // remove trail object
  arith_trail_pop(&solver->trail_stack);

  // delete the tableau
  simplex_reset_tableau(solver);
}


/*
 * Reset to the empty solver
 */
void simplex_reset(simplex_solver_t *solver) {
  uint32_t n;

  solver->base_level = 0;
  solver->decision_level = 0;
  solver->unsat_before_search = false;

  reset_simplex_statistics(&solver->stats);

  if (solver->freshval != NULL) {
    simplex_free_freshval_set(solver->freshval);
    solver->freshval = NULL;
  }

  n = solver->vtbl.nvars;
  if (solver->value != NULL) {
    free_rational_array(solver->value, n);
    solver->value = NULL;
  }
  q_clear(&solver->epsilon);
  q_clear(&solver->factor);

  reset_arith_atomtable(&solver->atbl);  
  reset_arith_vartable(&solver->vtbl);

  reset_matrix(&solver->matrix);
  solver->tableau_ready = false;
  solver->matrix_ready = true;

  solver->last_conflict_row = -1;
  solver->recheck = false;
  solver->integer_solving = false;

  if (solver->dsolver != NULL) {
    reset_dsolver(solver->dsolver);
  }

  if (solver->cache != NULL) {
    reset_cache(solver->cache);
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
  ivector_reset(&solver->saved_vars);

  reset_elim_matrix(&solver->elim);
  reset_fvar_vector(&solver->fvars);

  reset_poly_buffer(&solver->buffer);  
  q_clear(&solver->constant);
  q_clear(&solver->aux);
  q_clear(&solver->gcd);
  xq_clear(&solver->bound);
  xq_clear(&solver->delta);

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
      printf("  (true)\n");
    } else {
      printf("  (false)\n");
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
 */
void simplex_expand_explanation(simplex_solver_t *solver, literal_t l, aprop_header_t *expl, ivector_t *v) {
  aprop_egraph_diseq_t *diseq;

  switch (expl->tag) {
  case APROP_BOUND:
    simplex_explain_bound(solver, ((aprop_t *) expl)->bound, v);
    break;

  case APROP_EGRAPH_DISEQ:
    diseq = (aprop_egraph_diseq_t *) expl;
    egraph_expand_diseq_pre_expl(solver->egraph, &diseq->d, v);
    break;

  default:
    abort();
    break;
  }
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

  b = false;
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

  if (simplex_eval_atom(solver, atom)) {
    return pos_lit(v);
  } else {
    return neg_lit(v);
  }
}




/**********************
 * DELETE THE SOLVER  *
 *********************/

void delete_simplex_solver(simplex_solver_t *solver) {
  uint32_t n;

  if (solver->freshval != NULL) {
    simplex_free_freshval_set(solver->freshval);
    solver->freshval = NULL;
  }

  n = solver->vtbl.nvars;
  if (solver->value != NULL) {
    free_rational_array(solver->value, n);
    solver->value = NULL;
  }
  q_clear(&solver->epsilon);
  q_clear(&solver->factor);


  delete_arith_atomtable(&solver->atbl);
  delete_arith_vartable(&solver->vtbl);

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
 */
void simplex_assert_var_eq(simplex_solver_t *solver, thvar_t x1, thvar_t x2) {
  assert(arith_var_has_eterm(&solver->vtbl, x1) && arith_var_has_eterm(&solver->vtbl, x2));
  eassertion_push_eq(&solver->egraph_queue, x1, x2);

#if TRACE
  printf("---> Simplex: received egraph equality: ");
  print_simplex_var(stdout, solver, x1);
  printf(" = ");
  print_simplex_var(stdout, solver, x2);
  printf("\n---> ");
  print_simplex_vardef(stdout, solver, x1);
  printf("---> ");
  print_simplex_vardef(stdout, solver, x2);
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
static inline bool is_root_var(simplex_solver_t *solver, thvar_t x) {
  egraph_t *egraph;
  eterm_t t;

  t = arith_var_get_eterm(&solver->vtbl, x);
  egraph = solver->egraph;
  return (t != null_eterm) && 
    (egraph_class_thvar(egraph, egraph_term_class(egraph, t)) == x);
}


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

#if 0
  printf("\n\n*** SIMPLEX RECONCILE ***\n");
  printf("==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Assignment ====\n");
  print_simplex_assignment(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
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
	simplex_trichotomy_lemma(solver, x, i);
	neq ++;
	if (neq == max_eq) break;
      }
    }
  }

  delete_int_hclass(&hclass);

  return neq;
}




/************************
 *  MODEL CONSTRUCTION  *
 ***********************/

/*
 * Ajust epsilon to ensure concretization of q1 <= concretization of q2 
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
 * Adjust solver->epsilon to ensure that rational value of x 
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

  b = false;
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
    case VAL_UNDEF:
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
 * Check that the model is valid
 */
static bool good_simplex_model(simplex_solver_t *solver) {
  return equations_hold_in_model(solver) && assertions_hold_in_model(solver) && 
    model_is_integer_feasible(solver);
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
 * Free the model (and the freshval set if present)
 */
void simplex_free_model(simplex_solver_t *solver) {
  uint32_t n;

  assert(solver->value != NULL);
  n = solver->vtbl.nvars;
  free_rational_array(solver->value, n);
  solver->value = NULL;
  q_clear(&solver->epsilon);
  q_clear(&solver->factor);


  if (solver->freshval != NULL) {
    simplex_free_freshval_set(solver->freshval);
    solver->freshval = NULL;
  }
}


/*
 * Value of variable x in the model
 */
bool simplex_value_in_model(simplex_solver_t *solver, int32_t x, rational_t *v) {
  assert(solver->value != NULL && 0 <= x && x < solver->vtbl.nvars);
  q_set(v, solver->value + x);
  return true;
}



/*
 * Initialize the freshval set based on the values used in solver->value
 */
static void simplex_init_freshval(simplex_solver_t *solver) {
  simplex_freshval_t *set;
  rational_t *q;
  uint32_t i, n;
  int32_t x;

  assert(solver->value != NULL && solver->freshval != NULL);

  set = solver->freshval;
  n = solver->vtbl.nvars;
  for (i=0; i<n; i++) {
    q = solver->value + i; // value of i
    if (q_is_integer(q)) {
      if (q_lt(&set->max_used, q)) {
	// value[i] > max_used: update max_used
	q_set(&set->max_used, q);

      } else {
	q_normalize(q); // just to be safe
	if (q_is_smallint(q)) {
	  x = q_get_smallint(q);
	  if (0 <= x && x < SIMPLEX_NVAL) {
	    set_bit(set->used_val, x);	    
	  } else if (set->low <= x && x < set->high) {
	    // Heuristic: reduce [low, high] to [x+1, high] or [low, x]
	    // whichever is larger
	    if (x > (set->high + set->low)/2) {
	      set->high = x;
	    } else {
	      set->low = x + 1;
	    }
	  }
	}
      }
    }
  }

}


/*
 * Return an integer in freshval set and remove it from the set
 * - store the integer in array v
 */
static void simplex_get_freshval(simplex_freshval_t *set, rational_t *v) {
  int32_t i;

  i = set->used_val_idx;
  assert(0 <= i && i <= SIMPLEX_NVAL);

  if (i < SIMPLEX_NVAL) {
    do {
      if (! tst_bit(set->used_val, i)) {
	// i can be used
	set_bit(set->used_val, i);
	q_set32(v, i);
	set->used_val_idx = i+1;
	return;
      }
      i ++;

    } while (i < SIMPLEX_NVAL);
    
    // nothing found in the used_val interval
    set->used_val_idx = SIMPLEX_NVAL;
  }

  assert(SIMPLEX_NVAL <= set->low && set->low <= set->high && 
	 set->high <= SIMPLEX_HVAL);

  i = set->low;
  if (i < set->high) {
    q_set32(v, i); 
    set->low = i+1;
  } else {
    assert(q_is_integer(&set->max_used));
    q_add_one(&set->max_used);
    q_set(v, &set->max_used);
  }

}


/*
 * Create a unique value: it's always an integer
 */
static bool simplex_fresh_value(simplex_solver_t *solver, rational_t *v, bool is_int) {
  simplex_freshval_t *set;

  assert(solver->value != NULL);
  set = solver->freshval;
  if (set == NULL) {
    set = simplex_new_freshval_set();
    solver->freshval = set;
    simplex_init_freshval(solver);
  }

  simplex_get_freshval(set, v);

  return true;
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

  (create_arith_atom_fun_t) simplex_create_eq_atom,
  (create_arith_atom_fun_t) simplex_create_ge_atom,
  (create_arith_vareq_atom_fun_t) simplex_create_vareq_atom,

  (assert_arith_axiom_fun_t) simplex_assert_eq_axiom,
  (assert_arith_axiom_fun_t) simplex_assert_ge_axiom,
  (assert_arith_vareq_axiom_fun_t) simplex_assert_vareq_axiom,
  (assert_arith_cond_vareq_axiom_fun_t) simplex_assert_cond_vareq_axiom,

  (attach_eterm_fun_t) simplex_attach_eterm,
  (eterm_of_var_fun_t) simplex_eterm_of_var,

  (build_model_fun_t) simplex_build_model,
  (free_model_fun_t) simplex_free_model,
  (arith_val_in_model_fun_t) simplex_value_in_model,
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
};

static th_smt_interface_t simplex_smt = {
  (assert_fun_t) simplex_assert_atom,
  (expand_expl_fun_t) simplex_expand_explanation,
  (select_pol_fun_t) simplex_select_polarity,
  (del_atom_fun_t) simplex_delete_branch_atom,
  (end_del_fun_t) simplex_end_atom_deletion,
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
  NULL, // no need for expand_th_explanation
  (reconcile_model_fun_t) simplex_reconcile_model,
  (attach_to_var_fun_t) simplex_attach_eterm,
  (get_eterm_fun_t) simplex_eterm_of_var,
};


static arith_egraph_interface_t simplex_arith_egraph = {
  (make_arith_var_fun_t) simplex_create_var,
  (arith_val_fun_t) simplex_value_in_model,
  (arith_fresh_val_fun_t) simplex_fresh_value,
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






/*****************
 *  FOR TESTING  *
 ****************/

#if 0

static uint32_t number_of_mpqs(row_t *row) {
  uint32_t i, n, k;

  k = 0;
  n = row->size;
  for (i=0; i<n; i++) {
    if (row->data[i].coeff.den == 0) k++;
  }
  return k;
}

void simplex_print_matrix_size(simplex_solver_t *solver) {
  matrix_t *matrix;
  column_t *column;
  row_t *row;
  uint32_t i, n;
  uint32_t ncells, nelems, nqs;

  matrix = &solver->matrix;
  printf("\n---> Matrix size\n");
  printf("   %"PRIu32" rows\n", matrix->nrows);
  printf("   %"PRIu32" columns\n", matrix->ncolumns);

  ncells = 0;
  nelems = 0;
  n = matrix->ncolumns;
  for (i=0; i<n; i++) {
    column = matrix->column[i];
    if (column != NULL) {
      ncells += column->capacity;
      nelems += column->nelems;
    }
  }
  printf("  column cells: cap = %"PRIu32", used = %"PRIu32"\n", ncells, nelems);

  ncells = 0;
  nelems = 0;
  nqs = 0;
  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (row != NULL) {
      ncells += row->capacity;
      nelems += row->nelems;
      nqs += number_of_mpqs(row);
    }
  }

  printf("  row cells: cap = %"PRIu32", used = %"PRIu32"\n", ncells, nelems);
  printf("  gmp numbers in the matrix: %"PRIu32"\n", nqs);  


  n = matrix->ncolumns;
  for (i=0; i<n; i++) {
    column = matrix->column[i];
    if (column != NULL) {
      printf("   column[%"PRIu32"]: cap = %"PRIu32", used = %"PRIu32"\n", i, column->capacity, column->nelems);
    }
  }
  printf("\n");

  n = matrix->nrows;
  for (i=0; i<n; i++) {
    row = matrix->row[i];
    if (row != NULL) {
      printf("   row[%"PRIu32"]: cap = %"PRIu32", used = %"PRIu32"\n", i, row->capacity, row->nelems);
    }
  }
  printf("\n");

}

#endif


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

#if 0
// NOT USED

static void print_egraph(FILE *f, egraph_t *egraph) {
  fprintf(f, "\n==== Egraph terms ====\n");
  print_egraph_terms(f, egraph);
  fprintf(f, "\n==== Classes ====\n");
  print_egraph_root_classes_details(f, egraph);
  fprintf(f, "\n==== Egraph atoms ====\n");
  print_egraph_atoms(f, egraph);  
}


static void dump_final_state(simplex_solver_t *solver) {
  FILE *dump;

  dump = fopen("final.dmp", "w");
  if (dump == NULL) return;

  if (solver->egraph != NULL) {
    fprintf(dump, "==== Egraph terms ====\n");
    print_egraph_terms(dump, solver->egraph);
    fprintf(dump, "\n");
  }
  fprintf(dump, "==== Simplex variables ====\n");
  print_simplex_vars(dump, solver);
  fprintf(dump, "\n==== Assignment ====\n");
  print_simplex_assignment(dump, solver);
  fprintf(dump, "\n==== Bounds  ====\n");
  print_simplex_bounds(dump, solver);
  fprintf(dump, "\n==== Atoms ====\n");
  print_simplex_atoms(dump, solver);

  fclose(dump);
}
#endif

#endif


#if YEXPORT

static void export_state(simplex_solver_t *solver) {
  FILE *f;

  f = fopen("simplex.ys", "w");
  if (f == NULL) return;
  export_simplex(f, solver);
  fputs("\n(check)\n", f);
  fclose(f);
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
  case VAL_UNDEF:
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
    printf("---> ERROR: row[%"PRIu32"] not satified\n", r);
    fflush(stdout);
  }  
  xq_clear(&check);  
}


/*
 * Check whether all equations in matrix are satisified
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
