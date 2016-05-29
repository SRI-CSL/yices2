/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * DATA STRUCTURES FOR THE SIMPLEX SOLVER
 *
 * Version 2: simplified to attempt to get close to Yices 1 solver
 * - removed all equality atoms (x == b): they are always
 *   rewritten as (and (x <= b)  (x >= b))
 * - generate binary lemmas all the time (not optional)
 * - removed "derived bounds". All theory propagations are direct
 *   assertions of a literal in the core.
 * - added support for turning propagations into lemmas.
 * - removed trichotomy lemmas/cache
 *
 * Version 3: 2008/11/03
 * - put back the derived bounds and more general forms of bound
 *   propagation.
 * - added diophantine subsolver
 * - put back the trichotomy cache. It's now used for interfacing
 *   with the egraph.
 */

/*
 * Simplex solver:
 * - a global set of linear equalities A X = 0
 *   where A is a matrix and X is the vector of variables
 * - all atoms are of the form (x <= b) or (x >= b) where
 *   x is a variable and b is a rational constant.
 * - strict inequalities are encoded using "extended rational":
 *   an extended rational is of the form (b + c \delta) where b and c
 *   are rationals and \delta is infinitesimal.
 *
 * Variable table: (cf. arith_vartable):
 * - each variable x is stored in the simplex's variable table
 * - the table maps x to a descriptor
 * - variable 0 is always the constant (const_idx = 0)
 *   its descriptor is the rational 1/1 (kind = AVAR_CONST)
 * - for all other variables, we use only two kinds of descriptors
 *   either x is a free variable          (kind = AVAR_FREE)
 *       or x has a polynomial definition (kind = AVAR_POLY)
 *   We convert any rational constant to a constant polynomial before
 *   adding it to the variable table (i.e., we don't use kind = AVAR_CONST).
 *
 * Variable substitutions: if x's definition is a simple polynomial of
 * the form (c + b.y) then the solver always replace x by c + b.y
 * (rather than adding the row c - x + b.y = 0 to the matrix).
 *
 * Matrix/tableau:
 * - We use a two-stage approach to building the constraints A X = 0.
 * - The constraint matrix is built during formula internalization.
 *   It contains two types of rows:
 *   - variable definitions: rows of the form (x - p) == 0,
 *     where x := p is an entry in the variable table and p is not a
 *     simple polynomial
 *   - top-level assertions: rows of the form (p == 0) when p == 0
 *     is asserted at the toplevel
 * - The matrix is simplified and the tableau is constructed
 *   when start_search is called.
 *
 * The solver maintains:
 * - a variable assignment that maps X to extended rationals
 * - a queue/stack of asserted or derived constraints
 * - each constraint in the queue is either (x <= u) or (x >= l)
 *   where u and l are extended rationals
 * - each constraint has an explanation
 *
 * For each variable x, we keep track of the current lower and upper bounds for x
 *
 */

/*
 * Processing of assertions/bounds
 * -------------------------------
 * There are two stacks: a stack of assertions and a constraint (or bound) stack.
 * Assertions are arithmetic atoms or negation of arithmetic atoms. Each assertion
 * is identified by the atom id and a polarity bit (1 for negation).
 * Assertions are pushed onto the assertion stack when the core calls
 * simplex_assert_atom(.., l) where l is a literal. The bound stack maintains the
 * current lower and upper bound on each variable.
 *
 * Then simplex_propagate does the following operations:
 *
 * 1) Process_assertions: visit all assertions on the assertion stack
 *    - if an assertion i conflicts with an existing bound then a conflict is reported,
 *    and simplex_propagate exits.
 *    (Example: i is (x >= a) and current upper bound on x is smaller than a.)
 *    - if an assertion i is redundant, it's skipped.
 *    (Example: i is (x >= a) and current lower bound on x is larger than or equal to a).
 *    - otherwise, a new bound for x is pushed onto the bound stack.
 *
 * 2) If process_assertions does not detect a conflict, update the variable assignment:
 *    Visit all the constraints added to the bound-stack during process_assertions.
 *    Update the assignment to ensure that all non-basic variables are within their bounds,
 *    collect the basic variables that are not within their bounds.
 *
 * 3) Check feasibility using simplex.
 *
 * 4) Optional: search for implied bounds (simplex-propagation)
 *    If no conflict is found by step 1 or 3:
 *    - add more bounds to the bound stacks (implied bounds).
 *    - if integer variables are present, theory propagation may detect
 *      conflicts or invalidate the current assignment (i.e.. val[x] no longer
 *      between lb[x] and ub[x] because the bounds are strengthened).
 *    - if theory_propagation does not find a conflict but the current assignment is
 *      invalid, attempt to correct it: make sure all non-basic variables are within
 *      their bounds then call make_feasible again.
 *
 * 5) Find implied literals and propagate them to the core.
 *    If no conflict is found in steps 1, 3, or 4: process all the new bounds on the
 *    bound stack, and assign all literals implied by these bounds in the core.
 */


#ifndef __SIMPLEX_TYPES_H
#define __SIMPLEX_TYPES_H

#include <stdint.h>
#include <stdbool.h>
#include <setjmp.h>

#include "context/context_types.h"
#include "solvers/cdcl/gates_manager.h"
#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/diseq_stacks.h"
#include "solvers/egraph/egraph.h"
#include "solvers/egraph/egraph_assertion_queues.h"
#include "solvers/simplex/arith_atomtable.h"
#include "solvers/simplex/arith_vartable.h"
#include "solvers/simplex/diophantine_systems.h"
#include "solvers/simplex/matrices.h"
#include "solvers/simplex/offset_equalities.h"
#include "terms/extended_rationals.h"
#include "terms/poly_buffer.h"
#include "terms/polynomials.h"
#include "terms/rationals.h"
#include "utils/arena.h"
#include "utils/bitvectors.h"
#include "utils/cache.h"
#include "utils/int_heap.h"
#include "utils/int_vectors.h"
#include "utils/ptr_vectors.h"


/*******************
 *   BOUND STACK   *
 ******************/

/*
 * Each element i in the stack is a constraint of the form (x <= u) or (x >= l)
 * - x is an arithmetic variable stored in bstack->var[i]
 * - u or l is an extended rational (of the form a + b\delta) stored in bstack->bound[i]
 * - each constraint has an 8bit tag that defines what it is and how it was derived:
 *   - lower order bit = 0 means it's a lower bound (x >= l)
 *     lower order bit = 1 means it's an upper bound (x <= u)
 *   - the next two lower bits define how to explain the bound:
 *       axiom --> no explanation
 *       assertion --> explanation is a literal l
 *       derived/strengthened --> explanation is an array of literals
 *       equality propagation from the egraph --> the explanation is a pair
 *                                                of variables (v[0], v[1])
 *       new egraph explanation --> explanation is a pointer to a triple
 *        (v[0], v[1], id) where id is an egraph edge index
 *
 * - bit 7 of the tag is used as a mark when generating explanations
 * - for backtracking, pre[i] stores the previous constraint of the same type,
 *   on the same variable.
 *
 * For each variable x, we maintain a list of lower and upper bounds on x:
 * - lower_index[x] = -1 if x has no lower bound
 *   lower_index[x] = index k of the current lower bound on x in the stack otherwise
 *      then pre[k] = index of the previous lower on x, and so forth
 * - upper_index[x]: same thing for upper bounds on x
 *
 * Other components:
 * - top = top of the stack
 * - prop_ptr = index of the first constraint to check for theory propagation
 *   (bounds of index prop_ptr to top-1 have not been visited)
 * - fix_ptr = index of the first constraint to check for updating the assignment.
 * - size = size of all subarrays
 */

// Explanation: either a literal or a pointer or a pair of variables
typedef union arith_expl_u {
  literal_t lit;
  void *ptr;
  thvar_t v[2];
} arith_expl_t;

typedef struct arith_bstack_s {
  xrational_t *bound;
  thvar_t *var;
  arith_expl_t *expl;
  int32_t *pre;
  uint8_t *tag;

  uint32_t top;
  uint32_t prop_ptr;
  uint32_t fix_ptr;
  uint32_t size;
} arith_bstack_t;


// New: explanation triple from the egraph
typedef struct egraph_expl_triple_s {
  thvar_t var[2];
  int32_t id;
} egraph_expl_triple_t;


/*
 * Default/maximal sizes
 */
#define DEF_ARITH_BSTACK_SIZE 100
#define MAX_ARITH_BSTACK_SIZE (UINT32_MAX/sizeof(xrational_t))


/*
 * Tags and marks
 */
typedef enum arith_cnstr_type {
  ATYPE_LB = 0,   // lower bound
  ATYPE_UB = 1,   // upper bound
} arith_cnstr_type_t;

typedef enum arith_cnstr_expl {
  AEXPL_AXIOM,
  AEXPL_ASSERTION,
  AEXPL_DERIVED,
  AEXPL_EGRAPHEQ,
} arith_cnstr_expl_t;


#define ARITH_CNSTR_TYPE_MASK ((uint8_t) 0x1)
#define ARITH_CNSTR_TAG_MASK  ((uint8_t) 0x6)
#define ARITH_CNSTR_MARK_MASK ((uint8_t) 0x80)



// construct an 8bit tag (we need a macro here because it's used in constant definitions below)
#define mk_arith_tag(e, t) ((uint8_t)(((e)<<1)|(t)))

static inline uint8_t mk_arith_lb_tag(arith_cnstr_expl_t e) {
  return mk_arith_tag(e, ATYPE_LB);
}

static inline uint8_t mk_arith_ub_tag(arith_cnstr_expl_t e) {
  return mk_arith_tag(e, ATYPE_UB);
}


// check the mark
static inline bool arith_tag_mark(uint8_t tag) {
  return (tag & ARITH_CNSTR_MARK_MASK) != 0;
}


// extract components
static inline arith_cnstr_expl_t arith_tag_get_expl(uint8_t tag) {
  return (arith_cnstr_expl_t)((tag & ARITH_CNSTR_TAG_MASK) >> 1);
}

static inline arith_cnstr_type_t arith_tag_get_type(uint8_t tag) {
  return (arith_cnstr_type_t) (tag & ARITH_CNSTR_TYPE_MASK);
}

// type + explanation
static inline uint8_t arith_tag(uint8_t tag) {
  return (uint8_t) (tag & (ARITH_CNSTR_TAG_MASK|ARITH_CNSTR_TYPE_MASK));
}



/*
 * All combinations
 */
#define ARITH_AXIOM_LB    mk_arith_tag(AEXPL_AXIOM, ATYPE_LB)
#define ARITH_AXIOM_UB    mk_arith_tag(AEXPL_AXIOM, ATYPE_UB)
#define ARITH_ASSERTED_LB mk_arith_tag(AEXPL_ASSERTION, ATYPE_LB)
#define ARITH_ASSERTED_UB mk_arith_tag(AEXPL_ASSERTION, ATYPE_UB)
#define ARITH_DERIVED_LB  mk_arith_tag(AEXPL_DERIVED, ATYPE_LB)
#define ARITH_DERIVED_UB  mk_arith_tag(AEXPL_DERIVED, ATYPE_UB)
#define ARITH_EGRAPHEQ_LB mk_arith_tag(AEXPL_EGRAPHEQ, ATYPE_LB)
#define ARITH_EGRAPHEQ_UB mk_arith_tag(AEXPL_EGRAPHEQ, ATYPE_UB)






/****************************
 *  ASSERTIONS STACK/QUEUE  *
 ***************************/

/*
 * Asserted atoms (from the core) are stored into a queue/stack
 * before being processed by simplex_propagate.
 * - each assertion is a 32bit integer than consists of an
 *   atom id + a sign bit
 * - the atom id, is an atom index in the atom table
 *   (that fits in 28 bits since there are at most UINT32_MAX/16 atoms)
 * The sign bit is the low-order bit of the assertion code:
 * - sign bit = 0 means atom asserted true
 * - sign bit = 1 means atom asserted false
 *
 * Any atom that's in the queue is also marked in the atom table (this
 * is used for theory propagation). Atoms are unmarked during
 * backtracking.
 *
 * Other components:
 * - size = size of the stack
 * - top = top of the stack = end of the queue
 * - prop_ptr = first assertion to process = start of the queue
 *   the queue is the set of assertions in data[prop_ptr ... top-1]
 */
typedef struct arith_astack_s {
  uint32_t size;
  uint32_t top;
  uint32_t prop_ptr;
  int32_t *data;
} arith_astack_t;


#define DEF_ARITH_ASTACK_SIZE 100
#define MAX_ARITH_ASTACK_SIZE (UINT32_MAX/4)




/****************
 *  UNDO STACK  *
 ***************/

/*
 * On entry to each decision level k we store:
 * - the number of asserted bounds (i.e., arith_stack.top)
 * - the number of asserted atoms (i.e., arith_queue.top)
 *
 * At level 0: n_bounds = 0, n_assertions = 0
 */
typedef struct arith_undo_record_s {
  uint32_t n_bounds;
  uint32_t n_assertions;
} arith_undo_record_t;

typedef struct arith_undo_stack_s {
  uint32_t size;
  uint32_t top;
  arith_undo_record_t *data;
} arith_undo_stack_t;

#define DEF_ARITH_UNDO_STACK_SIZE 100
#define MAX_ARITH_UNDO_STACK_SIZE (UINT32_MAX/sizeof(arith_undo_record_t))





/********************
 *  PUSH/POP STACK  *
 *******************/

/*
 * The constraint matrix is modified (destructively) on every simplex_start_search
 * To support push/pop and multiple checks, we must keep enough information to
 * restore the matrix to what it was before the previous 'start_search'.
 *
 * The matrix contains two types of rows:
 * - rows of the form (p == 0) added on calls to assert_eq_axiom
 * - rows of the form (x - q = 0) where x is a variable and q is a polynomial.
 *   The polynomial q is x's definition obtained from the variable table.
 *
 * We don't add the row (x - q = 0) if q is simple. Currently
 * simple means that q is of the form (k + a.y) for two constants k and a.
 * For such polynomials, we replace x by q eagerly, everywhere x is referenced.
 * (and x is a trivial variable).
 *
 * To restore the matrix to its old state:
 * - we keep a copy of all polynomials p_1, ..., p_k that form the first type of
 *   rows. These polynomials are stored in vector simplex->saved_rows.
 * - we reconstruct the rows (x - q = 0) for all the non-trivial variables.
 */

/*
 * On entry to a new base level, we save
 * - the number of variables and atoms
 * - the size of the saved row vector
 * - the current propagation pointer for both assertion_queue and bound stack
 */
typedef struct arith_trail_s {
  uint32_t nvars;
  uint32_t natoms;
  uint32_t nsaved_rows;
  uint32_t bound_ptr;
  uint32_t assertion_ptr;
} arith_trail_t;

typedef struct arith_trail_stack_s {
  uint32_t size;
  uint32_t top;
  arith_trail_t *data;
} arith_trail_stack_t;


#define DEF_SIMPLEX_TRAIL_SIZE 20
#define MAX_SIMPLEX_TRAIL_SIZE (UINT32_MAX/sizeof(arith_trail_t))




/********************************
 *  THEORY PROPAGATION OBJECTS  *
 *******************************/

/*
 * When a simplex solver propagate a literal l (via a call to propagate_literal)
 * it uses an propagation object as antecedent for l. The propagation object
 * stores enough information to construct an explanation for l when requested.
 * The explanation for l must be a vector of literals (l_1 ... l_n) such that
 *  "(and l_1 ... l_n) implies l" holds.
 *
 * Currently, there are two types of propagation objects, corresponding to two
 * propagation rules:
 *
 * 1) simplex propagation:
 *    a bound k implies l (e.g., bound k is (x >= 2) and l is the atom (x >= 1))
 *    The propagation object stores k in that case.
 *
 * 2) egraph disequalities:
 *    If x1 and x2 are attached to terms t1 and  t2 in the egraph, then
 *    the egraph will assert (x1 != x2) in simplex when (t1 != t2) holds in
 *    the egraph. To deal with (x1 != x2), the simplex will create
 *    a simplex variable  y = x1 - x2 and two atoms (y >= 0) and (y <= 0).
 *    Then it will add a trichotomy clause to the core:
 *        (or (eq t1 t2) (not (y >= 0)) (not (y <= 0)))
 *    and the simplex solver may have to propagate (not (eq t1 t2)) to the core.
 *    The propagation object stores x1 and x2 in that case + a hint.
 *
 * The propagation objects starts with a tag that identifies the
 * propagation rule.
 *
 * NOTE: APROP_EGRAPH_DISEQ is not used anymore.
 */
typedef enum aprop_tag {
  APROP_BOUND,        // ordinary simplex propagation
  APROP_EGRAPH_DISEQ, // propagation for egraph disequality
} aprop_tag_t;

typedef struct aprop_header_s {
  aprop_tag_t tag;
} aprop_header_t;

// simplex propagation object
typedef struct aprop_s {
  aprop_tag_t tag;
  int32_t bound;
} aprop_t;

// egraph disequality propagation object
typedef struct aprop_egraph_diseq_s {
  aprop_tag_t tag;
  diseq_pre_expl_t d;
} aprop_egraph_diseq_t;




/*****************************************
 *  PROPAGATION USING OFFSET EQUALITIES  *
 ****************************************/

/*
 * To propagate equalities to the egraph:
 * - we use offset_manager as an auxiliary solver
 * - for every theory variable x, we mark x as relevant
 *   if its definition is suitable for offset equality:
 *   (i.e., x's definition must be of the form x := y - z
 *    so that we can propagate y == z + a when we detect a <= x <= a)
 * - to detect frozen variables, we keep a propagation pointer
 *   (an index in the simplex's bound stack).
 *
 * To build explanations:
 * - aux = vector of frozen variables
 * - expl_queue = queue of constraint indices used to convert aux
 *   into a th_explanation_t objet.
 * - we need a separate expl_queue than the one in the egraph
 *   because simplex_expand_th_explanation may be called
 *   within simplex_build_explanation
 */
typedef struct eq_propagator_s {
  offset_manager_t mngr;
  byte_t *relevant;   // one bit per variable
  uint32_t nvars;     // number of variables
  uint32_t size;      // size of vector 'relevant' (number of bits)
  uint32_t prop_ptr;  // propagation pointer

  ivector_t aux;         // for explanations
  ivector_t expl_queue;  // also for explanations
  rational_t q_aux;
} eq_propagator_t;


#define DEF_EQPROP_SIZE 128



/******************
 *  CACHED DATA   *
 *****************/

/*
 * If the simplex solver is connected to an egraph, trichotomy clauses
 * may be generated dynamically. If t1 and t2 are two egraph terms,
 * with respective theory variables x1 and x2 (both in the simplex), then the
 * trichotomy clauses is the axiom:
 *    (t1 == t2) or (x1 < x2) or (x2 < x1)
 * Internally, this is encoded via an auxiliary variable y and a constant k
 * such that y - k = (x1 - x2) or y - k = (x2 - x1). The axiom is then
 *    (t1 == t2) or (not (y >= k)) or (not (y <= k))
 *
 * To avoid generating the same axiom several time, we keep track
 * of which trichotomy clauses have been generated in an internal cache.
 * For each clause, the cache stores a record [TRICHOTOMY_LEMMA, t1, t2]
 * (modulo reordering to ensure t1 < t2). Note: we can't use l in the cache
 * because (t1 == t2) may the false literal (fixed a bug by changing that).
 *
 * Each cache record needs a tag + a non-zero flag. To differentiate from the tags
 * used in the egraph cache, we use 2 here.
 */
typedef enum arith_lemma_tag {
  TRICHOTOMY_LEMMA = 2,
} arith_lemma_tag_t;

typedef enum arith_lemma_flag {
  ACTIVE_ARITH_LEMMA = 1,
} arith_lemma_flag_t;






/*********************
 *  BOUND COLLECTOR  *
 ********************/

/*
 * When we adjust the model (in reconcile model), we try to shift the
 * current value of a non-basic variable x by some delta, then adjust
 * the value of all basic variables that depend on x.  We want this
 * shift to preserve feasibility (without requiring any pivoting)
 *
 * To do this, we compute an interval of values for delta that maintains
 * feasibility and we also need a rational D that defines which deltas
 * maintain integer feasibility. All these components are stored in
 * the following record.
 *
 * - lb and ub are lower and upper bounds
 * - has_lb is true if lb is valid, otherwise, there's no lower bound
 * - has_ub is true if ub is valid, otherwise, there's no upper bound
 * - period is a rational number, if it's not zero then the allowed
 *   shifts on x must be multiple of period. (If it's zero, the allowed
 *   shifts on x can be anything).
 *
 * Two more components are used for sampling
 * - k_min = smallest integer k such that lb <= k period
 *   (i.e., k_min = ceil(lb/period))
 * - k_max = largest integer k such that k period <= ub
 *   (i.e., k_max = floor(ub/period))
 */
typedef struct interval_s {
  bool has_lb;
  bool has_ub;
  xrational_t lb;
  xrational_t ub;
  rational_t period;
  int32_t k_min;
  int32_t k_max;
} interval_t;



/****************
 *  STATISTICS  *
 ***************/

/*
 * Search + problem size
 */
typedef struct simplex_stats_s {
  // problem size
  uint32_t num_init_vars;    // number of variables/columns in initial matrix
  uint32_t num_init_rows;    // number of rows in the initial matrix
  uint32_t num_atoms;        // number of atoms (initially)

  // simplification data
  uint32_t num_elim_candidates;
  uint32_t num_elim_rows;
  uint32_t num_simpl_fvars;  // number of fixed variable after simplification
  uint32_t num_simpl_rows;   // number of rows in the simplified matrix
  uint32_t num_fixed_vars;   // number of fixed variables after tableau construction

  // more problem size data
  uint32_t num_rows;         // number of rows in the tableau after simplification
  uint32_t num_end_rows;     // number of rows in the final tableau
  uint32_t num_end_atoms;    // number of atoms at the end

  // lemmas and propagation
  uint32_t num_binary_lemmas;  // simple lemmas
  uint32_t num_prop_lemmas;    // lemmas from theory propagation
  uint32_t num_props;          // theory propagations
  uint32_t num_bound_props;    // bound propagations
  uint32_t num_prop_expl;      // propagations involved in a conflict

  // interface + trichotomy lemmas
  uint32_t num_interface_lemmas;
  uint32_t num_reduced_inter_lemmas;
  uint32_t num_tricho_lemmas;
  uint32_t num_reduced_tricho;

  // search statistics
  uint32_t num_make_feasible;  // calls to make_feasible
  uint32_t num_pivots;         // pivoting steps
  uint32_t num_blands;         // number of activations of bland's rule
  uint32_t num_conflicts;

  // stats on integer arithmetic solver
  uint32_t num_make_intfeasible;        // calls to make_integer_feasible
  uint32_t num_bound_conflicts;         // unsat by ordinary bound strengthening
  uint32_t num_bound_recheck_conflicts; // unsat by bound strengthening + recheck
  uint32_t num_itest_conflicts;         // unsat by the integrality test
  uint32_t num_itest_bound_conflicts;   // unsat by itest bound strengthening
  uint32_t num_itest_recheck_conflicts; // unsat by itest bounds + recheck
  uint32_t num_dioph_checks;            // number of calls to dsolver_check
  uint32_t num_dioph_gcd_conflicts;     // failed GCD tests in dsolver
  uint32_t num_dioph_conflicts;         // number of dsolver unsat
  uint32_t num_dioph_bound_conflicts;   // unset by dioph bound strengthening
  uint32_t num_dioph_recheck_conflicts; // unsat after dioph bounds + recheck

  uint32_t num_branch_atoms;            // new branch&bound atoms created

} simplex_stats_t;





/********************
 *  SIMPLEX SOLVER  *
 *******************/

typedef struct simplex_solver_s {
  /*
   * Attached smt core + gate manager + egraph
   * (egraph may be NULL)
   */
  smt_core_t *core;
  gate_manager_t *gate_manager;
  egraph_t *egraph;

  /*
   * Base level and decision level
   */
  uint32_t base_level;
  uint32_t decision_level;

  /*
   * Unsat flag: set to true if the asserted axioms are inconsistent
   */
  bool unsat_before_search;

  /*
   * Options: each option is a single bit in the 32-bit word
   */
  uint32_t options;

  /*
   * Interrupt flag: set to true to stop pivoting
   */
  bool interrupted;

  /*
   * Pivoting parameters
   */
  bool use_blands_rule;     // true if Bland's rule is active
  uint32_t bland_threshold; // number of repeat entering variable

  /*
   * Parameters for propagation
   */
  uint32_t prop_row_size;     // max size of rows considered for propagation
  int32_t last_conflict_row;  // last row where a conflict was found
  bool recheck;               // true if make_feasible must be called after propagation

  /*
   * Pseudo-random number generator
   */
  uint32_t prng;

  /*
   * Flag and parameter for integer arithmetic
   */
  bool integer_solving;
  bool enable_dfeas;
  int32_t check_counter;
  int32_t check_period;
  bvar_t last_branch_atom;

  /*
   * Optional subsolver for integer arithmetic: allocated when needed
   */
  dsolver_t *dsolver;

  /*
   * Optional cache for trichotomy lemmas: allocated when needed
   */
  cache_t *cache;

  /*
   * Statistics
   */
  simplex_stats_t stats;

  /*
   * Table of variables and atoms + pointer to the variable manager
   * for all input polynomials
   */
  arith_atomtable_t atbl;
  arith_vartable_t  vtbl;

  /*
   * Propagation data structure: defined elsewhere
   */
  void *propagator;

  /*
   * Propagator for the egraph: optional
   */
  eq_propagator_t *eqprop;

  /*
   * Matrix/tableau
   * - tableau_ready is true if the matrix is in tableau form
   *   and the variables have an initial assignment
   * - matrix_ready is true if the matrix contains all the
   *   constraints asserted so far
   * - save_rows is true if the top-level rows must be saved (i.e.,
   *   if the context supports push/pop or multiple checks).
   *
   * The flags are set as follows to support push/pop/multicheck:
   * - initially, the matrix is empty:
   *      tableau_ready = false
   *      matrix_ready = true
   * - in start_search, the matrix is converted to a tableau:
   *   so after start_search,
   *      tableau_ready = true
   *      matrix_ready = false
   * - after pop, the tableau is emptied:
   *      tableau_ready = false
   *      matrix_ready keeps its current value
   * - in start_internalization, we restore the constraint matrix
   *   and reset the tableau if needed:
   *      tableau_ready = false
   *      matrix_ready = true
   */
  matrix_t matrix;
  bool tableau_ready;
  bool matrix_ready;
  bool save_rows;

  /*
   * Heap to store the basic-variables whose current assignment
   * does not satisfy the bounds
   */
  int_heap_t infeasible_vars;

  /*
   * Bounds + assertions
   */
  arith_bstack_t bstack;
  arith_astack_t assertion_queue;

  /*
   * Queue of egraph assertions + disequalities received from
   * the egraph (disequalities are stored in a stack)
   */
  eassertion_queue_t egraph_queue;

  /*
   * Undo stack
   */
  arith_undo_stack_t stack;

  /*
   * Push/pop stack + saved rows
   */
  arith_trail_stack_t trail_stack;
  pvector_t saved_rows;

  /*
   * Result of matrix simplification
   * - a triangular matrix + a variable assignment
   */
  elim_matrix_t elim;
  fvar_vector_t fvars;

  /*
   * Auxiliary buffers and data structures
   */
  poly_buffer_t buffer;
  rational_t constant;
  rational_t aux;
  rational_t gcd;
  xrational_t bound;
  xrational_t delta;
  xrational_t xq0;         // general purpose buffer

  ivector_t expl_vector;   // vector of literals for conflicts/explanations
  ivector_t expl_queue;    // vector used as a queue for building explanations
  ivector_t expl_aux;      // to collect explanations from the egraph
  ivector_t aux_vector;    // general-purpose vector
  ivector_t aux_vector2;   // another one
  ivector_t rows_to_process;  // rows for propagation

  arena_t arena; // store explanations of implied atoms


  /*
   * Model construction support
   * - value[x] = rational value of x
   * - epsilon is a positive rational
   * - if val[x] = a + b delta as an extended rational, then the rational value
   *   for a variable x is a + b * epsilon.
   * - factor is an auxiliary rational used for computing epsilon
   * - dprng is used by a pseudo-random number generator (for adjust model)
   */
  rational_t *value;
  rational_t epsilon;
  rational_t factor;
  double dprng;

  /*
   * Jump buffer for exception handling during internalization
   */
  jmp_buf *env;
} simplex_solver_t;


/*
 * Initial size of the explanation vector/queue
 */
#define DEF_ARITH_EXPL_VECTOR_SIZE 20


/*
 * Initial size of the vector of rows to process
 */
#define DEF_PROCESS_ROW_VECTOR_SIZE 20



/*
 * Option flags
 * - each mask selects a bit in the option word
 * - bit = 1 means option enabled, 0 means disabled
 *
 * Current options
 * - EAGER_LEMMAS: when an atom on x is created, all binary lemmas
 *   relating it to other atoms on x are added to the clause set.
 * - PROPAGATION: enable propagation via rows
 * - ICHECK: enable periodic integer checking
 * - ADJUST_MODEL: attempt to modify the variable assignment to
 *   make the simplex model consistent with the egraph (as much as possible).
 * - EQPROP: enable propagation of equalities to the egraph
 *
 * Bland's rule threshold: based on the count of repeat
 * leaving variable. The counter is incremented whenever
 * a variable x leaves the basic for at least the second time.
 * When the counter becomes >= threshold, then Bland's rule
 * is activated to ensure termination.
 *
 * Propagation row size = maximal size of rows considered for propagation.
 */
#define SIMPLEX_EAGER_LEMMAS        0x1
#define SIMPLEX_PROPAGATION         0x2
#define SIMPLEX_ICHECK              0x4
#define SIMPLEX_ADJUST_MODEL        0x8
#define SIMPLEX_EQPROP              0x10

#define SIMPLEX_DISABLE_ALL_OPTIONS 0x0

#define SIMPLEX_DEFAULT_BLAND_THRESHOLD    1000
#define SIMPLEX_DEFAULT_PROP_ROW_SIZE        30
#define SIMPLEX_DEFAULT_CHECK_PERIOD   99999999

// default options
#define SIMPLEX_DEFAULT_OPTIONS (SIMPLEX_DISABLE_ALL_OPTIONS)


#endif /* __SIMPLEX_TYPES_H */
