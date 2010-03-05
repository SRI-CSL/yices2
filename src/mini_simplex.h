/*
 * A simpler simplex solver to be used in conjunction with the diophantine solver.
 *
 * The input to this solver is a set of equalities
 *   x_1 = b_1 + a_11 y_1 + ... + a_1k y_k
 *    ...
 *   x_n = b_n + a_n1 y_1 + ... + a_nk y_k
 * plus a set of bounds on the variables x_1, ..., x_n:
 *  l_i <= x_i <= u_i
 *
 * The equalities are the general solutions computed by the diophantine 
 * solver. The variables x_1, ..., x_n are problem variables. 
 * The variables y_1, ..., y_k are integer parameters.
 * 
 * The coefficients b_i, a_ij, and the bounds l_i and u_i are * integers,
 * and all variables are also integer.
 *
 * For a variable x_i, let d = gcd(a_i1, ..., a_ik). If d is greater than one,
 * we can strengthen the bounds on x_i as follows:
 *   l'_i = b_i + d * ceil((l_i - b_i)/d)
 *   u'_i = b_i + d * floor((u_i - b_i)/d)
 * This preserves satisfiability.
 */

#ifndef __MINI_SIMPLEX_H
#define __MINI_SIMPLEX_H

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "int_vectors.h"
#include "int_heap.h"
#include "rationals.h"
#include "polynomials.h"
#include "matrices.h"


/*
 * Status flags:
 * - ready means that the system has not been solved yet
 *
 * After solving, the status is updated:
 * - unknown means no conflict found but the current solution is not integer
 * - sat means: valid solution found
 * - bound_conflict: a variable x_i has conflicting bounds (l_i <= x_i <= u_i)
 *   but l_i > u_i (so the system is unsat)
 * - row_conflict: a conflict row was found by simplex (also unsat)
 *
 * For both bound_conflict and row_conflict, the index of a conflict variable 
 * is stored to generate explanations
 * - if status is bound_conflict, the conflict variable is a variable 
 *   x_i such that lb[x_i] > ub[x_i]
 * - if status is row_conflict, the conflict variable x_i is the basic variable
 *   in the conflict row. The value of x_i in the current assignment
 *   is either less than lb[x_i] or more than ub[x_i].
 */
typedef enum msplx_status {
  MINI_SIMPLEX_READY,
  MINI_SIMPLEX_UNKNOWN,
  MINI_SIMPLEX_SAT,
  MINI_SIMPLEX_BOUND_CONFLICT,
  MINI_SIMPLEX_ROW_CONFLICT,
} msplx_status_t;


/*
 * Input components:
 * - nvars = number of x_i variables
 * - nparams = number of parameter variables y_1, ..., y_k
 * - eq = array of nvars polynomials (general solutions computed by dsolver) 
 * - lb = array of nvars rationals (lower bounds)
 * - ub = array of nvars rationals (upper bounds)
 * - tag = array of tags. Each tag is 8bits
 *
 * The left-hand-side variables (x_i) are identified by an index between 0 and nvars-1.
 * This is the same index used for x_i in the full simplex solver and in the dsolver.
 * For a variable x between 0 and nvars-1:
 * - eq[x] is NULL is x does not occur in the system
 * - eq[x] is a polynomial in variables y_1, ..., y_k otherwise.
 * - tag[x] indicates whether x has a lower and an upper bound,
 *          and whether the bounds have been strengthened.
 * - lb[x] and ub[x] are two integers (stored as rational_t objects)
 *
 * The parameters y_1,..., y_k have an index in the range [nvars, .., nvars + k -1]
 * The problem variablex x_1, ..., x_n have an index in the range [0, ..., nvars-1]
 * (index 0 is not really a variable. It represents the constant and eq[0] is always 
 *  the polynomial 1.)
 *
 * Tableau:
 * - formed by matrix + current solution
 * - val[x] = value for x in the current solution (a rational)
 *            val has size nvars + k.
 *   val[0] is always 1.
 */
typedef struct mini_simplex_s {
  // status + conflict var
  msplx_status_t status;
  int32_t conflict_var;

  // size and main components
  uint32_t nvars;
  uint32_t nparams;
  polynomial_t **eq;
  rational_t *lb;
  rational_t *ub;
  uint8_t *tag;

  // Tableau
  rational_t *val;
  matrix_t matrix;

  // Set of variables to make feasible
  int_heap_t infeasible_vars;

  // Auxiliary rationals
  rational_t q0, q1, q2;
} mini_simplex_t;



/*
 * Maximal number of variables (vars + params)
 */
#define MAX_MINI_SIMPLEX_VARS (UINT32_MAX/8)


/*
 * Tag for a variable x: 4 bits b_3 b_2 b_1 b_0
 * - b_0 is 1 if x has a lower bound  (stored in lb[x])
 * - b_1 is 1 if x has an upper bound (stored in ub[x])
 * - b_2 is 1 if lb[x] was derived by bound strengthening
 * - b_3 is 1 if ub[x] was derived by bound strengthening
 */
#define MINI_SIMPLEX_LB_MASK 0x1
#define MINI_SIMPLEX_UB_MASK 0x2
#define MINI_SIMPLEX_STRLB_MASK 0x4
#define MINI_SIMPLEX_STRUB_MASK 0x8

#define MINI_SIMPLEX_INIT_MASK 0x00


/*
 * Possible bound combinations: based on the
 * two low order bits of the tag.
 */
typedef enum msplx_btag {
  MINI_SIMPLEX_NO_BOUNDS = 0,   // 00
  MINI_SIMPLEX_LB_ONLY = 1,     // 01
  MINI_SIMPLEX_UB_ONLY = 2,     // 10
  MINI_SIMPLEX_BOTH_BOUNDS = 3, // 11 
} msplx_btag_t;


/*
 * Explanation codes:
 * - a conflict explanation is a set of three types of assertions:
 * - lower bound on variable x
 * - upper bound on variable x
 * - initial equality (x == p)
 * We encode a each assertion in a 32bit integer:
 * - the two lower bits are a tag, the rest (29 bits) is the variable index
 * - there are three tags encoded as 00, 01, 10
 */
typedef enum msplx_etag {
  MSPLX_EQ_TAG = 0x0,    // 00
  MSPLX_LB_TAG = 0x1,    // 01
  MSPLX_UB_TAG = 0x2,    // 10
} msplx_etag_t;


/*
 * Build explanation code
 */
static inline int32_t mini_expl_eq(int32_t x) {
  return (x << 2) | MSPLX_EQ_TAG;
}

static inline int32_t mini_expl_lb(int32_t x) {
  return (x << 2) | MSPLX_LB_TAG;
}

static inline int32_t mini_expl_ub(int32_t x) {
  return (x << 2) | MSPLX_UB_TAG;
}


/*
 * Extract tag and variable from an explanation code
 */
static inline msplx_etag_t mini_expl_tag(int32_t code) {
  return (msplx_etag_t) (((uint32_t) code) & 0x3);
}

static inline int32_t mini_expl_var(int32_t code) {
  return (int32_t) (((uint32_t) code) >> 2);
}










/*
 * Initialize s to the empty solver
 */
extern void init_mini_simplex(mini_simplex_t *s);


/*
 * Reset s to an empty solver (nvars = 0, nparameters = 0, eq = NULL)
 */
extern void reset_mini_simplex(mini_simplex_t *s);


/*
 * Delete s
 */
extern void delete_mini_simplex(mini_simplex_t *s);


/*
 * Prepare s for solving: add equations and allocate internal structures
 * - n = number of variables
 *   m = number of parameters
 * - gen_sol = array of polynomials defining (it will be used as eq).
 *   the solver does not modify eq so that's safe, but this solver must
 *   be deleted before the dsolver that constructed gen_sol is deleted or reset.
 * - no bounds are asserted on the variables.
 * - s must be empty (to avoid memory leaks).
 *
 * This function must be called before the lower/upper bounds are asserted.
 * - it initialize the tableau with equalities x_i == eq[x_i]
 * - it allocates internal and initializes the internal arrays lb, ub, tag, val
 */
extern void mini_simplex_set_eq(mini_simplex_t *s, uint32_t n, uint32_t m, polynomial_t **eq);


/*
 * Add b as lower bound or upper_bound on x
 * - x must be in the range 1,..., nvars-1 
 * - b must be an integer
 */
extern void mini_simplex_set_lb(mini_simplex_t *s, int32_t x, rational_t *b);
extern void mini_simplex_set_ub(mini_simplex_t *s, int32_t x, rational_t *b);


/*
 * Solve the system s and set s->status
 * - max_pivots = bound on the number of pivoting steps
 * - the result is stored in s->status and related fields
 * Status code:
 * - MINI_SIMPLEX_SAT: satisfiable
 *   a feasible integer solution is stored in s->val
 * - MINI_SIMPLEX_BOUND_CONFLICT: unsat
 *   the conflict variable is in s->conflict_var
 * - MINI_SIMPLEX_ROW_CONFLICT: unsat
 *   the basic variable of the conflict row is in s->conflict_var
 * - MINI_SIMPLEX_UNKNOWN: unsuccessful attempt
 *   if s->infeasible_vars is non-empty, then solving was interrupted after max_pivots
 *   otherwise, a feasible solution is in s->val but it's not all integers
 */
extern void mini_simplex_check(mini_simplex_t *s, uint32_t max_pivots);


/*
 * EXPLANATIONS
 */

/*
 * Get the conflict row
 * - s->status must be MINI_SIMPLEX_ROW_CONFLICT
 */
extern row_t *mini_simplex_get_conflict_row(mini_simplex_t *s);


/*
 * Collect the conflicting bounds in the conflict row (add them to v)
 * - s->status must be MINI_SIMPLEX_ROW_CONFLICT
 */
extern void mini_simplex_explain_row_conflict_bounds(mini_simplex_t *s, ivector_t *v);


/*
 * Explanation for a bound conflict
 * - s->status must be MINI_SIMPLEX_BOUND_CONFLICT
 */
extern void mini_simplex_explain_bound_conflict(mini_simplex_t *s, ivector_t *v);


/*
 * Build a conflict explanation:
 * - s->status must be BOUND_CONFLICT or ROW_CONFLICT
 * - the conflict is stored in vector v
 * (each element of v encodes ub/lb or eq for a variable x)
 */
extern void mini_simplex_conflict_explanation(mini_simplex_t *s, ivector_t *v);


/*
 * TESTING
 * - return false if unsat is detected
 */
extern bool mini_simplex_test(mini_simplex_t *s);



/*
 * Check whether x has a lower or an upper bound
 * - x must be in the range 1,..., nvars-1
 */
static inline bool mini_simplex_var_has_lb(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars);
  return (s->tag[x] & MINI_SIMPLEX_LB_MASK) != 0;
}

static inline bool mini_simplex_var_has_no_lb(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars);
  return (s->tag[x] & MINI_SIMPLEX_LB_MASK) == 0;
}

static inline bool mini_simplex_var_has_ub(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars);
  return (s->tag[x] & MINI_SIMPLEX_UB_MASK) != 0;
}

static inline bool mini_simplex_var_has_no_ub(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars);
  return (s->tag[x] & MINI_SIMPLEX_UB_MASK) == 0;
}

static inline bool mini_simplex_var_has_bounds(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars);
  return (s->tag[x] & (MINI_SIMPLEX_UB_MASK|MINI_SIMPLEX_LB_MASK)) != 0;
}

static inline msplx_btag_t mini_simplex_bound_tag(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars);
  return (msplx_btag_t) (s->tag[x] & 0x3); // low order bits of the tag
}



#endif /* __MINI_SIMPLEX_H */


   
