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

#include <assert.h>
#include <stdbool.h>

#include "prng.h"
#include "memalloc.h"
#include "mini_simplex.h"

#if 0
// TO BE REMOVED
#include <stdio.h>
#include <inttypes.h>
#include "dsolver_printer.h"
#endif


/*
 * INITIALIZATION
 */

/*
 * Initialize s to the empty solver
 */
void init_mini_simplex(mini_simplex_t *s) {
  s->status = MINI_SIMPLEX_READY;
  s->conflict_var = -1;
  s->nvars = 0;
  s->nparams = 0;
  s->eq = NULL;
  s->lb = NULL;
  s->ub = NULL;
  s->tag = NULL;
  s->val = NULL;
  
  init_matrix(&s->matrix, 0, 0);
  init_int_heap(&s->infeasible_vars, 0, 0);

  q_init(&s->q0);
  q_init(&s->q1);
  q_init(&s->q2);
}


/*
 * Reset s to an empty solver (nvars = 0, nparameters = 0, eq = NULL)
 */
void reset_mini_simplex(mini_simplex_t *s) {
  uint32_t i, n;

  n = s->nvars;
  for (i=0; i<n; i++) {
    q_clear(s->lb + i);
    q_clear(s->ub + i);
  }
  n = s->nvars + s->nparams;
  for (i=0; i<n; i++) {
    q_clear(s->val + i);
  }
  safe_free(s->lb);
  safe_free(s->ub);
  safe_free(s->tag);
  safe_free(s->val);

  s->status = MINI_SIMPLEX_READY;
  s->conflict_var = -1;
  s->nvars = 0;
  s->nparams = 0;
  s->eq = NULL;
  s->lb = NULL;
  s->ub = NULL;
  s->tag = NULL;
  s->val = NULL;

  reset_matrix(&s->matrix);
  reset_int_heap(&s->infeasible_vars);
  q_clear(&s->q0);
  q_clear(&s->q1);
  q_clear(&s->q2);
}


/*
 * Delete s
 */
void delete_mini_simplex(mini_simplex_t *s) {
  uint32_t i, n;

  n = s->nvars;
  for (i=0; i<n; i++) {
    q_clear(s->lb + i);
    q_clear(s->ub + i);
  }
  n = s->nvars + s->nparams;
  for (i=0; i<n; i++) {
    q_clear(s->val + i);
  }
  safe_free(s->lb);
  safe_free(s->ub);
  safe_free(s->tag);
  safe_free(s->val);

  s->eq = NULL;
  s->lb = NULL;
  s->ub = NULL;
  s->tag = NULL;
  s->val = NULL;

  delete_matrix(&s->matrix);
  delete_int_heap(&s->infeasible_vars);
  q_clear(&s->q0);
  q_clear(&s->q1);
  q_clear(&s->q2);
}



/*
 * ASSERTIONS: EQUATIONS AND BOUNDS
 */

/*
 * Prepare s for solving: add equations and allocate internal structures
 * - n = number of variables = size of array eq
 *   m = number of parameters
 * - gen_sol = array of polynomials defining (it will be used as eq).
 *   the solver does not modify eq so that's safe, but this solver must
 *   be deleted before the dsolver that constructed gen_sol is deleted or reset.
 * - no bounds are asserted on the variables.
 * - s must be empty (to avoid memory leaks).
 *
 * This function must be called before the lower/upper bounds are asserted.
 */
void mini_simplex_set_eq(mini_simplex_t *s, uint32_t n, uint32_t m, polynomial_t **eq) {
  uint32_t i;
  polynomial_t *p;

  assert(s->eq == NULL && s->lb == NULL && s->ub == NULL && s->tag == NULL && s->val == NULL);

  if (n + m >= MAX_MINI_SIMPLEX_VARS) {
    // this assumes n + m does not overflow. Could be more paranoid here.
    out_of_memory();
  }


  s->nvars = n;
  s->nparams = m;
  s->eq = eq;

  // lb, ub, tag have size n
  s->lb = (rational_t *) safe_malloc(n * sizeof(rational_t));
  s->ub = (rational_t *) safe_malloc(n * sizeof(rational_t));
  s->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  for (i=0; i<n; i++) {
    q_init(s->lb + i);
    q_init(s->ub + i);
    s->tag[i] = MINI_SIMPLEX_INIT_MASK;
  }


  // the total number of variables is n+m
  // val is initialized to all zeros
  m += n;
  s->val = (rational_t *) safe_malloc(m * sizeof(rational_t));
  for (i=0; i<m; i++) {
    q_init(s->val + i);
  }
  
  // allocate enough columns in the matrix
  matrix_add_columns(&s->matrix, m);

  /*
   * Initial tableau: 
   * - eq[x_i] is turned into the row (x_i - eq[x_i] == 0), 
   *   with x_i as basic variable
   * - i=0 is skipped since it's not a variable
   */
  for (i=1; i<n; i++) {
    p = eq[i];
    if (p != NULL) {
      matrix_add_tableau_eq(&s->matrix, i, p->mono, p->nterms);
    }
  }

}




/*
 * Add b as lower bound or upper_bound on x
 * - x must be in the range 1,..., nvars-1 
 * - b must be an integer
 */
void mini_simplex_set_lb(mini_simplex_t *s, int32_t x, rational_t *b) {
  assert(s->lb != NULL && 1 <= x && x < s->nvars && q_is_integer(b));
  q_set(s->lb + x, b);
  s->tag[x] |= MINI_SIMPLEX_LB_MASK;
} 

void mini_simplex_set_ub(mini_simplex_t *s, int32_t x, rational_t *b) {
  assert(s->ub != NULL && 1 <= x && x < s->nvars && q_is_integer(b));
  q_set(s->ub + x, b);
  s->tag[x] |= MINI_SIMPLEX_UB_MASK;  
}




/*
 * SOLVING
 */

/*
 * Check the asserted bounds and strengthen them if possible
 * - set the status to bound_conflict if a conflict is found 
 *   and record the conflict variable
 */
static void mini_simplex_check_bounds(mini_simplex_t *s) {
  polynomial_t *p;
  rational_t *gcd, *aux, *constant;
  uint32_t i, n;
  msplx_btag_t tau;

  assert(s->status == MINI_SIMPLEX_READY);

  gcd = &s->q0;
  aux = &s->q1;
  constant = &s->q2;

  n = s->nvars;
  for (i=1; i<n; i++) {
    p = s->eq[i];
    tau = mini_simplex_bound_tag(s, i);
    switch (tau) {
    case MINI_SIMPLEX_NO_BOUNDS:
      break;
    case MINI_SIMPLEX_BOTH_BOUNDS:
      /*
       * We need to check whether the asserted bounds are compatible here.
       * to get a more precise explanation (not involving strengthening)
       */
      if (q_gt(s->lb + i, s->ub +i)) {
	s->status = MINI_SIMPLEX_BOUND_CONFLICT;
	s->conflict_var = i;
	return;
      }
      // fall through to compute gcd, etc.
    case MINI_SIMPLEX_LB_ONLY: 
    case MINI_SIMPLEX_UB_ONLY:
      if (p != NULL) {
	monarray_gcd(p->mono, gcd);
	assert(q_is_nonneg(gcd));
	if (q_cmp_int32(gcd, 1, 1) > 0) { // gcd > 1/1
	  monarray_constant(p->mono, constant);

	  if (tau & MINI_SIMPLEX_LB_MASK) {
	    /*
	     * Let b = constant of p and l = current lower bound;
	     * the strengthened bound is l' = b + d * ceil((l - b)/d)
	     * Let r = remainder of (l-b) divided by d
	     * if r = 0, then l' = l else l' = l + d - r (and l' > l)
	     */
	    q_set(aux, s->lb + i);
	    q_sub(aux, constant);   
	    q_integer_rem(aux, gcd);  // remainder of (l - b) divided by d
	    if (q_is_pos(aux)) {
	      // strengthen the bound and mark it
	      q_add(s->lb + i, gcd);
	      q_sub(s->lb + i, aux);
	      s->tag[i] |= MINI_SIMPLEX_STRLB_MASK;
	    }
	  }

	  if (tau & MINI_SIMPLEX_UB_MASK) {
	    /*
	     * The strengthened bound is u' = b + d * floor((u - b)/d)
	     * Let r = remainder of (u - b) divided by d
	     * If r = 0 then u' = u else u' = u - r
	     */
	    q_set(aux, s->ub + i);
	    q_sub(aux, constant);
	    q_integer_rem(aux, gcd);
	    if (q_is_pos(aux)) {
	      // strengthen the bound and mark it
	      q_sub(s->ub + i, aux);
	      s->tag[i] |= MINI_SIMPLEX_STRUB_MASK;
	    }
	  }

	  /*
	   * Check whether the two bounds are still compatible after
	   * strengthening.
	   */
	  if (tau == MINI_SIMPLEX_BOTH_BOUNDS && q_gt(s->lb + i, s->ub +i)) {
	    s->status = MINI_SIMPLEX_BOUND_CONFLICT;
	    s->conflict_var = i;
	    return;
	  }
	}
      }
    }
  }
}


/*
 * Check whether val[x] is between lb[x] and ub[x]
 */
static bool mini_simplex_value_within_bounds(mini_simplex_t *s, int32_t x) {
  uint8_t tag;

  assert(1 <= x && x < s->nvars);
  tag = s->tag[x];
  return ((tag & MINI_SIMPLEX_LB_MASK) == 0 || q_le(s->lb + x, s->val + x))
    && ((tag & MINI_SIMPLEX_UB_MASK) == 0 || q_le(s->val + x, s->ub + x));
}


/*
 * Compute the initial assignment and collect the basic variables whose
 * value is not within the bounds.
 * - the initial assignment is val[x_i] = b_i for all x_i and val[y_j] = 0
 *   since val is zero initially, we just need to set val[x_i]
 * - s->nvars must be positive
 * - infeasible_vars must be empty
 */
static void mini_simplex_init_assignment(mini_simplex_t *s) {
  polynomial_t *p;
  uint32_t i, n;

  assert(s->nvars > 0 && int_heap_is_empty(&s->infeasible_vars)) ;

  // first set val[0] = 1 (for the constant)
  q_set_one(s->val);
  n = s->nvars;
  for (i=1; i<n; i++) {
    p = s->eq[i];
    if (p != NULL) {
      monarray_constant(p->mono, s->val + i); // v[x_i] = constant of p_i = b_i
      if (! mini_simplex_value_within_bounds(s, i)) {
	int_heap_add(&s->infeasible_vars, i);
      }
    } else {
      /*
       * Adjust v[x_i] if bounds have been asserted on x_i
       * (x_i does not occur in the tableau)
       */
      if (mini_simplex_var_has_lb(s, i)) {
	q_set(s->val + i, s->lb + i);
      } else if (mini_simplex_var_has_ub(s, i)) {
	q_set(s->val + i, s->ub + i);
      }
      
    }
  }
}



/*
 * Check whether val[x] is integer for all variables
 */
static bool mini_simplex_integral_solution(mini_simplex_t *s) {
  uint32_t i, n;

  n = s->nvars + s->nparams;
  for (i=0; i<n; i++) {
    if (! q_is_integer(s->val + i)) return false;
  }
  return true;
}


/*
 * Update val[x] to lb[x] or ub[x] and propagate to the basic variables
 */
static void mini_simplex_update_solution(mini_simplex_t *s, int32_t x) {
  matrix_t *matrix;
  column_t *col;
  rational_t *delta;
  uint32_t i, n;
  int32_t y, k, r;

  assert(1 <= x && x < s->nvars && ! mini_simplex_value_within_bounds(s, x));

  delta = &s->q0;

  if (mini_simplex_var_has_ub(s, x) && q_gt(s->val + x, s->ub + x)) {
    // val[x] > ub[x]: new val[x] is ub[x]
    q_set(delta, s->ub + x);
    q_sub(delta, s->val + x);
    q_set(s->val + x, s->ub + x); // new value for x
  } else {
    assert(mini_simplex_var_has_lb(s, x) && q_lt(s->val + x, s->lb + x));
    // val[x] < lb[x]: new val[x] is lb[x]
    q_set(delta, s->lb + x);
    q_sub(delta, s->val + x);
    q_set(s->val + x, s->lb + x);
  }

  // delta = new val[x] - old val[x]
  matrix = &s->matrix;
  col = matrix->column[x];
  assert (col != NULL);
  n = col->size;
  for (i=0; i<n; i++) {
    r = col->data[i].r_idx;
    if (r >= 0) {
      y = matrix_basic_var(matrix, r);
      k = col->data[i].r_ptr;
      assert(1 <= y && y < s->nvars + s->nparams);
      // new val[y] = old val[y] + a * delta, 
      // where a = coeff of x in row[r]
      q_submul(s->val + y, delta, matrix_coeff(matrix, r, k));

      // add y to the heap if new val[y] is not withing bounds      
      if (y < s->nvars && ! mini_simplex_value_within_bounds(s, y)) {       
	int_heap_add(&s->infeasible_vars, y);
      }
    }
  }
  
}




/*
 * Check whether x is a free variable (i.e., no lower or upper bound
 * is asserted on x).
 * - if x is in the range 1 .. nvars-1, we check the tag
 * - if x >= nvars, x is a parameter so it's free
 */
static bool mini_simplex_var_is_free(mini_simplex_t *s, int32_t x) {
  assert(1 <= x && x < s->nvars + s->nparams);
  return x >= s->nvars || mini_simplex_bound_tag(s, x) == MINI_SIMPLEX_NO_BOUNDS;
}


/*
 * Score for an entering variable
 * - score for x = number of non-free basic variables that depend on x
 *     + 1 if x is non-free
 * - x is free if it has no lower or upper bound
 *
 * This function returns the score of x if it's smaller than best
 * or best + 1 otherwise.
 */
static uint32_t mini_simplex_var_score(mini_simplex_t *s, int32_t x, uint32_t best) {
  matrix_t *matrix;
  column_t *col;
  uint32_t i, n, score;
  int32_t r, y;

  assert(1 <= x && x < s->nvars + s->nparams);

  score = 0;
  if (! mini_simplex_var_is_free(s, x)) {
    score ++;
    if (score > best) goto done;
  }

  matrix = &s->matrix;
  col = matrix->column[x];
  n = col->size;
  for (i=0; i<n; i++) {
    r =  col->data[i].r_idx;
    if (r >= 0) {
      y = matrix_basic_var(matrix, r);
      assert(y >= 0);
      if (! mini_simplex_var_is_free(s, y)) {
	score ++;
	if (score > best) goto done;
      }
    }
  }

 done:
  return score;
}



/*
 * Check whether monomial a * x can increase or decrease without causing
 * the bounds on x to be violated.
 * - x must be in the range 1 ... x->nvars - 1
 * - a must be non null
 * - incr: true means check whether a * x can increase
 *         false means check whether a * x can decrease
 *
 * This boils down to four cases:
 *   a>0  incr       --> check whether x can increase
 *   a>0  (not incr) --> check whether x can decrease
 *   a<0  incr       --> check whether x can decrease
 *   a<0  (not incr) --> check whether x can increase
 */
static inline bool monomial_can_change(mini_simplex_t *s, int32_t x, rational_t *a, bool incr) {
  assert(1 <= x && x < s->nvars && q_is_nonzero(a));
  if (q_is_pos(a) == incr) {
    // check whether x can increase
    return mini_simplex_var_has_no_ub(s, x) || q_lt(s->val + x, s->ub + x);
  } else {
    // cehck whether x can decrease
    return mini_simplex_var_has_no_lb(s, x) || q_gt(s->val + x, s->lb + x);
  }
}


/*
 * Search for an entering variable in row
 * - x = current basic variable in that row
 * - val[x] must be above ub[x] or below lb[x]
 * - return -1 if no entering variable is found
 *   otherwise, return the index i such that row->data[i] constains the entering variable
 */
static int32_t mini_simplex_find_entering_var(mini_simplex_t *s, row_t *row, int32_t x) {
  uint32_t i, n;
  int32_t y, param;
  uint32_t score, best_score, k;
  int32_t best_i;
  bool incr;


  /*
   * The row is x + ... + a * y + ... = 0
   * We want (a * y) to increase if x needs to decrease and conversely.
   * So incr = true if val[x] > ub[x] and incr = false if val[x] < lb[x]
   */
  assert(1 <= x && x < s->nvars && ! mini_simplex_value_within_bounds(s, x));
  incr = mini_simplex_var_has_ub(s, x) && q_gt(s->val + x, s->ub + x);

  param = s->nvars; // first parameter variable

  n = row->size;
  best_i = -1;
  best_score = UINT32_MAX;
  k = 0;

  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;  
    if (y >= param || 
	(y >= 1 && y != x && monomial_can_change(s, y, &row->data[i].coeff, incr))) {      
      // a * y can go in the right direction
      score = mini_simplex_var_score(s, y, best_score);

      if (score < best_score) {
	best_score = score;
	best_i = i;
	k = 1;
      } else if (score == best_score) {
	// pick uniformly among variables with equal score
	k ++;
	if (random_uint(k) == 0) {
	  best_i = i;
	}
      }
    }
  }

  assert(best_score < UINT32_MAX || best_i < 0);

  return best_i;
}


/*
 * Check for feasibility:
 * - check for a (possibly rational) assignment that satisfies all bnounds
 * - the infeasible variables must be stored in s->infeasible_vars
 * - the current solution must be integral
 * - max_pivot is a bound on the number of pivoting steps to perform
 *   (max_pivot must be positive 0)
 * - return true if a feasible assignment is found, false otherwise
 * - false either means that max_pivot has been reached or that 
 *   a conflict row was found.
 *
 * The status flag is set as follows:
 *   solution found, all integral: s->status = MINI_SIMPLEX_SAT
 *   solution found, not all integral: s->status = MINI_SIMPLEX_UNKNOWN
 *   conflict row found: s->status = MINI_SIMPLEX_ROW_CONFLICT
 *                       s->conflict_var = basic varibale in that row
 *   max_pivot reached: s->status  = MINI_SIMPLEX_UNKNOWN
 */
static bool mini_simplex_make_feasible(mini_simplex_t *s, uint32_t max_pivot) {
  matrix_t *matrix;
  row_t *row;
  int32_t x, r, k;


  assert(mini_simplex_integral_solution(s) && max_pivot > 0);

  s->conflict_var = -1; // default: no conflict/unknown
  s->status = MINI_SIMPLEX_UNKNOWN;

  if (int_heap_is_empty(&s->infeasible_vars)) {
    // all good
    s->status = MINI_SIMPLEX_SAT;
    return true;
  }


#if 0  // TRACE
  printf("\n*** sub simplex: make feasible ***\n");
  dsolver_splx_print_tableau(stdout, s);
  dsolver_splx_print_sol_and_bounds(stdout, s);
  dsolver_splx_print_infeasible_vars(stdout, s);
  printf("-----\n");
#endif

  matrix = &s->matrix;

  do {
    x = int_heap_get_min(&s->infeasible_vars);

    assert(x >= 0);
    r = matrix_basic_row(matrix, x);
    row = matrix_row(matrix, r);

#if 0
    printf("Leaving var: ");
    dsolver_splx_print_var(stdout, s, x);
    printf("\nRow: %"PRId32"\n", r);
#endif

    if (! mini_simplex_value_within_bounds(s, x)) {
      k = mini_simplex_find_entering_var(s, row, x);
      if (k < 0) {
	// conflict
	s->status = MINI_SIMPLEX_ROW_CONFLICT;
	s->conflict_var = x;
	return false;
      } else {
	// pivot
#if 0
	printf("Entering var: ");
	dsolver_splx_print_var(stdout, s, row->data[k].c_idx);
	printf("\n\n");
#endif
	matrix_pivot(matrix, r, k);
	mini_simplex_update_solution(s, x);
	max_pivot --;

#if 0
	dsolver_splx_print_tableau(stdout, s);
	dsolver_splx_print_sol_and_bounds(stdout, s);
	dsolver_splx_print_infeasible_vars(stdout, s);
	printf("-----\n");
#endif
      }
    }

  } while (max_pivot>0  && ! int_heap_is_empty(&s->infeasible_vars));

  if (int_heap_is_empty(&s->infeasible_vars)) {
    // solution found
    if (mini_simplex_integral_solution(s)) {
      s->status = MINI_SIMPLEX_SAT;
    }
    return true;
  } else {
    // max pivot reached
    return false;
  }
}



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
void mini_simplex_check(mini_simplex_t *s, uint32_t max_pivots) {
  if (s->nvars == 0) {
    s->status = MINI_SIMPLEX_SAT;
    return;
  }

  mini_simplex_check_bounds(s);
  if (s->status != MINI_SIMPLEX_BOUND_CONFLICT) {
    mini_simplex_init_assignment(s);
    (void) mini_simplex_make_feasible(s, max_pivots);
  }
}



/*
 * EXPLANATIONS
 */

/*
 * Build an explanation for row:
 * - row is a linear combination of original equations 
 *    x_1 - p_1 = 0 
 *    x_2 - p_2 = 0
 *      ...
 *    x_k - p_l = 0
 * - the explanation is then eq(x_1), ..., eq(x_k) where
 *    x_1, ....,  x_k are the non-parameter variables in the row
 * - the assertion codes for eq(x_1), ..., eq(x_k) are added to v
 */
static void mini_simplex_explain_row(mini_simplex_t *s, row_t *row, ivector_t *v) {
  uint32_t i, n, m;
  int32_t x;

  m = s->nvars;
  n = row->size;
  for (i=0; i<n; i++) {
    x = row->data[i].c_idx;
    if (x >= 1 && x < m) {
      ivector_push(v, mini_expl_eq(x)); // eq x
    }
  }
}


/*
 * Get the conflict row
 */
row_t *mini_simplex_get_conflict_row(mini_simplex_t *s) {
  int32_t x, r;

  assert(s->status == MINI_SIMPLEX_ROW_CONFLICT);

  x = s->conflict_var;
  r = matrix_basic_row(&s->matrix, x);
  return matrix_row(&s->matrix, r);  
}


/*
 * Build the explanation of the conflicting bounds in the conflict row
 */
void mini_simplex_explain_row_conflict_bounds(mini_simplex_t *s, ivector_t *v) {
  row_t *row;
  uint32_t i, n;
  int32_t r, x, y;
  bool incr;

  assert(s->status == MINI_SIMPLEX_ROW_CONFLICT);

  x = s->conflict_var;
  r = matrix_basic_row(&s->matrix, x);
  row = matrix_row(&s->matrix, r);

  if (mini_simplex_var_has_lb(s, x) && q_lt(s->val + x, s->lb + x)) {
    // val[x] < lb[x]
    ivector_push(v, mini_expl_lb(x));
    incr = false;
  }  else {
    assert(mini_simplex_var_has_ub(s, x) && q_gt(s->val + x, s->ub + x));
    // val[x] > ub[x]
    ivector_push(v, mini_expl_ub(x));
    incr = true;
  }

  /*
   * if incr true: explain why monomials (a * y) can't increase (for y != x)
   * if incr false: explain why monomials (a * y) can't decrease (for y != x)
   */
  n = row->size;
  for (i=0; i<n; i++) {
    y = row->data[i].c_idx;
    if (y >= 1 && y != x) {
      assert(y < s->nvars && q_is_nonzero(&row->data[i].coeff));
      if (q_is_pos(&row->data[i].coeff) == incr) {
	// (a * y) can't increase with a>0 or (a * y) can't decrease with a < 0
	assert(mini_simplex_var_has_ub(s, y) && q_eq(s->val + y, s->ub + y));
	ivector_push(v, mini_expl_ub(y));
      } else {
	// (a * y) can't increase with a<0 or (a * y) can't decrease with a>0
	assert(mini_simplex_var_has_lb(s, y) && q_eq(s->val + y, s->lb + y));
	ivector_push(v, mini_expl_lb(y));
      }
    }
  }  
}


/*
 * Build the full explanation for a row conflict
 */
static void mini_simplex_explain_row_conflict(mini_simplex_t *s, ivector_t *v) {
  row_t *row;

  assert(s->status == MINI_SIMPLEX_ROW_CONFLICT);

  // explain row first
  row = mini_simplex_get_conflict_row(s);
  mini_simplex_explain_row(s, row, v);
  mini_simplex_explain_row_conflict_bounds(s, v);
}


/*
 * Explanation for a bound conflict
 */
void mini_simplex_explain_bound_conflict(mini_simplex_t *s, ivector_t *v) {
  int32_t x;

  assert(s->status == MINI_SIMPLEX_BOUND_CONFLICT);

  x = s->conflict_var;
  assert(mini_simplex_var_has_lb(s, x) && mini_simplex_var_has_ub(s, x) && q_lt(s->ub + x, s->lb + x));

  ivector_push(v, mini_expl_lb(x));
  ivector_push(v, mini_expl_ub(x));
  if ((s->tag[x] & (MINI_SIMPLEX_STRLB_MASK|MINI_SIMPLEX_STRUB_MASK)) != 0) {
    // the conflict was obtained by bound strenghtening
    ivector_push(v, mini_expl_eq(x));
  }
}


/*
 * Build a conflict explanation:
 * - s->status must be BOUND_CONFLICT or ROW_CONFLICT
 * - the conflict is stored in vector v
 * (each element of v encodes ub/lb or eq for a variable x)
 */
void mini_simplex_conflict_explanation(mini_simplex_t *s, ivector_t *v) {
  if (s->status == MINI_SIMPLEX_BOUND_CONFLICT) {
    mini_simplex_explain_bound_conflict(s, v);
  } else {
    mini_simplex_explain_row_conflict(s, v);
  }
}





/*
 * TEST
 */
bool mini_simplex_test(mini_simplex_t *s) {
  if (s->nvars > 0) {
    mini_simplex_check_bounds(s);
    if (s->status == MINI_SIMPLEX_BOUND_CONFLICT) {
      return false;
    }
    mini_simplex_init_assignment(s);

    (void) mini_simplex_make_feasible(s, 200);
#if 0
    printf("*** Done ***\n");
    dsolver_splx_print_status(stdout, s);
    printf("\n");
#endif
    if (s->status == MINI_SIMPLEX_ROW_CONFLICT) {
      return false;
    }
  }

  return true;
}
