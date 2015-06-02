/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <assert.h>

#include "solvers/simplex/integrality_constraints.h"
#include "utils/memalloc.h"


/*
 * Allocate and initialize an array of n monomials
 */
static monomial_t *alloc_mono_array(uint32_t n) {
  monomial_t *tmp;
  uint32_t i;

  assert(n <= INT_CONSTRAINT_MAX_SIZE);
  tmp = (monomial_t *) safe_malloc(n * sizeof(monomial_t));
  for (i=0; i<n; i++) {
    q_init(&tmp[i].coeff);
  }
  return tmp;
}

/*
 * Realloc: n = current size, m = new size
 */
static monomial_t *realloc_mono_array(monomial_t *a, uint32_t n, uint32_t m) {
  monomial_t *tmp;
  uint32_t i;

  assert(n <= m && m <= INT_CONSTRAINT_MAX_SIZE);

  tmp = (monomial_t *) safe_realloc(a, m * sizeof(monomial_t));
  for (i=n; i<m; i++) {
    q_init(&tmp[i].coeff);
  }
  return tmp;
}

/*
 * Reset array a: clear all the coefficients
 * - n = size of the array
 */
static void reset_mono_array(monomial_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    q_clear(&a[i].coeff);
  }
}

/*
 * Delete: free the coefficients first
 */
static void delete_mono_array(monomial_t *a, uint32_t n) {
  reset_mono_array(a, n);
  safe_free(a);
}


/*
 * Allocate and initialize an array of n rationals
 */
static rational_t *alloc_rational_array(uint32_t n) {
  rational_t *tmp;
  uint32_t i;

  assert(n <= (UINT32_MAX/sizeof(rational_t)));

  tmp = (rational_t *) safe_malloc(n * sizeof(rational_t));
  for (i=0; i<n; i++) {
    q_init(tmp + i);
  }
  return tmp;
}

/*
 * Realloc: n = current size, m = new size
 */
static rational_t *realloc_rational_array(rational_t *a, uint32_t n, uint32_t m) {
  rational_t *tmp;
  uint32_t i;

  assert(n <= m && m <= (UINT32_MAX/sizeof(rational_t)));
  tmp = (rational_t *) safe_realloc(a, m * sizeof(rational_t));
  for (i=n; i<m; i++) {
    q_init(tmp + i);
  }
  return tmp;
}

/*
 * Reset: clear all rationals
 * - a = array, n = size of the array
 */
static void reset_rational_array(rational_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    q_clear(a + i);
  }
}

/*
 * Delete: free the rationals first
 */
static void delete_rational_array(rational_t *a, uint32_t n) {
  reset_rational_array(a, n);
  safe_free(a);
}


/*
 * Initialize a constraint descriptor.
 */
void init_int_constraint(int_constraint_t *cnstr) {
  uint32_t n;
  
  n = INT_CONSTRAINT_DEF_SIZE;
  cnstr->sum = alloc_mono_array(n);
  cnstr->sum_nterms = 0;
  cnstr->sum_size = n;

  cnstr->fixed_sum = alloc_mono_array(n);
  cnstr->fixed_val = alloc_rational_array(n);
  cnstr->is_int = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  cnstr->fixed_nterms = 0;
  cnstr->fixed_size = n;

  q_init(&cnstr->constant); // constant is zero
  q_init(&cnstr->num_gcd);
  q_init(&cnstr->den_lcm);
  q_init(&cnstr->gcd);
  q_init(&cnstr->fixed_constant);
  q_init(&cnstr->period);
  q_init(&cnstr->phase);
  q_init(&cnstr->q0);
  q_init(&cnstr->q1);
}


/*
 * Reset
 */
void reset_int_constraint(int_constraint_t *cnstr) {
  reset_mono_array(cnstr->sum, cnstr->sum_size);
  cnstr->sum_nterms = 0;

  reset_mono_array(cnstr->fixed_sum, cnstr->fixed_size);
  reset_rational_array(cnstr->fixed_val, cnstr->fixed_size);
  cnstr->fixed_nterms = 0;

  q_clear(&cnstr->constant);
  q_clear(&cnstr->num_gcd);
  q_clear(&cnstr->den_lcm);
  q_clear(&cnstr->gcd);
  q_clear(&cnstr->fixed_constant);
  q_clear(&cnstr->period);
  q_clear(&cnstr->phase);
  q_clear(&cnstr->q0);
  q_clear(&cnstr->q1);
}


/*
 * Delete the whole thing
 */
void delete_int_constraint(int_constraint_t *cnstr) {
  delete_mono_array(cnstr->sum, cnstr->sum_size);
  delete_mono_array(cnstr->fixed_sum, cnstr->fixed_size);
  delete_rational_array(cnstr->fixed_val, cnstr->fixed_size);
  safe_free(cnstr->is_int);

  q_clear(&cnstr->constant);
  q_clear(&cnstr->num_gcd);
  q_clear(&cnstr->den_lcm);
  q_clear(&cnstr->gcd);
  q_clear(&cnstr->fixed_constant);
  q_clear(&cnstr->period);
  q_clear(&cnstr->phase);
  q_clear(&cnstr->q0);
  q_clear(&cnstr->q1);

  cnstr->sum = NULL;
  cnstr->fixed_sum = NULL;
  cnstr->fixed_val = NULL;
  cnstr->is_int = NULL;
}


/*
 * Make the sum array 50% larger
 */
static void int_constraint_extend_sum(int_constraint_t *cnstr) {
  uint32_t n; // new size

  n = cnstr->sum_size + 1;
  n += (n >> 1);
  if (n > INT_CONSTRAINT_MAX_SIZE) {
    out_of_memory();
  }
  assert(n > cnstr->sum_size);
  cnstr->sum = realloc_mono_array(cnstr->sum, cnstr->sum_size, n);
  cnstr->sum_size = n;
}


/*
 * Make the fixed_sum arrays larger
 */
static void int_constraint_extend_fixed_sum(int_constraint_t *cnstr) {
  uint32_t n, m;

  n = cnstr->fixed_size;
  m = n + 1;
  m += (m >> 1); // m is the new size
  if (m > INT_CONSTRAINT_MAX_SIZE) {
    out_of_memory();
  }
  assert(m > n);
  cnstr->fixed_sum = realloc_mono_array(cnstr->fixed_sum, n, m);
  cnstr->fixed_val = realloc_rational_array(cnstr->fixed_val, n, m);
  cnstr->is_int = (uint8_t *) safe_realloc(cnstr->is_int, m * sizeof(uint8_t));
  cnstr->fixed_size = m;
}



/*
 * Compute the fractional part of q (i.e., q - floor(q))
 * - store the result in f
 */
static void q_set_fraction(rational_t *f, const rational_t *q) {
  q_set(f, q); // f := q
  q_floor(f);  // f := floor(q)
  q_neg(f);    // f := - floor(q)
  q_add(f, q); // f := q - floor(q)
}



/*
 * Add a monomial to the non-fixed part
 * - a = rational coefficient
 * - x = integer variable
 * - x must not occur already
 */
void int_constraint_add_mono(int_constraint_t *cnstr, const rational_t *a, int32_t x) {
  uint32_t i;

  assert(! q_is_integer(a));

  i = cnstr->sum_nterms;
  if (i == cnstr->sum_size) {
    int_constraint_extend_sum(cnstr);
  }
  assert(i < cnstr->sum_size);

  q_set_fraction(&cnstr->sum[i].coeff, a);
  cnstr->sum[i].var = x;
  cnstr->sum_nterms = i + 1;
}


/*
 * Add a monomial to the fixed part
 * - a = rational coefficient
 * - x = variable
 * - is_int = true if x is an integer variable
 * - val = value of x
 */
void int_constraint_add_fixed_mono(int_constraint_t *cnstr, const rational_t *a, int32_t x, bool is_int, const rational_t *val) {
  uint32_t i;

  assert(!is_int || !q_is_integer(a));

  i = cnstr->fixed_nterms;
  if (i == cnstr->fixed_size) {
    int_constraint_extend_fixed_sum(cnstr);
  }
  assert(i < cnstr->fixed_size);

  if (is_int) {
    q_set_fraction(&cnstr->fixed_sum[i].coeff, a);
  } else {
    q_set(&cnstr->fixed_sum[i].coeff, a);
  }
  cnstr->fixed_sum[i].var = x;
  q_set(cnstr->fixed_val + i, val);
  cnstr->is_int[i] = is_int;
  cnstr->fixed_nterms = i + 1;
}


/*
 * Add the constant term a
 */
void int_constraint_add_constant(int_constraint_t *cnstr, const rational_t *a) {
  assert(! q_is_integer(a));
  q_set_fraction(&cnstr->constant, a);
}


/*
 * Compute the gcd of all non-fixed coefficients
 * - if the coefficients are a[0]/b[0] ... a[k]/b[k]
 *   then this function computes gcd(a[0], ..., a[k])
 *   and lcm(b[0] ... b[k]).
 * - result:
 *    cnstr->num_gcd := gcd(a[0] ... a[k])
 *    cnstr->den_lcm := lcm(b[0] ... b[k])
 *    cnstr->gcd := gcd(a[0] ... a[k])/lcm(b[0] ... b[k])
 */
static void int_constraint_build_gcd(int_constraint_t *cnstr) {
  rational_t *l, *d, *aux;
  uint32_t i, n;

  assert(cnstr->sum_nterms > 0);

  n = cnstr->sum_nterms;
  d = &cnstr->num_gcd;
  l = &cnstr->den_lcm;
  aux = &cnstr->q0;

  q_get_den(l, &cnstr->sum[0].coeff); // b[0]
  q_get_num(d, &cnstr->sum[0].coeff); // a[0]
  for (i=1; i<n; i++) {
    assert(q_is_nonzero(l) && q_is_nonzero(d));
    q_get_den(aux, &cnstr->sum[i].coeff); // b[i]
    q_lcm(l, aux);
    q_get_num(aux, &cnstr->sum[i].coeff); // a[i]
    q_gcd(d, aux);
  }

  q_set(&cnstr->gcd, d);
  q_div(&cnstr->gcd, l); // gcd := d/l
}


/*
 * Compute the sum of the fixed terms
 * - skip term c.x if c is a multiple of cnstr->gcd
 * - the resut is stored in sum_const
 * - store the variables that are not skipped into vector v
 */
static void int_constraint_build_fixed_constant(int_constraint_t *cnstr, ivector_t *v) {
  rational_t *s, *val;
  monomial_t *fixed;
  uint32_t i, n;
  int32_t x;

  s = &cnstr->fixed_constant;
  q_set(s, &cnstr->constant);

  fixed = cnstr->fixed_sum;
  val = cnstr->fixed_val;
  n = cnstr->fixed_nterms;
  for (i=0; i<n; i++) {
    x = fixed[i].var;
    if (cnstr->is_int[i] && q_divides(&cnstr->gcd, &fixed[i].coeff)) {
      // skip this term
      continue;
    }
    ivector_push(v, x);
    q_addmul(s, &fixed[i].coeff, &val[i]);
  }
}


/*
 * Test whether denominator of gcd is a multiple of denominator of fixed_constant.
 */
static bool test_feasibility_condition(int_constraint_t *cnstr) {
  q_get_den(&cnstr->q0, &cnstr->gcd); // denominator of gcd
  q_get_den(&cnstr->q1, &cnstr->fixed_constant); // denominator of fixed constant
  return q_integer_divides(&cnstr->q1, &cnstr->q0);
}


/*
 * Degenerate case: if all variables are fixed, we compute the sum of the
 * fixed terms and we check whether that's an integer.
 */
static bool degenerate_int_constraint_is_feasible(int_constraint_t *cnstr, ivector_t *v) {
  rational_t *s, *val;
  monomial_t *fixed;
  uint32_t i, n;
  int32_t x;

  assert(cnstr->sum_nterms == 0);
  s = &cnstr->fixed_constant;
  q_set(s, &cnstr->constant);

  fixed = cnstr->fixed_sum;
  val = cnstr->fixed_val;
  n = cnstr->fixed_nterms;
  for (i=0; i<n; i++) {
    x = fixed[i].var;
    ivector_push(v, x);
    q_addmul(s, &fixed[i].coeff, &val[i]);
  }
  
  return q_is_integer(s);
}


/*
 * Check feasibility
 */
bool int_constraint_is_feasible(int_constraint_t *cnstr, ivector_t *v) {
  if (cnstr->sum_nterms == 0) {
    return degenerate_int_constraint_is_feasible(cnstr, v);
  }
  int_constraint_build_gcd(cnstr);
  int_constraint_build_fixed_constant(cnstr, v);
  return test_feasibility_condition(cnstr);
}


/*
 * Get the i-th non-fixed variable of cnstr
 * - i must be less than cnstr->sum_nterms
 */
int32_t int_constraint_get_var(int_constraint_t *cnstr, uint32_t i) {
  assert(i < cnstr->sum_nterms);
  return cnstr->sum[i].var;
}


/*
 * Perdiod computation for period of the i-th variable.
 * We compute gcd(1, a_1/b_1, ... a_n/b_n)  (skipping a_i/b_i).
 * The GCD is gcd(1, a_1, ..., a_n)/lcm(1, b_1, ..., b_n),
 * which simplifies to 1/lcm(1, b_1,...,b_n).
 *
 * Then we have a_i/b_i x_i = GCD * some integer + sum of fixed terms
 * So the period for x_i is (GCD/(a_i/b_i)) = GCD * b_i / a_i.
 *
 * Result:
 *   cnstr->den_lcm = lcm(1, b_1, ..., b_n)
 *   cnstr->gcd = 1/lcm(1, b_1, ..., b_n)
 *   cnstr->period = 1/lcm(1, b_1, ..., b_n) / (a_i/b_i)
 *
 */
static void int_constraint_build_var_period(int_constraint_t *cnstr, uint32_t i) {
  rational_t *l, *aux;
  uint32_t j, n;

  assert(i < cnstr->sum_nterms);

  n = cnstr->sum_nterms;
  l = &cnstr->den_lcm;
  aux = &cnstr->q0;

  q_set_one(l);

  for (j=0; j<n; j++) {
    assert(q_is_nonzero(l));
    if (j != i) {
      q_get_den(aux, &cnstr->sum[j].coeff);
      q_lcm(l, aux);
    }
  }

  // set gcd to 1/l
  q_set_one(&cnstr->gcd);
  q_div(&cnstr->gcd, l);

  // set period to gcd/(a_i/b_i)
  q_set(&cnstr->period, &cnstr->gcd);
  aux = &cnstr->sum[i].coeff; // coefficient a_i/b_i
  q_div(&cnstr->period, aux);
}


/*
 * Compute the phase for a variable x_i
 * - assumes cnstr->period contains the period of x_i
 * - the phase = - (sum of all constant terms)/(a_i/b_i)
 *   where a_i/b_i is the coefficient of x_i
 *
 * Optimization: if term (a_j/b_j) * x_j occurs in the fixed sum
 * where x_j is an integer and (a_j/b_j)/(a_i/b_i) is a multiple
 * of the period, when we skip this term.
 */
static void int_constraint_build_var_phase(int_constraint_t *cnstr, uint32_t i, ivector_t *v) {
  rational_t *s, *val, *c, *aux;
  monomial_t *fixed;
  uint32_t j, n;
  int32_t x;

  assert(i < cnstr->sum_nterms);

  c = &cnstr->sum[i].coeff; // coefficient of i = a[i]/b[i]

  aux = &cnstr->q0;  // to store intermediate coefficients: (a[j]/b[j])/c


  // compute the sum of all fixed_terms/c
  s = &cnstr->phase;
  q_set(s, &cnstr->constant);
  q_div(s, c);

  fixed = cnstr->fixed_sum;
  val = cnstr->fixed_val;
  n = cnstr->fixed_nterms;
  for (j=0; j<n; j++) {
    q_set(aux, &fixed[j].coeff);
    q_div(aux, c);  // scaled coefficient
    if (cnstr->is_int[j] && q_divides(&cnstr->period, aux)) {
      // skip this term
      continue;
    }
    x = fixed[j].var;
    ivector_push(v, x);
    q_addmul(s, aux, &val[j]);
  }

  q_neg(s); // negate
  q_normalize(s);
}


/*
 * Auxiliary function: find the remainder of a divided by b
 * - the result is stored in a in place
 * - aux is another rational for temporary results
 */
static void q_generalized_rem(rational_t *a, const rational_t *b, rational_t *aux) {
  q_set(aux, a);
  q_div(aux, b); // aux = a/b
  q_floor(aux);  // aux = floor(a/b)
  q_submul(a, aux, b); // a := a - aux * b
}

/*
 * Compute period and phase of the i-th non-fixed variable of cnstr
 * - i must be between 0 and cnstr->sum_nterms.
 * - store the explanation in vector v = set of fixed variables that
 *   contribute to the phase
 * - period and phase are stored in cnstr->period and cnstr->phase
 */
void int_constraint_period_of_var(int_constraint_t *cnstr, uint32_t i, ivector_t *v) {
  assert(i < cnstr->sum_nterms);
  int_constraint_build_var_period(cnstr, i);
  int_constraint_build_var_phase(cnstr, i, v);

  // normalize the phase
  q_generalized_rem(&cnstr->phase, &cnstr->period, &cnstr->q0);
}

