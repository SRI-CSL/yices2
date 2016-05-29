/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Support for constructing Mixed-integer Gomory cuts.
 */

#include "solvers/simplex/gomory_cuts.h"
#include "utils/memalloc.h"


/*
 * Initialization: use the default size
 * - nelem is 0
 */
void init_gomory_vector(gomory_vector_t *v) {
  uint32_t n;

  n = DEF_GOMORY_VECTOR_SIZE;
  assert(n <= MAX_GOMORY_VECTOR_SIZE);

  v->tag = (uint8_t *) safe_malloc(n * sizeof(uint8_t));
  v->var = (int32_t *) safe_malloc(n * sizeof(int32_t));
  v->coeff = (rational_t *) safe_malloc(n * sizeof(rational_t));
  v->bound = (rational_t *) safe_malloc(n * sizeof(rational_t));
  v->nelems = 0;
  v->size = n;

  q_init(&v->sum);
  q_init(&v->fraction);
  q_init(&v->ext);
  q_init(&v->aux_fraction);
  q_init(&v->aux_coeff);
  q_init(&v->aux);
}


/*
 * Reset: empty the vector, also reset all the rationals to 0
 */
void reset_gomory_vector(gomory_vector_t *v) {
  uint32_t i, n;

  n = v->nelems;
  for (i=0; i<n; i++) {
    q_clear(v->coeff + i);
    q_clear(v->bound + i);
  }
  v->nelems = 0;

  q_clear(&v->sum);
  q_clear(&v->fraction);
  q_clear(&v->ext);
  q_clear(&v->aux_fraction);
  q_clear(&v->aux_coeff);
  q_clear(&v->aux);
}


/*
 * Delete: free memory
 */
void delete_gomory_vector(gomory_vector_t *v) {
  reset_gomory_vector(v);
  safe_free(v->tag);
  safe_free(v->var);
  safe_free(v->coeff);
  safe_free(v->bound);
  v->tag = NULL;
  v->var = NULL;
  v->coeff = NULL;
  v->bound = NULL;
}


/*
 * Make the vector 50% larger
 */
static void extend_gomory_vector(gomory_vector_t *v) {
  uint32_t n;

  n = v->size;
  if (n >= MAX_GOMORY_VECTOR_SIZE) {
    out_of_memory();
  }
  n += n>>1;
  assert(n > v->size);

  v->tag = (uint8_t *) safe_realloc(v->tag, n * sizeof(uint8_t));
  v->var = (int32_t *) safe_realloc(v->var, n * sizeof(int32_t));
  v->coeff = (rational_t *) safe_realloc(v->coeff, n * sizeof(rational_t));
  v->bound = (rational_t *) safe_realloc(v->bound, n * sizeof(rational_t));
  v->size = n;
}


/*
 * Add an element to the vector:
 * - x = variable
 * - a = coefficient
 * - b = bound
 * - is_int: true if x is an integer variable
 * - is_lb:  true if b is a lower bound (i.e., x >= b)
 */
void gomory_vector_add_elem(gomory_vector_t *v, int32_t x, rational_t *a, rational_t *b, 
			    bool is_int, bool is_lb) {
  uint32_t i;

  assert(!is_int || q_is_integer(b)); // if x is an integer, b must be too

  i = v->nelems;
  if (i == v->size) {
    extend_gomory_vector(v);
  }
  assert(i < v->size);

  v->tag[i] = gomory_tag(is_int, is_lb);
  v->var[i] = x;
  q_init(v->coeff + i);
  q_set(v->coeff + i, a); // make a copy
  q_init(v->bound + i);
  q_set(v->bound + i, b);
  v->nelems = i+1;
}


/*
 * GOMORY CUT
 */

/*
 * Store the fractional part of a into f
 */
static void get_fraction(rational_t *f, const rational_t *a) {
  q_set(f, a);
  q_floor(f);   
  q_sub(f, a);   // f is floor(a) - a
  q_neg(f);
}

/*
 * Compute the sum of a_i * bound_i
 * - store the result if v->sum
 * - store the fractional part in v->fraction
 * - store 1 - fractional part in v->ext
 */
static void gomory_add_bounds(gomory_vector_t *v) {
  uint32_t i, n;

  q_clear(&v->sum);
  n = v->nelems;
  for (i=0; i<n; i++) {
    q_addmul(&v->sum, v->coeff + i, v->bound + i);
  }
  get_fraction(&v->fraction, &v->sum);
  q_set_one(&v->ext);
  q_sub(&v->ext, &v->fraction);
}


/*
 * Build the Gomory cut from vector v:
 * - the cut is of the form (poly >= bound)
 * - this function stores poly in buffer and bound in *bound
 */
bool make_gomory_cut(gomory_vector_t *v, poly_buffer_t *buffer) {
  uint32_t i, n;
  rational_t *f, *e, *f_i, *c_i;


  gomory_add_bounds(v);  

  f = &v->fraction;
  e = &v->ext;         
  if (q_is_zero(f)) {
    return false;
  }

  f_i = &v->aux_fraction;
  c_i = &v->aux_coeff;

  reset_poly_buffer(buffer);

  n = v->nelems;
  for (i=0; i<n; i++) {
    /*
     * Coefficient for variable x_i
     * - if x_i is an integer, that's either f_i or f_i - 1
     * - otherwise, that's a_i.
     */
    if (gomory_var_is_int(v, i)) {
      get_fraction(f_i, v->coeff + i);
      q_set(c_i, f_i);
      // if x_i has a lower bound and f_i > 1 - f then c_i := f_i - 1
      // if x_i has an upper bound and f_i > f then c_i := f_i - 1
      if ((gomory_bound_is_lb(v, i) && q_gt(f_i, e))  ||
	  (gomory_bound_is_ub(v, i) && q_gt(f_i, f))) {
	q_sub_one(c_i);
      }
    } else {
      q_set(c_i, v->coeff + i);
    }

    if (gomory_bound_is_lb(v, i)) {
      // c_i * (x_i - l_i) with x_i >= l_i
      if (q_is_pos(c_i)) {
	q_div(c_i, e);   // c_i/(1-f)
      } else {
	q_neg(c_i);
	q_div(c_i, f);  // -c_i/f
      }
      assert(q_is_pos(c_i));
    } else {
      // c_i * (x_i - u_i) with x_i <= u_i
      if (q_is_pos(c_i)) {
	q_neg(c_i);
	q_div(c_i, f);   // -c_i/f
      } else {
	q_div(c_i, e);   //  c_i/(1-f)
      }
      assert(q_is_neg(c_i));
    }

    /*
     * Add c_i * (x_i - bound_i) to buffer
     */
    poly_buffer_add_monomial(buffer, v->var[i], c_i);
    q_mul(c_i, v->bound + i);
    poly_buffer_sub_const(buffer, c_i);
  }

  poly_buffer_sub_one(buffer);
  normalize_poly_buffer(buffer);

  return true;
}



