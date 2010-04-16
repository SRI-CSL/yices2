/*
 * ARITHMETIC OPERATIONS INVOLVING BUFFERS AND TERMS
 */

#include <assert.h>

#include "arith_buffer_terms.h"


/*
 * Add t to buffer b
 * - t must be an arithmetic term
 * - b->ptbl and table->pprods must be equal
 */
void arith_buffer_add_term(arith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  polynomial_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_arithmetic_term(table, t));
  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    arith_buffer_add_pp(b, pprod_for_idx(table, i));
    break;

  case ARITH_CONSTANT:
    arith_buffer_add_const(b, rational_for_idx(table, i));
    break;

  case ARITH_POLY:
    p = polynomial_for_idx(table, i);
    v = pprods_for_poly(table, p);
    arith_buffer_add_monarray(b, p->mono, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    arith_buffer_add_var(b, t);
    break;
  }  
}


/*
 * Subtract t from buffer b
 * - t must be an arithmetic term
 * - b->ptbl and table->pprods must be equal
 */
void arith_buffer_sub_term(arith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  polynomial_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_arithmetic_term(table, t));
  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    arith_buffer_sub_pp(b, pprod_for_idx(table, i));
    break;

  case ARITH_CONSTANT:
    arith_buffer_sub_const(b, rational_for_idx(table, i));
    break;

  case ARITH_POLY:
    p = polynomial_for_idx(table, i);
    v = pprods_for_poly(table, p);
    arith_buffer_sub_monarray(b, p->mono, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    arith_buffer_sub_var(b, t);
    break;
  }  
}


/*
 * Mulitply b by t
 * - t must be an arithmetic term
 * - b->ptbl and table->pprods must be equal
 */
void arith_buffer_mul_term(arith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  polynomial_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_arithmetic_term(table, t));
  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    arith_buffer_mul_pp(b, pprod_for_idx(table, i));
    break;

  case ARITH_CONSTANT:
    arith_buffer_mul_const(b, rational_for_idx(table, i));
    break;

  case ARITH_POLY:
    p = polynomial_for_idx(table, i);
    v = pprods_for_poly(table, p);
    arith_buffer_mul_monarray(b, p->mono, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    arith_buffer_mul_var(b, t);
    break;
  }  
}


/*
 * Add t * a to b
 * - t must be an arithmetic term
 * - b->ptbl and table->pprods must be equal
 */
void arith_buffer_add_const_times_term(arith_buffer_t *b, term_table_t *table, rational_t *a, term_t t) {
  rational_t q;
  pprod_t **v;
  polynomial_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_arithmetic_term(table, t));
  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    arith_buffer_add_mono(b, a, pprod_for_idx(table, i));
    break;

  case ARITH_CONSTANT:
    q_init(&q);
    q_set(&q, a);
    q_mul(&q, rational_for_idx(table, i));
    arith_buffer_add_const(b, &q);
    q_clear(&q);
    break;

  case ARITH_POLY:
    p = polynomial_for_idx(table, i);
    v = pprods_for_poly(table, p);
    arith_buffer_add_const_times_monarray(b, p->mono, v, a);
    term_table_reset_pbuffer(table);
    break;

  default:
    arith_buffer_add_varmono(b, a, t);
    break;
  }  
}


/*
 * Convert b to a term and reset b.
 *
 * The following simplification rules are applied:
 * 1) if b is a constant, then a constant rational is created
 * 2) if b is of the form 1.t then t is returned
 * 3) if b is of the form 1.t_1^d_1 x ... x t_n^d_n, then a power product is returned
 * 4) otherwise, a polynomial term is returned
 */
term_t arith_buffer_get_term(arith_buffer_t *b, term_table_t *table) {
  mlist_t *m;
  pprod_t *r;
  uint32_t n;
  term_t t;

  assert(b->ptbl == table->pprods);

  arith_buffer_normalize(b);

  n = b->nterms;
  if (n == 0) {
    t = zero_term;
  } else if (n == 1) {
    m = b->list; // unique monomial of b
    r = m->prod;
    if (r == empty_pp) {
      // constant polynomial
      t = arith_constant(table, &m->coeff);
    } else if (q_is_one(&m->coeff)) {
      // term or power product
      t =  pp_is_var(r) ? var_of_pp(r) : pprod_term(table, r);
    } else {
    // can't simplify
      t = arith_poly(table, b);
    }
  } else {
    t = arith_poly(table, b);
  }

  arith_buffer_reset(b);
  assert(good_term(table, t) && is_arithmetic_term(table, t));

  return t;
}



/*
 * Construct the atom (b == 0) then reset b.
 *
 * Normalize b first.
 * simplify to true if b is the zero polynomial
 * simplify to false if b is constant and non-zero
 * rewrite to (t1 == t2) if that's possible.
 */
term_t arith_buffer_get_eq0_atom(arith_buffer_t *b, term_table_t *table) {
  pprod_t *r1, *r2;
  term_t t1, t2, t;

  assert(b->ptbl == table->pprods);

  arith_buffer_normalize(b);

  if (arith_buffer_is_zero(b)) {
    t = true_term;
  } else if (arith_buffer_is_nonzero(b)) {
    t = false_term;
  } else {
    r1 = empty_pp;
    r2 = empty_pp;
    if (arith_buffer_is_equality(b, &r1, &r2)) {
      // convert to (t1 == t2)
      t1 = pp_is_var(r1) ? var_of_pp(r1) : pprod_term(table, r1);
      t2 = pp_is_var(r2) ? var_of_pp(r2) : pprod_term(table, r2);
    
      // normalize
      if (t1 > t2) {
	t = t1; t1 = t2; t2 = t;
      }

      t = arith_bineq_atom(table, t1, t2);
    } else {    
      t = arith_poly(table, b);
      t = arith_eq_atom(table, t);
    }
  }

  arith_buffer_reset(b);
  assert(good_term(table, t) && is_boolean_term(table, t));

  return t;
}

