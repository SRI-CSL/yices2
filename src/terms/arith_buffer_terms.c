/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ARITHMETIC OPERATIONS INVOLVING BUFFERS AND TERMS
 */

#include <assert.h>

#include "terms/arith_buffer_terms.h"


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
 * Multiply b by t
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
 * Multiply b by t^d
 * - t must be an arithmetic term
 * - p->ptbl and table->pprods must be equal
 */
void arith_buffer_mul_term_power(arith_buffer_t *b, term_table_t *table, term_t t, uint32_t d) {
  arith_buffer_t aux;
  rational_t q;
  pprod_t **v;
  polynomial_t *p;
  pprod_t *r;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_arithmetic_term(table, t));

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    r = pprod_exp(b->ptbl, pprod_for_idx(table, i), d); // r = t^d
    arith_buffer_mul_pp(b, r);
    break;

  case ARITH_CONSTANT:
    q_init(&q);
    q_set_one(&q);
    q_mulexp(&q, rational_for_idx(table, i), d); // q = t^d
    arith_buffer_mul_const(b, &q);
    q_clear(&q);
    break;

  case ARITH_POLY:
    p = polynomial_for_idx(table, i);
    v = pprods_for_poly(table, p);
    init_arith_buffer(&aux, b->ptbl, b->store);
    arith_buffer_mul_monarray_power(b, p->mono, v, d, &aux);
    delete_arith_buffer(&aux);
    term_table_reset_pbuffer(table);
    break;

  default:
    r = pprod_varexp(b->ptbl, t, d);
    arith_buffer_mul_pp(b, r);
    break;
  }
}
