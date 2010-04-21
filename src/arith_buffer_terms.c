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


