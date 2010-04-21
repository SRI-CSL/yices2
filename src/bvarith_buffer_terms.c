/*
 * BIT-VECTOR OPERATION INVOLVING BUFFERS AND TERMS
 */

#include <assert.h>

#include "bvarith_buffer_terms.h"


/*
 * Copy t's value into buffer b
 * - t must be defined in table and be a bitvector term
 * - b->ptbl must be the same as table->pprods
 */
void bvarith_buffer_set_term(bvarith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly_t *p;
  uint32_t n;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  i = index_of(t);
  n = bitsize_for_idx(table, i);
  bvarith_buffer_prepare(b, n); // reset b

  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith_buffer_add_pp(b, pprod_for_idx(table, i));
    break;

  case BV_CONSTANT:
    bvarith_buffer_add_const(b, bvconst_for_idx(table, i)->data);
    break;

  case BV_POLY:
    p = bvpoly_for_idx(table, i);
    v = pprods_for_bvpoly(table, p);
    bvarith_buffer_add_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith_buffer_add_var(b, t);
    break;
  }
}



/*
 * Add t to buffer b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith_buffer_add_term(bvarith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) && 
	 term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith_buffer_add_pp(b, pprod_for_idx(table, i));
    break;

  case BV_CONSTANT:
    bvarith_buffer_add_const(b, bvconst_for_idx(table, i)->data);
    break;

  case BV_POLY:
    p = bvpoly_for_idx(table, i);
    v = pprods_for_bvpoly(table, p);
    bvarith_buffer_add_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith_buffer_add_var(b, t);
    break;
  }
}


/*
 * Subtract t from buffer b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith_buffer_sub_term(bvarith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) && 
	 term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith_buffer_sub_pp(b, pprod_for_idx(table, i));
    break;

  case BV_CONSTANT:
    bvarith_buffer_sub_const(b, bvconst_for_idx(table, i)->data);
    break;

  case BV_POLY:
    p = bvpoly_for_idx(table, i);
    v = pprods_for_bvpoly(table, p);
    bvarith_buffer_sub_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith_buffer_add_var(b, t);
    break;
  }
}



/*
 * Multiply b by t
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith_buffer_mul_term(bvarith_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) && 
	 term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith_buffer_mul_pp(b, pprod_for_idx(table, i));
    break;

  case BV_CONSTANT:
    bvarith_buffer_mul_const(b, bvconst_for_idx(table, i)->data);
    break;

  case BV_POLY:
    p = bvpoly_for_idx(table, i);
    v = pprods_for_bvpoly(table, p);
    bvarith_buffer_mul_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith_buffer_add_var(b, t);
    break;
  }
}



