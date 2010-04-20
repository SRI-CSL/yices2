/*
 * OPERATION COMBINING BIT-VECTOR BUFFERS AND TERMS
 */

#include <assert.h>

#include "bvlogic_buffer_terms.h"



/*
 * Copy t into buffer b
 * - t must be a bitvector term in table
 */
void bvlogic_buffer_set_term(bvlogic_buffer_t *b, term_table_t *table, term_t t) {  
  bvconst64_term_t *c64;
  bvconst_term_t *c;
  composite_term_t *d;
  uint32_t n;
  int32_t i;

  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  i = index_of(t);
  switch (table->kind[t]) {
  case BV64_CONSTANT:
    c64 = bvconst64_for_idx(table, i);
    bvlogic_buffer_set_constant64(b, c64->bitsize, c64->value);
    break;

  case BV_CONSTANT:
    c = bvconst_for_idx(table, i);
    bvlogic_buffer_set_constant(b, c->bitsize, c->data);
    break;

  case BV_ARRAY:
    d = composite_for_idx(table, i);
    
    break;

  default:
    n = bitsize_for_idx(table, i);
    bvlogic_buffer_set_bv(b, n, t);
    break;
  }
}
