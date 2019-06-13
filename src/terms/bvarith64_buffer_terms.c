/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * BIT-VECTOR OPERATION INVOLVING BUFFERS AND TERMS
 */

#include <assert.h>

#include "terms/bvarith64_buffer_terms.h"
#include "utils/int_powers.h"


/*
 * Copy t's value into buffer b
 * - t must be defined in table and be a bitvector term
 * - b->ptbl must be the same as table->pprods
 */
void bvarith64_buffer_set_term(bvarith64_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly64_t *p;
  uint32_t n;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  i = index_of(t);
  n = bitsize_for_idx(table, i);
  bvarith64_buffer_prepare(b, n); // reset b

  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith64_buffer_add_pp(b, pprod_for_idx(table, i));
    break;

  case BV64_CONSTANT:
    bvarith64_buffer_add_const(b, bvconst64_for_idx(table, i)->value);
    break;

  case BV64_POLY:
    p = bvpoly64_for_idx(table, i);
    v = pprods_for_bvpoly64(table, p);
    bvarith64_buffer_add_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith64_buffer_add_var(b, t);
    break;
  }
}



/*
 * Add t to buffer b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith64_buffer_add_term(bvarith64_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly64_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith64_buffer_add_pp(b, pprod_for_idx(table, i));
    break;

  case BV64_CONSTANT:
    bvarith64_buffer_add_const(b, bvconst64_for_idx(table, i)->value);
    break;

  case BV64_POLY:
    p = bvpoly64_for_idx(table, i);
    v = pprods_for_bvpoly64(table, p);
    bvarith64_buffer_add_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith64_buffer_add_var(b, t);
    break;
  }
}


/*
 * Subtract t from buffer b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith64_buffer_sub_term(bvarith64_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly64_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith64_buffer_sub_pp(b, pprod_for_idx(table, i));
    break;

  case BV64_CONSTANT:
    bvarith64_buffer_sub_const(b, bvconst64_for_idx(table, i)->value);
    break;

  case BV64_POLY:
    p = bvpoly64_for_idx(table, i);
    v = pprods_for_bvpoly64(table, p);
    bvarith64_buffer_sub_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith64_buffer_sub_var(b, t);
    break;
  }
}



/*
 * Multiply b by t
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith64_buffer_mul_term(bvarith64_buffer_t *b, term_table_t *table, term_t t) {
  pprod_t **v;
  bvpoly64_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith64_buffer_mul_pp(b, pprod_for_idx(table, i));
    break;

  case BV64_CONSTANT:
    bvarith64_buffer_mul_const(b, bvconst64_for_idx(table, i)->value);
    break;

  case BV64_POLY:
    p = bvpoly64_for_idx(table, i);
    v = pprods_for_bvpoly64(table, p);
    bvarith64_buffer_mul_bvpoly(b, p, v);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith64_buffer_mul_var(b, t);
    break;
  }
}


/*
 * Add a * t to b
 * - t must be defined in table and be a bitvector term of same bitsize as b
 * - b->ptbl must be the same as table->pprods
 */
void bvarith64_buffer_add_const_times_term(bvarith64_buffer_t *b, term_table_t *table, uint64_t a, term_t t) {
  pprod_t **v;
  bvpoly64_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    bvarith64_buffer_add_mono(b, a, pprod_for_idx(table, i));
    break;

  case BV64_CONSTANT:
    a *= bvconst64_for_idx(table, i)->value;
    bvarith64_buffer_add_const(b, a);
    break;

  case BV64_POLY:
    p = bvpoly64_for_idx(table, i);
    v = pprods_for_bvpoly64(table, p);
    bvarith64_buffer_add_const_times_bvpoly(b, p, v, a);
    term_table_reset_pbuffer(table);
    break;

  default:
    bvarith64_buffer_add_varmono(b, a, t);
    break;
  }
}


/*
 * Multiply b by t^d
 * - t must be an arithmetic term
 * - p->ptbl and table->pprods must be equal
 */
void bvarith64_buffer_mul_term_power(bvarith64_buffer_t *b, term_table_t *table, term_t t, uint32_t d) {
  bvarith64_buffer_t aux;
  bvpoly64_t *p;
  pprod_t **v;
  pprod_t *r;
  uint64_t c;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (table->kind[i]) {
  case POWER_PRODUCT:
    r = pprod_exp(b->ptbl, pprod_for_idx(table, i), d); // r = t^d
    bvarith64_buffer_mul_pp(b, r);
    break;

  case BV64_CONSTANT:
    c = upower64(bvconst64_for_idx(table, i)->value, d); // c := t^d
    bvarith64_buffer_mul_const(b, c);
    break;

  case BV64_POLY:
    p = bvpoly64_for_idx(table, i);
    v = pprods_for_bvpoly64(table, p);
    init_bvarith64_buffer(&aux, b->ptbl, b->store);
    bvarith64_buffer_mul_bvpoly_power(b, p, v, d, &aux);
    delete_bvarith64_buffer(&aux);
    term_table_reset_pbuffer(table);
    break;

  default:
    r = pprod_varexp(b->ptbl, t, d);
    bvarith64_buffer_mul_pp(b, r);
    break;
  }
}
