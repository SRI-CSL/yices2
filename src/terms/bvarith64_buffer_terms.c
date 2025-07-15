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
#include "terms/term_utils.h"
#include "utils/int_powers.h"

/*
 * Initialize an auxiliary buffer aux, using the same store and prod table as b
 */
static void init_aux64_buffer(bvarith64_buffer_t *aux, bvarith64_buffer_t *b) {
  init_bvarith64_buffer(aux, b->ptbl, b->store);
  bvarith64_buffer_prepare(aux, b->bitsize);
}

/*
 * Try to convert t to an arithmetic expression
 * - t must be a bv-array term
 * - return true if that succeeds, and store the result in buffer b
 * - otherwise return false and leave b unchanged.
 *
 * We currently just check for the case t = (bvnot x) or t = x.
 * If t is (bvnot x), we store -1 - x in b.
 */
static bool convert_bvarray_to_bvarith64(term_table_t *table, term_t t, bvarith64_buffer_t *b) {
  term_t t0;
  bool negated;

  if (bvarray_convertible_to_term(table, t, &t0, &negated)) {
    if (negated) {
      // t is (bvnot t0) == (-t0) - 1
      bvarith64_buffer_sub_one(b);
      bvarith64_buffer_sub_term(b, table, t0);
    } else {
      bvarith64_buffer_add_term(b, table, t0);
    }
    bvarith64_buffer_normalize(b);
    return true;
  }

  return false;
}


/*
 * Copy t's value into buffer b
 * - t must be defined in table and be a bitvector term
 * - b->ptbl must be the same as table->pprods
 */
void bvarith64_buffer_set_term(bvarith64_buffer_t *b, term_table_t *table, term_t t) {
  uint32_t n;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t));

  n = term_bitsize(table, t);
  bvarith64_buffer_prepare(b, n); // reset b
  bvarith64_buffer_add_term(b, table, t);
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
  term_t t0;
  bool negated;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (kind_for_idx(table, i)) {
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

  case BV_ARRAY:
    if (bvarray_convertible_to_term(table, t, &t0, &negated)) {
      if (negated) {
	// t is (bvnot t0) == (-t0) - 1
	bvarith64_buffer_sub_one(b);
	bvarith64_buffer_sub_term(b, table, t0);
      } else {
	bvarith64_buffer_add_term(b, table, t0);
      }
    } else {
      bvarith64_buffer_add_var(b, t);
    }
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
  term_t t0;
  bool negated;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (kind_for_idx(table, i)) {
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

  case BV_ARRAY:
    if (bvarray_convertible_to_term(table, t, &t0, &negated)) {
      if (negated) {
	// t is (bvnot t0) == (-t0) - 1
	bvarith64_buffer_add_one(b);
	bvarith64_buffer_add_term(b, table, t0);
      } else {
	bvarith64_buffer_sub_term(b, table, t0);
      }
    } else {
      bvarith64_buffer_sub_var(b, t);
    }
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
  bvarith64_buffer_t aux;
  pprod_t **v;
  bvpoly64_t *p;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (kind_for_idx(table, i)) {
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

  case BV_ARRAY:
    init_aux64_buffer(&aux, b);
    if (convert_bvarray_to_bvarith64(table, t, &aux)) {
      bvarith64_buffer_mul_buffer(b, &aux);
    } else {
      bvarith64_buffer_mul_var(b, t);
    }
    delete_bvarith64_buffer(&aux);
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
  term_t t0;
  bool negated;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (kind_for_idx(table, i)) {
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

  case BV_ARRAY:
    if (bvarray_convertible_to_term(table, t, &t0, &negated)) {
      if (negated) {
	// t is (bvnot t0) == (-t0) - 1
	bvarith64_buffer_sub_const(b, a);
	bvarith64_buffer_add_const_times_term(b, table, -a, t0);
      } else {
	bvarith64_buffer_add_const_times_term(b, table, a, t0);
      }
    } else {
      bvarith64_buffer_add_varmono(b, a, t);
    }
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
  bvarith64_buffer_t aux, aux2;
  bvpoly64_t *p;
  pprod_t **v;
  pprod_t *r;
  uint64_t c;
  int32_t i;

  assert(b->ptbl == table->pprods);
  assert(pos_term(t) && good_term(table, t) && is_bitvector_term(table, t) &&
         term_bitsize(table, t) == b->bitsize);

  i = index_of(t);
  switch (kind_for_idx(table, i)) {
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
    init_aux64_buffer(&aux, b);
    bvarith64_buffer_mul_bvpoly_power(b, p, v, d, &aux);
    delete_bvarith64_buffer(&aux);
    term_table_reset_pbuffer(table);
    break;

  case BV_ARRAY:
    init_aux64_buffer(&aux, b);
    if (convert_bvarray_to_bvarith64(table, t, &aux)) {
      init_aux64_buffer(&aux2, b);
      bvarith64_buffer_mul_buffer_power(b, &aux, d, &aux2);
      delete_bvarith64_buffer(&aux2);
    } else {
      r = pprod_varexp(b->ptbl, t, d);
      bvarith64_buffer_mul_pp(b, r);
    }
    delete_bvarith64_buffer(&aux);
    break;

  default:
    r = pprod_varexp(b->ptbl, t, d);
    bvarith64_buffer_mul_pp(b, r);
    break;
  }
}
