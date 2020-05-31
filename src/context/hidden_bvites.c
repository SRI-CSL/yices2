/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * TRY TO CONVERT PAIRS OF IMPLICATIONS INTO EQUALITIES
 *
 * This code searches for pairs of assertions of the form:
 *   (c => t = a)
 *   (not(c) => t = b)
 * where a and b are bit-vector constants and c is a Boolean variable. 
 * When it finds them, it rewrites the pair to
 *    t = (ite c a b).
 *
 * Variant:
 *   (c => t = u)
 *   (not (c) => (bvsub t u) = a)
 * can be rewritten to
 *   (bvsub t u) = (ite c zero a)
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "context/context_utils.h"
#include "context/hidden_bvites.h"

#define TRACE 0

#if TRACE
#include "io/term_printer.h"
#endif


/*
 * Initialize the table
 */
void init_half_ite_table(half_ite_table_t *table, context_t *context) {
  table->context = context;
  table->terms = context->terms;
  table->data = NULL;
  table->nelems = 0;
  table->size = 0;
  init_vector_hmap(&table->index, 0);
  init_int_hset(&table->subsumed, 0);
}

/*
 * Delete it
 */
void delete_half_ite_table(half_ite_table_t *table) {
  safe_free(table->data);
  table->data = NULL;
  delete_vector_hmap(&table->index);
  delete_int_hset(&table->subsumed);
}

/*
 * Increase the size of the table
 */
static void extend_half_ite_table(half_ite_table_t *table) {
  uint32_t n;

  n = table->size;
  if (n == 0) {
    n = DEF_HALF_ITE_TABLE_SIZE;
    table->data = (half_ite_t *) safe_malloc(n * sizeof(half_ite_t));
    table->size = n;
  } else {
    n += n>>1;
    if (n > MAX_HALF_ITE_TABLE_SIZE) {
      out_of_memory();
    }
    table->data = (half_ite_t *) safe_realloc(table->data, n * sizeof(half_ite_t));
    table->size = n;
  }
}


/*
 * Add an entry (c => a = b) : t to the tablw
 */
static void add_half_ite_entry(half_ite_table_t *table, term_t c, term_t a, term_t b, term_t t) {
 uint32_t i;

  i = table->nelems;
  if (i == table->size) {
    extend_half_ite_table(table);    
  }
  assert(i < table->size);
  table->data[i].c = c;
  table->data[i].a = a;
  table->data[i].b = b;
  table->data[i].t = t;
  table->nelems ++;

  vector_hmap_add(&table->index, unsigned_term(c), i);
}


/*
 * Process a conditional equality:
 * - t is equivalent to (cond => left = right)
 * - the triple (cond, left, right) is stored in condeq
 */
void add_half_ite(half_ite_table_t *table, conditional_eq_t *condeq, term_t t) {
  add_half_ite_entry(table, condeq->cond, condeq->left, condeq->right, t);
}


/*
 * Assert the auxiliary equality (x = (ite c a b))
 * - x is a bit-vector term
 * - c is a Boolean term
 * - a and b are two bit-vector terms (constants for now)
 */
static void assert_ite_equality(half_ite_table_t *table, term_t x, term_t c, term_t a, term_t b) {
  term_table_t *terms;
  type_t tau;
  term_t aux;

  terms = table->terms;

  assert(is_bvconst_term(terms, a) && is_bvconst_term(terms, b));

  tau = term_type(terms, x);
  if (a == b) {

#if TRACE
    printf("  hidden eq: ");
    print_term(stdout, terms, x);
    printf(" == ");
    print_term(stdout, terms, a);
    printf("\n");
#endif

    add_bv_aux_eq(table->context, x, a);
  } else {
    // normalize: (ite (not c) a b) --> (ite c b a)
    if (is_neg_term(c)) {
      c = opposite_term(c);
      aux = a; a = b; b = aux;
    }
    aux = ite_term(terms, tau, c, a, b);

#if TRACE
    printf("  hidden ite eq: ");
    print_term(stdout, terms, x);
    printf(" == ");
    print_term(stdout, terms, aux);
    printf("\n");
#endif

    add_bv_aux_eq(table->context, x, aux);
  }
}


/*
 * bit-vector constant zero with n bits
 */
static term_t make_bvzero(term_table_t *terms, uint32_t n) {
  uint32_t aux[32];
  uint32_t *a;
  uint32_t i, w;
  term_t z;

  assert(n > 0);

  if (n <= 64) {
    z = bv64_constant(terms, n, 0);
  } else {
    w = (n + 31) >> 5; 
    a = aux;
    if (w > 32) {
      a = (uint32_t *) safe_malloc(w * sizeof(uint32_t));
    }
    for (i=0; i<w; i++) {
      a[i] = 0;
    }
    z = bvconst_term(terms, n, a);
    if (w  >32) {
      safe_free(a);
    }
  }

  return z;
}

/*
 * Assert the auxiliary equality (x = (ite c a zero))
 */
static void assert_ite_zero_equality(half_ite_table_t *table, term_t x, term_t c, term_t a) {
  term_table_t *terms;
  uint32_t nbits;
  term_t z;

  terms = table->terms;
  nbits = term_bitsize(terms, x);
  z = make_bvzero(terms, nbits);
  assert_ite_equality(table, x, c, a, z);
}

/*
 * Test whether two entries in the table match each other
 */
static bool check_matching_entries(half_ite_table_t *table, half_ite_t *h1, half_ite_t *h2) {
  term_table_t *terms;
  term_t x, y;

  terms = table->terms;
  if (h1->c == opposite_term(h2->c)) {
    if (h1->a == h2->a && is_bvconst_term(terms, h1->b) && is_bvconst_term(terms, h2->b)) {
      // h1: c => x = b1  and  h2: (not c) => x = b2
      // x = (ite c b1 b2)
      assert_ite_equality(table, h1->a, h1->c, h1->b, h2->b);      
      return true;
    }
    if (h1->a == h2->b && is_bvconst_term(terms, h1->b) && is_bvconst_term(terms, h2->a)) {
      // h1: c => x = b1  and h2: (not c) => a2 = x
      // x = (ite c b1 a2)
      assert_ite_equality(table, h1->a, h1->c, h1->b, h2->a);
      return true;
    }
    if (h1->b == h2->a && is_bvconst_term(terms, h1->a) && is_bvconst_term(terms, h2->b)) {
      // h1: c => a1 = x  and  h2: (not c) => x = b2
      // x = (ite c a1 b2)
      assert_ite_equality(table, h1->b, h1->c, h1->a, h2->b);
      return true;
    }
    if (h1->b == h2->b && is_bvconst_term(terms, h1->a) && is_bvconst_term(terms, h2->a)) {
      // h1: c => a1 = x  and h2: (not c) => a2 = x
      // x = (ite c a1 a2)
      assert_ite_equality(table, h1->b, h1->c, h1->a, h2->a);
      return true;
    }

    if (is_bvsub(terms, h1->a, &x, &y) && is_bvconst_term(terms, h1->b)) {
      if ((h2->a == x && h2->b == y) ||(h2->a == y && h2->b == x)) {
	// h1: c => (bvsub x y) = b  and h2: x == y
	assert_ite_zero_equality(table, h1->a, h1->c, h1->b);
	return true;
      }   
    }

    if (is_bvsub(terms, h1->b, &x, &y) && is_bvconst_term(terms, h1->a)) {
      if ((h2->a == x && h2->b == y) || (h2->a == y && h2->b == x)) {
	// h1: c => a = (bvsub x y)   and h2: x == y
	assert_ite_zero_equality(table, h1->b, h1->c, h1->a);
	return true;
      }
    }

    if (is_bvsub(terms, h2->a, &x, &y) && is_bvconst_term(terms, h2->b))  {
      if ((h1->a == x && h1->b == y) || (h1->a == y && h1->b == x)) {
	// h2: (not c) => (bvsub x y) = b and  h1: x == y
	assert_ite_zero_equality(table, h2->a, h2->c, h2->b);
	return true;
      }
    }

    if (is_bvsub(terms, h2->b, &x, &y) && is_bvconst_term(terms, h2->a)) {
      if ((h1->a == x && h1->b == y) || (h1->a == y && h1->b == x)) {
	// h2: (not c) => a = (bvsub x y) and  h1: x == y
	assert_ite_zero_equality(table, h2->b, h2->c, h2->a);
	return true;
      }
    }
  }

  return false;
}


/*
 * Mark that two terms h1->t and h2->t are subsumed
 */
static void mark_subsumed(half_ite_table_t *table, half_ite_t *h1, half_ite_t *h2) {
  int_hset_add(&table->subsumed, h1->t);
  int_hset_add(&table->subsumed, h2->t);
}


/*
 * Process a vector of n entries
 * - d = array of n indices [i0 ,...., i_{n-1}]
 * - table->data[i0] , ... , table->data[i_{n-1}] have all the same condition variable x
 */
static uint32_t  process_half_ite_vector(half_ite_table_t *table, int32_t *d, uint32_t n) {
  half_ite_t *h1, *h2;
  uint32_t i, j, k;

  k = 0;
  for (i=0; i<n; i++) {
    h1 = table->data + d[i];
    for (j=i+1; j<n; j++) {
      h2 = table->data + d[j];
      assert(h1->c == h2->c || h1->c == opposite_term(h2->c));
      if (check_matching_entries(table, h1, h2)) {
	mark_subsumed(table, h1, h2);
	k++;
      }
    }
  }

  return k;
}

/*
 * Search for complementary entries in the table.
 */
uint32_t assert_hidden_ites(half_ite_table_t *table) {
  uint32_t i, n, count;
  vhmap_vector_t *v;

  count = 0;
  n = vector_hmap_size(&table->index);
  for (i=0; i<n; i++) {
    v = vector_hmap_entry(&table->index, i);
    if (v != NULL) {
      count += process_half_ite_vector(table, v->data, v->nelems);
    }
  }
  return count;
}


/*
 * Check whether term t is in the subsumed set
 */
bool subsumed_by_hidden_ite(half_ite_table_t *table, term_t t) {
  return int_hset_member(&table->subsumed, t);
}
