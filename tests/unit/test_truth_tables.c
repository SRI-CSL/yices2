/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TRUTH TABLES FOR PURE BOOLEAN TERMS
 *
 * This tests functions from src/conditional_definitions.c:
 * - truth tables with no more than six variables
 */

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>

#include "context/conditional_definitions.h"
#include "io/term_printer.h"
#include "utils/int_array_sort.h"
#include "yices.h"


#ifndef NDEBUG
static bool array_is_sorted(term_t *a, uint32_t n) {
  uint32_t i;

  for (i=0; i+1<n; i++) {
    if (a[i] >= a[i+1]) return false;
  }
  return true;
}
#endif

/*
 * Print a truth table
 * - ttbl = 64bit encoding for the table
 * - x[0 ... n-1] = Boolean variables in increasing order
 */
static void print_truth_tbl(cond_def_collector_t *c, uint64_t ttbl, term_t *x, uint32_t n) {
  uint32_t i, k, max_k;
  uint64_t mask, bit;

  assert(array_is_sorted(x, n) && n <= 6);

  for (i=0; i<n; i++) {
    assert(is_boolean_term(c->terms, x[i]) &&
	   is_pos_term(x[i]) &&
	   term_kind(c->terms, x[i]) == UNINTERPRETED_TERM);

    printf("  %6s", term_name(c->terms, x[i]));
  }
  printf("\n");

  max_k = (1 << n); // 2^n
  assert(max_k <= 64);
  mask = 1;  // select bit 0 of ttbl

  for (k=0; k<max_k; k++) {
    for (i=0; i<n; i++) {
      bit = (k & (1 << i));
      assert(bit == 0 || bit == (1 << i));
      if (bit == 0) {
	printf("  %6s", "0");
      } else {
	printf("  %6s", "1");
      }
    }
    bit = (ttbl & mask);
    assert(bit == 0 || bit == mask);
    if (bit == 0) {
      printf("    |    0\n");
    } else {
      printf("    |    1\n");
    }
    mask <<= 1;
  }

  printf("\n");
}

/*
 * Given a term t that's a Boolean combination of n variables x[0] ... x[n-1],
 * we can encode the truth table for t as a bit-vector of 2^n elements.
 * We limit this to n <= 6, then we can represent the truth table as an unsigned
 * 64 bit integer.
 *
 * For example, if n=3 the truth table for t will look like
 *
 *     x[2]   x[1]   x[0]   |  t
 *   ------------------------------
 *       0      0      0    |  t_0
 *       0      0      1    |  t_1
 *       0      1      0    |  t_2
 *       0      1      1    |  t_3
 *       1      0      0    |  t_4
 *       1      0      1    |  t_5
 *       1      1      0    |  t_6
 *       1      1      1    |  t_7
 *
 * The truth table for t is then 8 word [t_7 t_6 ... t_0] (from high-order
 * to low-order). We extend it to 64 bit by repeating this pattern 8 times.
 *
 * All functions below compute the truth-table for a term t, assuming a fixed
 * set of Boolean variables x[0 ... n-1] (with n <= 6). The variables are
 * sorted in increasing order and are all distinct.
 */


/*
 * Constant arrays: truth tables for variables x[0 ... 5]
 */
static const uint64_t truth_tbl_var[6] = {
  0xAAAAAAAAAAAAAAAAu,  // 1010 1010 1010 1010 1010 1010 1010 1010 ...
  0xCCCCCCCCCCCCCCCCu,  // 1100 1100 1100 1100 1100 1100 1100 1100 ...
  0xF0F0F0F0F0F0F0F0u,  // 1111 0000 1111 0000 1111 0000 1111 0000 ...
  0xFF00FF00FF00FF00u,  // 1111 1111 0000 0000 1111 1111 0000 0000 ...
  0xFFFF0000FFFF0000u,  // 1111 1111 1111 1111 0000 0000 0000 0000 ..
  0xFFFFFFFF00000000u,
};


/*
 * Main procedure: recursively compute the truth table of t
 * - t must be a pure Boolean term
 * - the variables of t must be included in { x[0] ... x[n-1] }
 * - n must be no more than 6
 */
static uint64_t truth_tbl_of_term(cond_def_collector_t *c, term_t t, term_t *x, uint32_t n);

/*
 * Truth table for a variable t
 * - t must be present in x[0 ... n-1]
 */
static uint64_t truth_tbl_of_var(term_t t, term_t *x, uint32_t n) {
  uint32_t i;

  assert(is_pos_term(t) && array_is_sorted(x, n) && n <= 6);

  for (i=0; i<n; i++) {
    if (t == x[i]) break;
  }
  assert(i < n);

  return truth_tbl_var[i];
}


/*
 * Store truth table of idx in c->cache
 */
static void cache_truth_tbl(cond_def_collector_t *c, int32_t idx, uint64_t ttbl) {
  assert(good_term_idx(c->terms, idx));
  simple_cache_store_u64(&c->cache, idx, 0x1a, ttbl); // tag = 0x1a (could be anything)
}

/*
 * Recursive computation for composite terms:
 * - idx is a valid term index in the term table
 * - we use c->cache to avoid blowing up
 */
static uint64_t truth_tbl_of_ite(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *ite;
  uint64_t tc, ta, tb, r;

  assert(kind_for_idx(c->terms, idx) == ITE_TERM ||
	 kind_for_idx(c->terms, idx) == ITE_SPECIAL);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  ite = composite_for_idx(c->terms, idx);
  assert(ite->arity == 3);

  tc = truth_tbl_of_term(c, ite->arg[0], x, n); // condition
  ta = truth_tbl_of_term(c, ite->arg[1], x, n); // then part
  tb = truth_tbl_of_term(c, ite->arg[2], x, n); // else part
  r = (tc & ta) | (~tc & tb);

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_or(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *or;
  uint64_t r;
  uint32_t i, m;

  assert(kind_for_idx(c->terms, idx) == OR_TERM);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  r = 0;
  or = composite_for_idx(c->terms, idx);
  m = or->arity;
  for (i=0; i<m; i++) {
    r |= truth_tbl_of_term(c, or->arg[i], x, n);
  }

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_xor(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *xor;
  uint64_t r;
  uint32_t i, m;

  assert(kind_for_idx(c->terms, idx) == XOR_TERM);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  r = 0;
  xor = composite_for_idx(c->terms, idx);
  m = xor->arity;
  for (i=0; i<m; i++) {
    r ^= truth_tbl_of_term(c, xor->arg[i], x, n);
  }

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_iff(cond_def_collector_t *c, int32_t idx, term_t *x, uint32_t n) {
  simple_cache_entry_t *e;
  composite_term_t *iff;
  uint64_t ta, tb, r;

  assert(kind_for_idx(c->terms, idx) == EQ_TERM);

  e = simple_cache_find(&c->cache, idx);
  if (e != NULL) {
    assert(e->key == idx && e->tag == 0x1a);
    return e->val.u64;
  }

  iff = composite_for_idx(c->terms, idx);
  assert(iff->arity == 2);

  ta = truth_tbl_of_term(c, iff->arg[0], x, n);
  tb = truth_tbl_of_term(c, iff->arg[1], x, n);
  r = ~(ta ^ tb); // not xor

  cache_truth_tbl(c, idx, r);

  return r;
}

static uint64_t truth_tbl_of_term(cond_def_collector_t *c, term_t t, term_t *x, uint32_t n) {
  context_t *ctx;
  term_table_t *terms;
  uint64_t ttbl;
  term_t r;
  int32_t i;

  assert(is_boolean_term(c->terms, t));

  ctx = c->ctx;
  r = intern_tbl_get_root(&ctx->intern, t);
  if (term_is_true(ctx, r)) {
    return 0xFFFFFFFFFFFFFFFFu; // all true
  }

  if (term_is_false(ctx, r)) {
    return 0x0000000000000000u; // all false
  }

  i = index_of(r);
  terms = c->terms;

  assert(good_term_idx(c->terms, i));

  switch (kind_for_idx(terms, i)) {
  case UNINTERPRETED_TERM:
    ttbl = truth_tbl_of_var(pos_occ(i), x, n);
    break;

  case ITE_TERM:
  case ITE_SPECIAL:
    ttbl = truth_tbl_of_ite(c, i, x, n);
    break;

  case OR_TERM:
    ttbl = truth_tbl_of_or(c, i, x, n);
    break;

  case XOR_TERM:
    ttbl = truth_tbl_of_xor(c, i, x, n);
    break;

  case EQ_TERM:
    // this must be an equality between Boolean terms
    ttbl = truth_tbl_of_iff(c, i, x, n);
    break;

  default:
    // this should not happen. t is a pure Boolean term
    assert(false);
    ttbl = 0; // prevent a GCC warning
    break;
  }

  /*
   * ttbl is the truth table for i.
   * if  r is not(i), we flip all bits
   */
  if (is_neg_term(r)) {
    ttbl = ~ttbl;
  }

  return ttbl;
}

#if 0

/*
 * Truth table for the conjunction (a[0] /\ ... /\ a[m-1])
 */
static uint64_t truth_tbl_of_array(cond_def_collector_t *c, uint32_t m, term_t *a, term_t *x, uint32_t n) {
  uint64_t r;
  uint32_t i;

  r = 0xFFFFFFFFFFFFFFFFu;
  for (i=0; i<m; i++) {
    r &= truth_tbl_of_term(c, a[i], x, n);
  }

  return r;
}

#endif

/*
 * TEST PROCEDURES
 */

/*
 * Test: compute the truth table for t then print it
 * - x = variables of t
 */
static void test_ttbl(cond_def_collector_t *c, term_t t, term_t *x, uint32_t n) {
  uint64_t ttbl;

  printf("Test: ");
  yices_pp_term(stdout, t, 40, 4, 6);
  ttbl = truth_tbl_of_term(c, t, x, n);
  print_truth_tbl(c, ttbl, x, n);
}


/*
 * Binary combinations of t1 and t2
 */
static void ttbl_test_pair(cond_def_collector_t *c, term_t t1, term_t t2, term_t *x, uint32_t n) {
  term_t t;

  t = yices_and2(t1, t2);
  test_ttbl(c, t, x, n);
  t = yices_not(t);
  test_ttbl(c, t, x, n);

  t = yices_or2(t1, t2);
  test_ttbl(c, t, x, n);
  t = yices_not(t);
  test_ttbl(c, t, x, n);

  t = yices_xor2(t1, t2);
  test_ttbl(c, t, x, n);
  t = yices_not(t);
  test_ttbl(c, t, x, n);

  t = yices_implies(t1, t2);
  test_ttbl(c, t, x, n);
  t = yices_not(t);
  test_ttbl(c, t, x, n);

  t = yices_iff(t1, t2);
  test_ttbl(c, t, x, n);
  t = yices_not(t);
  test_ttbl(c, t, x, n);
}


/*
 * Some tests built on t1, t2, t3
 */
static void ttbl_test_triple(cond_def_collector_t *c, term_t t1, term_t t2, term_t t3, term_t *x, uint32_t n) {
  term_t t, u;

  t = yices_ite(t1, t2, t3);
  test_ttbl(c, t, x, n);

  t = yices_ite(t1, yices_not(t2), t3);
  test_ttbl(c, t, x, n);

  t = yices_ite(t1, t2, yices_not(t3));
  test_ttbl(c, t, x, n);

  t = yices_ite(t1, yices_not(t2), yices_not(t3));
  test_ttbl(c, t, x, n);

  t = yices_xor3(t1, t2, t3);
  test_ttbl(c, t, x, n);

  t = yices_or3(yices_not(t1), t2, t3);
  test_ttbl(c, t, x, n);
  u = yices_and2(t2, yices_not(t3));
  test_ttbl(c, u, x, n);
  t = yices_and2(u, t);
  test_ttbl(c, t, x, n);
}

/*
 * Build terms using x[0 ... n-1]
 * then show the truth tables.
 */
static void ttbl_tests(cond_def_collector_t *c, term_t *x, uint32_t n) {
  uint32_t i, j, k;

  assert(3 <= n && n <= 6);

  test_ttbl(c, yices_true(), x, n);
  test_ttbl(c, yices_false(), x, n);

  for (i=0; i<n; i++) {
    test_ttbl(c, x[i], x, n);
  }

  for (i=0; i<n; i++) {
    test_ttbl(c, yices_not(x[i]), x, n);
  }

  for (i=0; i<n; i++) {
    for (j=i+1; j<n; j++) {
      ttbl_test_pair(c, x[i], x[j], x, n);
    }
  }

  for (i=0; i<n; i++) {
    for (j=i+1; j<n; j++) {
      for (k=j+1; k<n; k++) {
	ttbl_test_triple(c, x[i], x[j], x[k], x, n);
	ttbl_test_triple(c, x[j], x[i], x[k], x, n);
	ttbl_test_triple(c, x[k], x[j], x[i], x, n);
      }
    }
  }
}


/*
 * Create boolean variables then build and test terms
 */
static void test_truth_tables(cond_def_collector_t *c) {
  term_t vars[6];
  char name[2];
  type_t btype;
  uint32_t i;

  name[0] = 'U';
  name[1] = '\0';

  btype = yices_bool_type();
  for (i=0; i<6; i++) {
    vars[i] = yices_new_uninterpreted_term(btype);
    yices_set_term_name(vars[i], name);
    name[0] ++;
  }

  int_array_sort(vars, 6);

  ttbl_tests(c, vars, 3);
  ttbl_tests(c, vars, 4);
  ttbl_tests(c, vars, 5);
  ttbl_tests(c, vars, 6);
}


int main(void) {
  context_t *ctx;
  cond_def_collector_t collect;

  yices_init();
  ctx = yices_new_context(NULL);
  init_cond_def_collector(&collect, ctx);
  test_truth_tables(&collect);
  delete_cond_def_collector(&collect);
  yices_free_context(ctx);
  yices_exit();

  return 0;
}
