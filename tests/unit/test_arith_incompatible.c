/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test function incompatible_arithmetic_literals from term_utils.c
 */

#include <stdio.h>
#include <stdint.h>

#include "api/yices_globals.h"
#include "terms/term_utils.h"

#include "yices.h"

#define NUM_TERMS     5
#define NUM_CONSTANTS 3
#define NUM_ATOMS     (2*NUM_TERMS*NUM_CONSTANTS)

static term_t term[NUM_TERMS];
static term_t constant[NUM_CONSTANTS];
static term_t atom[NUM_ATOMS];

static void init_terms(void) {
  type_t real;

  constant[0] = yices_zero();
  constant[1] = yices_int32(1);
  constant[2] = yices_int32(-1);

  real = yices_real_type();
  term[0] = yices_new_uninterpreted_term(real);
  yices_set_term_name(term[0], "x");
  term[1] = yices_new_uninterpreted_term(real);
  yices_set_term_name(term[1], "y");
  term[2] = yices_add(term[0], term[1]); // x + y
  term[3] = yices_sub(term[0], term[1]); // x - y
  term[4] = yices_sub(term[1], term[0]); // y - x
}


static void init_atoms(void) {
  uint32_t i, j, k;
  term_t t;

  k = 0;
  for (i=0; i<NUM_TERMS; i++) {
    for (j=0; j<NUM_CONSTANTS; j++) {
      assert(k + 2 <= NUM_ATOMS);
      t = yices_arith_eq_atom(term[i], constant[j]);
      atom[k] = t;
      k ++;
      t = yices_arith_geq_atom(term[i], constant[j]);
      atom[k] = t;
      k ++;
    }
  }
}


/*
 * Test on a pair of literals l1 and l2
 */
static void test_incompatible(term_t l1, term_t l2) {
  bool tst;

  printf("Test\n");
  printf("l1 is ");
  yices_pp_term(stdout, l1, 80, 4, 6);
  printf("l2 is ");
  yices_pp_term(stdout, l2, 80, 4, 6);

  tst = incompatible_arithmetic_literals(__yices_globals.terms, l1, l2);
  if (tst) {
    printf("incompatibility test: yes\n");
  } else {
    printf("incompatibility test: no\n");
  }
  printf("\n");
  fflush(stdout);
}

static void test_atom_pair(term_t a1, term_t a2) {
  test_incompatible(a1, a2);
  test_incompatible(opposite_term(a1), a2);
  test_incompatible(a1, opposite_term(a2));
  test_incompatible(opposite_term(a1), opposite_term(a2));
}

static void test_all_pairs(void) {
  uint32_t i, j;

  for (i=0; i<NUM_ATOMS; i++) {
    for (j=0; j<NUM_ATOMS; j++) {
      test_atom_pair(atom[i], atom[j]);
    }
  }
}


int main(void) {
  yices_init();
  init_terms();
  init_atoms();
  test_all_pairs();
  yices_exit();
  return 0;
}
