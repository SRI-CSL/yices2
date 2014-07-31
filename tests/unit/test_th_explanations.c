/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "solvers/egraph/egraph_types.h"
#include "solvers/egraph/theory_explanations.h"

#ifdef MINGW

/*
 * Need some version of random()
 * rand() exists on mingw
 */
static inline long int random(void) {
  return rand();
}

#endif

/*
 * Theory explanation object:
 * - av = atom vector
 * - eqv = equality vector
 * - dv = disequality vector (not used here)
 */
static void show_atoms(atom_vector_t *av) {
  uint32_t i, n, k;

  n = av->size;
  k = 0;
  for (i=0; i<n; i++) {
    if (k == 30) {
      k = 0;
      printf("\n        ");
    }
    k ++;
    printf(" %"PRId32, av->data[i]);
  }
}

static void show_eqs(eq_vector_t *eqv) {
  uint32_t i, n, k;

  n = eqv->size;
  k = 0;
  for (i=0; i<n; i++) {
    if (k == 8) {
      k = 0;
      printf("\n      ");
    }
    k ++;
    printf(" (t%"PRId32" = t%"PRId32")", eqv->data[i].lhs, eqv->data[i].rhs);
  }
}


static void show_th_explanation(th_explanation_t *e) {
  literal_t *atm;
  th_eq_t *eqs;
  uint32_t na, ne;

  printf("  atoms:");
  atm = e->atoms;
  if (atm == NULL) {
    na = 0;
    printf(" none\n");
  } else {
    na = get_av_size(atm);
    show_atoms(av_header(atm));
    printf("\n");
  }
  printf("  eqs:");
  eqs = e->eqs;
  if (eqs == NULL) {
    ne = 0;
    printf(" none\n");
  } else {
    ne = get_eqv_size(eqs);
    show_eqs(eqv_header(eqs));
    printf("\n");
  }
  printf("  %"PRIu32" atoms, %"PRId32" equalities\n", na, ne);
}


/*
 * Add n random atoms to e
 */
static void add_atoms(th_explanation_t *e, uint32_t n) {
  int32_t x;

  while (n > 0) {
    n --;
    x = random() & 0x3f;
    th_explanation_add_atom(e, x);
  }
}


/*
 * Add n random equalities
 */
static void add_eqs(th_explanation_t *e, uint32_t n) {
  int32_t x, y;

  while (n > 0) {
    n --;
    x = random() & 0x1f;
    y = random() & 0x1f;
    th_explanation_add_eq(e, x, y);
  }
}


/*
 * Force a duplicate (provided e has some equalities)
 */
static void duplicate_eq(th_explanation_t *e) {
  th_eq_t *eqs;
  uint32_t i, n;
  int32_t x, y;

  eqs = e->eqs;
  if (eqs != NULL) {
    n = get_eqv_size(eqs);
    if (n > 0) {
      i = random() % n;
      x = eqs[i].lhs;
      y = eqs[i].rhs;
      printf("  duplicate: (t%"PRId32" = t%"PRId32")\n", y, x);
      th_explanation_add_eq(e, y, x);
    }
  }
}

static void duplicate_eqs(th_explanation_t *e, uint32_t n) {
  while (n > 0) {
    n --;
    duplicate_eq(e);
  }
}


/*
 * Random test with na = number of atoms, ne = number of equalities
 */
static void random_test(th_explanation_t *e, uint32_t na, uint32_t ne) {
  printf("==== Random test ====\n");
  add_atoms(e, na);
  add_eqs(e, ne);
  duplicate_eqs(e, 4);
  show_th_explanation(e);
  cleanup_th_explanation(e);
  printf("After cleanup:\n");
  show_th_explanation(e);
  printf("\n");
  reset_th_explanation(e);
}


/*
 * Special cases for testing sort eqs
 */
static void constant_test(th_explanation_t *e, uint32_t n) {
  int32_t x, y;

  x = random() & 0x1f;
  y = random() & 0x1f;
  while (n > 0) {
    n --;
    th_explanation_add_eq(e, x, y);
  }
  printf("==== Constant test ====\n");
  show_th_explanation(e);
  cleanup_th_explanation(e);
  printf("After cleanup:\n");
  show_th_explanation(e);
  printf("\n");
  reset_th_explanation(e);
}

static void decreasing_test(th_explanation_t *e, uint32_t n) {
  int32_t x;

  x  = n + (((uint32_t) random()) & 0x1f);
  while (n > 0) {
    th_explanation_add_eq(e, n, x);
    n --;
  }

  printf("==== Decreasing test ====\n");
  show_th_explanation(e);
  cleanup_th_explanation(e);
  printf("After cleanup:\n");
  show_th_explanation(e);
  printf("\n");
  reset_th_explanation(e);
}

static void increasing_test(th_explanation_t *e, uint32_t n) {
  uint32_t i;
  int32_t x;

  x  = n + (((uint32_t) random()) & 0x1f);
  for (i=1; i<=n; i++) {
    th_explanation_add_eq(e, i, x);
  }

  printf("==== Increasing test ====\n");
  show_th_explanation(e);
  cleanup_th_explanation(e);
  printf("After cleanup:\n");
  show_th_explanation(e);
  printf("\n");
  reset_th_explanation(e);
}



int main(void) {
  th_explanation_t test;
  uint32_t i;

  init_th_explanation(&test);
  for (i=10; i<50; i++) {
    constant_test(&test, i);
  }
  delete_th_explanation(&test);

  init_th_explanation(&test);
  for (i=10; i<50; i++) {
    increasing_test(&test, i);
  }
  delete_th_explanation(&test);

  init_th_explanation(&test);
  for (i=10; i<50; i++) {
    decreasing_test(&test, i);
  }
  delete_th_explanation(&test);

  init_th_explanation(&test);
  printf("==== Initialized ====\n");
  show_th_explanation(&test);
  for (i=0; i<20; i++) {
    random_test(&test, 20, 0);
  }
  delete_th_explanation(&test);

  init_th_explanation(&test);
  printf("==== Initialized ====\n");
  show_th_explanation(&test);
  for (i=0; i<20; i++) {
    random_test(&test, 0, 20);
  }
  delete_th_explanation(&test);

  init_th_explanation(&test);
  printf("==== Initialized ====\n");
  show_th_explanation(&test);
  for (i=0; i<30; i++) {
    random_test(&test, 30, 30);
  }
  delete_th_explanation(&test);

  init_th_explanation(&test);
  printf("==== Initialized ====\n");
  show_th_explanation(&test);
  for (i=0; i<40; i++) {
    random_test(&test, 40, 40);
  }
  delete_th_explanation(&test);

  return 0;
}
