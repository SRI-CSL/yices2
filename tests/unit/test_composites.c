/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Test of composite constructors/signature computation
 * and congruence table
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>

#include "solvers/egraph/egraph_types.h"
#include "solvers/egraph/composites.h"
#include "solvers/egraph/egraph_printer.h"
#include "utils/arena.h"


/*
 * Test partition: 11 terms, 4 classes
 * class[0] = { true, a-, b+ }
 * class[1] = { c+, d- }
 * class[2] = { e+, f+, g+ }
 * class[3] = { h+, i+, j+ }
 *
 * with classes 2 and 3 distinct
 */

#define NC 4
#define NT 11

// fixed label array
static elabel_t label[NT];


static eterm_t a = 1;
static eterm_t b = 2;
static eterm_t c = 3;
static eterm_t d = 4;
static eterm_t e = 5;
static eterm_t f = 6;
static eterm_t g = 7;
static eterm_t h = 8;
static eterm_t i = 9;
static eterm_t j = 10;


#define NCMP 50

static composite_t *composite[NCMP];
static signature_t sgn;


static congruence_table_t tbl;


/*
 * Initialize the labels
 */
static void init_labels() {
  label[0] = pos_label(0); // true
  label[a] = neg_label(0);
  label[b] = pos_label(0);

  label[c] = pos_label(1);
  label[d] = neg_label(1);

  label[e] = pos_label(2);
  label[f] = pos_label(2);
  label[g] = pos_label(2);

  label[h] = pos_label(3);
  label[i] = pos_label(3);
  label[j] = pos_label(3);
};

/*
 * Test constructors
 */
static composite_t *apply2(eterm_t f, occ_t x, occ_t y) {
  occ_t aux[2];

  aux[0] = x;
  aux[1] = y;
  return new_apply_composite(pos_occ(f), 2, aux);
}

static composite_t *update2(eterm_t f, occ_t x, occ_t y, occ_t v) {
  occ_t aux[2];

  aux[0] = x;
  aux[1] = y;
  return new_update_composite(pos_occ(f), 2, aux, v);
}

static composite_t *pair(occ_t x, occ_t y) {
  occ_t aux[2];

  aux[0] = x;
  aux[1] = y;
  return new_tuple_composite(2, aux);
}

static composite_t *lambda(occ_t x, int32_t tag) {
  return new_lambda_composite(x, tag);
}

static void build_composites() {
  composite[0] = pair(pos_occ(a), neg_occ(a));
  composite[0]->id = 100;
  composite[1] = pair(pos_occ(a), pos_occ(a));
  composite[1]->id = 101;
  composite[2] = pair(neg_occ(a), pos_occ(a));
  composite[2]->id = 102;
  composite[3] = pair(neg_occ(a), neg_occ(a));
  composite[3]->id = 103;

  composite[4] = pair(pos_occ(a), true_occ);
  composite[4]->id = 104;
  composite[5] = pair(pos_occ(a), false_occ);
  composite[5]->id = 105;
  composite[6] = pair(neg_occ(a), pos_occ(b));
  composite[6]->id = 106;
  composite[7] = pair(neg_occ(a), neg_occ(b));
  composite[7]->id = 107;

  composite[8] = apply2(f, pos_occ(c), pos_occ(c));
  composite[8]->id = 108;
  composite[9] = update2(f, pos_occ(c), neg_occ(d), pos_occ(h));
  composite[9]->id = 109;

  composite[10] = lambda(pos_occ(a), 0);
  composite[10]->id = 110;
  composite[11] = lambda(pos_occ(a), 1);
  composite[11]->id = 110;
}

static void delete_composites(uint32_t n) {
  uint32_t k;

  for (k=0; k<n; k++) {
    safe_free(composite[k]);
  }
}


static void print_composites(uint32_t n) {
  uint32_t k;

  printf("==== Terms ====\n");
  for (k=0; k<n; k++) {
    printf("cmp[%"PRIu32"] = ", k);
    print_composite(stdout, composite[k]);
    printf("\n");
  }
  fflush(stdout);
}

static void show_label(eterm_t t) {
  print_eterm_id(stdout, t);
  printf(" ---> ");
  print_label(stdout, label[t]);
  printf("\n");
}

static void print_labels(void) {
  eterm_t t;

  printf("==== Labels ====\n");
  for (t=0; t<NT; t++) {
    show_label(t);
  }
  fflush(stdout);
}

static void test_signatures(uint32_t n) {
  uint32_t k;

  for (k=0; k<n; k++) {
    printf("cmp[%"PRIu32"] = ", k);
    print_composite(stdout, composite[k]);
    printf("\n");
    signature_composite(composite[k], label, &sgn);
    printf("---> signature = ");
    print_signature(stdout, &sgn);
    printf("\n");
  }
}

static void test_eq(arena_t *m, occ_t t1, occ_t t2) {
  composite_t *tmp;

  tmp = arena_eq_composite(m, t1, t2);
  signature_composite(tmp, label, &sgn);
  print_composite(stdout, tmp);
  printf("\t---> signature = ");
  print_signature(stdout, &sgn);
  printf("\n");
}

static void test_equalities(uint32_t n) {
  uint32_t k, l;
  arena_t m;

  init_arena(&m);
  for (k=0; k<n; k++) {
    arena_push(&m);
    for (l=0; l<n; l++) {
      show_label(k);
      if (k != l) show_label(l);

      test_eq(&m, pos_occ(k), pos_occ(l));
      test_eq(&m, pos_occ(k), neg_occ(l));
      test_eq(&m, neg_occ(k), pos_occ(l));
      test_eq(&m, neg_occ(k), neg_occ(l));
      printf("\n");
    }
    arena_pop(&m);
  }
  delete_arena(&m);
}


static void test_or3(arena_t *m, occ_t t1, occ_t t2, occ_t t3) {
  occ_t aux[3];
  composite_t *tmp;

  aux[0] = t1;
  aux[1] = t2;
  aux[2] = t3;

  tmp = arena_or_composite(m, 3, aux);
  signature_or(tmp, label, &sgn);
  print_composite(stdout, tmp);
  printf("\t---> signature = ");
  print_signature(stdout, &sgn);
  printf("\n");
}

static void test_disjunctions(uint32_t n) {
  uint32_t t1, t2, t3;
  arena_t m;

  init_arena(&m);
  for (t1=0; t1<n; t1++) {
    arena_push(&m);

    for (t2=0; t2<n; t2++) {
      for (t3=0; t3<n; t3++) {
	show_label(t1);
	if (t1 != t2) show_label(t2);
	if (t1 != t3 && t2 != t3) show_label(t3);
	test_or3(&m, pos_occ(t1), pos_occ(t2), pos_occ(t3));
	printf("\n");
      }
    }

    arena_pop(&m);
  }
  delete_arena(&m);
}


static void test_congruences(uint32_t n) {
  uint32_t k;
  composite_t *tmp, *root;
  uint32_t nroots;
  composite_t *roots[n];


  nroots = 0;
  for (k=0; k<n; k++) {
    print_composite(stdout, composite[k]);
    printf("\n");
    signature_composite(composite[k], label, &sgn);
    printf("---> signature = ");
    print_signature(stdout, &sgn);
    printf("\n");

    root = congruence_table_find(&tbl, &sgn, label);
    if (root == NULL) {
      printf("---> not in congruence table\n");
    } else {
      printf("---> congruent to term: ");
      print_composite(stdout, root);
      printf("\n");
    }

    tmp = congruence_table_get(&tbl, composite[k], &sgn, label);
    printf("---> get returns: ");
    print_composite(stdout, tmp);
    printf("\n");
    if (tmp == composite[k] && root == NULL) {
      printf("---> added as congruence root\n");
      roots[nroots] = tmp;
      nroots ++;
    } else if (tmp == root && root != NULL) {
      printf("---> confirmed congruence\n");
    } else {
      printf("\n*** BUG: get/find disagree ***\n");
    }

    printf("\n");
    fflush(stdout);
  }

  for (k=0; k<nroots; k++) {
    tmp = roots[k];
    printf("---> removing root: ");
    print_composite(stdout, tmp);
    printf("\n");
    congruence_table_remove(&tbl, tmp);
  }

  printf("\n");
  fflush(stdout);
}

int main() {
  init_labels();
  init_sign_buffer(&sgn);
  init_congruence_table(&tbl, 1);

  build_composites();
  print_labels();
  print_composites(12);
  printf("\n");

  test_signatures(12);
  printf("\n");

  test_equalities(12);
  printf("\n");

  test_disjunctions(12);
  printf("\n");

  test_congruences(12);

  delete_composites(12);
  delete_congruence_table(&tbl);
  delete_sign_buffer(&sgn);

  return 0;
}
