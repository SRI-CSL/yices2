/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TEST OF PSEUDO_SUBST TABLE
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "context/pseudo_subst.h"


#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif




/*
 * Print the table
 */
static void print_triple(subst_triple_t *triple) {
  printf("[var = %"PRId32", map = %"PRId32", eq = %"PRId32"]", triple->var, triple->map, triple->eq);
}

static void print_subst(pseudo_subst_t *subst) {
  subst_triple_t *s;
  uint32_t i, n;

  printf("subst %p\n", subst);
  printf("  size = %"PRIu32"\n", subst->size);
  printf("  nelems = %"PRIu32"\n", subst->nelems);
  printf("  resize threshold = %"PRIu32"\n", subst->resize_threshold);

  if (subst->nelems == 0) {
    printf("  empty\n");
  } else {
    printf("  content:\n");
    n = subst->size;
    for (i=0; i<n; i++) {
      s = subst->data[i];
      if (s != NULL) {
	printf("    ");
	print_triple(s);
	printf("\n");
      }
    }
  }
}


static void print_bank(st_bank_t *bank) {
  st_block_t *b;
  uint32_t j, i, n;

  j = 0;
  b = bank->head;

  if (b == NULL) {
    assert(bank->tail == NULL && bank->free_idx == ST_BANK_SIZE);
    printf("empty bank\n\n");
    return;
  }

  while (b != bank->tail) {
    printf("block %"PRIu32"\n", j);
    for (i=0; i<ST_BANK_SIZE; i++) {
      printf("  ");
      print_triple(b->data + i);
      printf("\n");
    }
    printf("\n");
    j ++;
    b = b->next;
  }

  assert(b != NULL && b->next == NULL);

  printf("block %"PRIu32"\n", j);
  n = bank->free_idx;
  for (i=0; i<n; i++) {
    printf("  ");
    print_triple(b->data + i);
    printf("\n");
  }
  printf("\n");
}




/*
 * Test: search for x
 */
static void test_var(pseudo_subst_t *subst, term_t x) {
  subst_triple_t *s, *r;

  printf("Testing: var %"PRId32"\n", x);

  s = pseudo_subst_find(subst, x);
  if (s == NULL) {
    printf("  not in table\n");
  } else {
    assert(s->var == x);
    printf("  found: ");
    print_triple(s);
    printf("\n");
  }

  r = pseudo_subst_get(subst, x);
  assert(r != NULL && r->var == x);
  printf("  got: ");
  print_triple(r);
  printf("\n");

  if (s == NULL) {
    assert(r->map == NULL_TERM && r->eq == NULL_TERM);
    printf("  new triple\n");
    printf("  adding map: %"PRId32" --> %"PRId32"\n", x, x);
    r->map = x;
  } else {
    assert(r == s && r->map == x && r->eq == NULL_TERM);
    printf("  good triple\n");
  }

  s = pseudo_subst_find(subst, x);
  assert(s != NULL && s->var == x && s->map == x && s->eq == NULL_TERM && s == r);
  printf("  check: found ");
  print_triple(s);
  printf("\n\n");
}



/*
 * Add n random maps x
 */
static void random_tests(pseudo_subst_t *subst, uint32_t n) {
  term_t x;

  while (n > 0) {
    x = random() % 100;
    test_var(subst, x);
    n --;
  }
}


static pseudo_subst_t subst;

int main() {
  init_pseudo_subst(&subst, 1);
  printf("=== INITIAL TABLE ===\n");
  print_subst(&subst);
  print_bank(&subst.bank);

  random_tests(&subst, 10);
  printf("=== AFTER 10 RANDOM TESTS ===\n");
  print_subst(&subst);
  print_bank(&subst.bank);

  random_tests(&subst, 10);
  printf("=== AFTER 20 RANDOM TESTS ===\n");
  print_subst(&subst);
  print_bank(&subst.bank);

  reset_pseudo_subst(&subst);
  printf("=== AFTER RESET ===\n");
  print_subst(&subst);
  print_bank(&subst.bank);

  random_tests(&subst, 1000);
  printf("=== AFTER 1000 RANDOM TESTS ===\n");
  print_subst(&subst);
  print_bank(&subst.bank);

  delete_pseudo_subst(&subst);

  return 0;
}
