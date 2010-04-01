/*
 * Test hash-consing of power products
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "pprod_table.h"


/*
 * Display power products
 */
static void print_varexp_array(FILE *f, varexp_t *a, uint32_t n) {
  uint32_t i, d;

  if (n == 0) {
    fprintf(f, "[]");
    return;
  }
  d = a[0].exp;
  fprintf(f, "[x_%"PRId32, a[0].var);
  if (d != 1) {
    fprintf(f, "^%"PRIu32, d);
  }
  for (i=1; i<n; i++) {
    d = a[i].exp;
    fprintf(f, " x_%"PRId32, a[i].var);
    if (d != 1) {
      fprintf(f, "^%"PRIu32, d);
    }
  }
  fprintf(f, "]");
}


static void print_pp_buffer0(FILE *f, pp_buffer_t *b) {
  print_varexp_array(f, b->prod, b->len);
}

static void print_pprod0(FILE *f, pprod_t *p) {
  if (pp_is_var(p)) {
    fprintf(f, "[x_%"PRId32"]", var_of_pp(p));
  } else if (pp_is_empty(p)) {
    fprintf(f, "[]");
  } else {
    print_varexp_array(f, p->prod, p->len);
  }
}



/*
 * Table + buffer for tests
 */
static pprod_table_t ptbl;
static pp_buffer_t buffer;

/*
 * Array of all power products
 */
#define NUM_PRODS 300

static pprod_t *p[NUM_PRODS];
static uint32_t num_prods;

/*
 * Check whether q is equal to a product p[k]
 * - if so, check whether p[k] = q
 * - otherwise, add a at the end of the array
 */
static void check_product(pprod_t *q) {
  uint32_t k;

  for (k=0; k<num_prods; k++) {
    if (pprod_equal(q, p[k])) {
      break;
    }
  }

  if (k < num_prods) {
    printf("--> equal to p[%"PRIu32"]\n", k);
    if (p[k] != q) {
      printf("BUG: HASH CONSING FAILED\n");
      fflush(stdout);
      abort();
    }
  } else if (num_prods < NUM_PRODS) {
    printf("--> stored as p[%"PRIu32"]\n", k);
    p[k] = q;
    num_prods ++;
  }  
}


int main(void) {
  uint32_t i, j, n;
  pprod_t *q;

  init_pprod_table(&ptbl, 10);
  init_pp_buffer(&buffer, 10);

  p[0] = empty_pp;
  p[1] = var_pp(0);
  p[2] = var_pp(1);
  p[3] = var_pp(2);
  p[4] = var_pp(3);
  num_prods = 5;

  for (i=0; i<5; i++) {
    for (j=0; j<5; j++) {
      q = pprod_mul(&ptbl, p[i], p[j]);
      print_pprod0(stdout, p[i]);
      printf(" * ");
      print_pprod0(stdout, p[j]);
      printf(" = ");
      print_pprod0(stdout, q);
      printf("\n");
      check_product(q);
      printf("\n");
    }
  }

  n = num_prods;
  for (i=0; i<n; i++) {
    for (j=0; j<n; j++) {
      q = pprod_mul(&ptbl, p[i], p[j]);
      print_pprod0(stdout, p[i]);
      printf(" * ");
      print_pprod0(stdout, p[j]);
      printf(" = ");
      print_pprod0(stdout, q);
      printf("\n");
      check_product(q);
      printf("\n");
    }
  }
  
  for (i=0; i<num_prods; i++) {
    pp_buffer_set_pprod(&buffer, p[i]);
    printf("p[%"PRIu32"] = %p = ", i, p[i]);
    print_pprod0(stdout, p[i]);
    printf("\n");
    printf("buffer: ");
    print_pp_buffer0(stdout, &buffer);
    printf("\n");
    q = pprod_from_buffer(&ptbl, &buffer);
    printf("prod from buffer = %p = ", q);
    print_pprod0(stdout, q);
    if (q != p[i]) {
      printf("BUG: HASH CONSING FAILED\n");
      fflush(stdout);
      abort();
    }
    printf("\n\n");
  }

  // delete the non-trivial products
  for (i=5; i<num_prods; i++) {
    q = p[i];
    assert(q != empty_pp && q != end_pp && !pp_is_var(q));
    printf("deleting p[%"PRIu32"] = %p = ", i, q);
    print_pprod0(stdout, q);
    printf("\n");
    delete_pprod(&ptbl, q);
  }
  printf("\n\n");

  p[5] = var_pp(4);
  num_prods = 6;

  // reconstruct more products
  q = pprod_mul(&ptbl, p[1], p[2]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[2], p[3]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[3], p[2]);
  printf("rechecking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[3], p[4]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[4], p[3]);
  printf("rechecking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[4], p[5]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  q = pprod_mul(&ptbl, p[0], p[5]);
  printf("checking q = %p = ", q);
  print_pprod0(stdout, q);
  printf("\n");
  check_product(q);
  printf("\n");

  delete_pp_buffer(&buffer);
  delete_pprod_table(&ptbl);
  

  return 0;
}
