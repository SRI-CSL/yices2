/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "terms/power_products.h"


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

#if 0

// not used
static void print_pp_buffer(FILE *f, pp_buffer_t *b) {
  fprintf(f, "pp_buffer %p\n", b);
  fprintf(f, "  size = %"PRIu32"\n", b->size);
  fprintf(f, "  len = %"PRIu32"\n", b->len);
  fprintf(f, "  product = ");
  print_varexp_array(f, b->prod, b->len);
  fprintf(f, "\n");
}

#endif

static void print_pprod(FILE *f, pprod_t *p) {
  fprintf(f, "pprod %p\n", p);
  if (pp_is_var(p)) {
    fprintf(f, " var pp = [x_%"PRId32"]\n", var_of_pp(p));
  } else if (pp_is_empty(p)) {
    fprintf(f, " empty\n");
  } else {
    fprintf(f, "  len = %"PRIu32"\n", p->len);
    fprintf(f, "  degree = %"PRIu32"\n", p->degree);
    fprintf(f, "  product = ");
    print_varexp_array(f, p->prod, p->len);
    fprintf(f, "\n");
  }
}

static void print_pp_buffer0(FILE *f, pp_buffer_t *b) {
  print_varexp_array(f, b->prod, b->len);
  fprintf(f, "\n");
}

static void print_pprod0(FILE *f, pprod_t *p) {
  if (pp_is_var(p)) {
    fprintf(f, "[x_%"PRId32"]\n", var_of_pp(p));
  } else if (pp_is_empty(p)) {
    fprintf(f, "[]\n");
  } else {
    print_varexp_array(f, p->prod, p->len);
    fprintf(f, "\n");
  }
}


#define NUM_PRODS 10

static pp_buffer_t buffer;
static pprod_t *p[NUM_PRODS];

int main() {
  pprod_t *p1, *p2;
  uint32_t i, j;
  int32_t cmp;

  p[0] = empty_pp;
  p[1] = var_pp(0);
  p[2] = var_pp(1);
  p[3] = var_pp(0x3fffffff);

  init_pp_buffer(&buffer, 0);
  p[4] = pp_buffer_getprod(&buffer);  // empty

  pp_buffer_reset(&buffer);
  pp_buffer_mul_var(&buffer, 0);
  p[5] = pp_buffer_getprod(&buffer); // x_0

  pp_buffer_reset(&buffer);
  pp_buffer_mul_var(&buffer, 0);
  pp_buffer_mul_var(&buffer, 1);
  pp_buffer_mul_var(&buffer, 0);
  p[6] = pp_buffer_getprod(&buffer);  // x_0^2 x_1

  pp_buffer_reset(&buffer);
  pp_buffer_mul_varexp(&buffer, 1, 2);
  pp_buffer_mul_varexp(&buffer, 4, 3);
  p[7] = pp_buffer_getprod(&buffer);  // x_1^2 x_4^3

  pp_buffer_set_varexp(&buffer, 3, 2);
  pp_buffer_mul_varexp(&buffer, 1, 4);
  p[8] = pp_buffer_getprod(&buffer);   // x_3^2 x_1^4

  pp_buffer_set_pprod(&buffer, p[7]);
  pp_buffer_mul_pprod(&buffer, p[1]);
  pp_buffer_mul_pprod(&buffer, p[8]);
  p[9] = pp_buffer_getprod(&buffer);

  for (i=0; i<NUM_PRODS; i++) {
    printf("p[%"PRIu32"] =  ", i);
    print_pprod(stdout, p[i]);
    printf(" total degree = %"PRIu32"\n", pprod_degree(p[i]));
    for (j=0; j<5; j++) {
      printf(" degree of x_%"PRIu32" = %"PRIu32"\n", j, pprod_var_degree(p[i], j));
    }
    printf("----\n");
  }
  printf("\n");

  for (i=0; i<NUM_PRODS; i++) {
    p1 = p[i];
    for (j=0; j<NUM_PRODS; j++) {
      p2 = p[j];
      printf("p1: ");
      print_pprod0(stdout, p1);
      printf("p2: ");
      print_pprod0(stdout, p2);
      if (pprod_equal(p1, p2)) {
	printf("equal products\n");
      }
      if (pprod_divides(p1, p2)) {
	printf("p1 divides p2\n");
      }
      if (pprod_divisor(&buffer, p1, p2)) {
	printf("p2/p1: ");
	print_pp_buffer0(stdout, &buffer);
      }
      if (pprod_divides(p2, p1)) {
	printf("p2 divides p1\n");
      }
      if (pprod_divisor(&buffer, p2, p1)) {
	printf("p1/p2: ");
	print_pp_buffer0(stdout, &buffer);
      }
      cmp = pprod_lex_cmp(p1, p2);
      if (cmp < 0) {
	printf("p1 < p2 in lex order\n");
      } else if (cmp > 0) {
	printf("p1 > p2 in lex order\n");
      } else {
	printf("p1 = p2 in lex order\n");
      }
      if (pprod_precedes(p1, p2)) {
	printf("p1 < p2 in deglex ordering\n");
      }
      if (pprod_precedes(p2, p1)) {
	printf("p2 < p1 in deglex ordering\n");
      }
      printf("----\n");
    }
  }


  for (i=0; i<10; i++) {
    free_pprod(p[i]);
  }

  delete_pp_buffer(&buffer);

  return 0;
}
