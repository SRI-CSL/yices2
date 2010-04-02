#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

#include "object_stores.h"
#include "pprod_table.h"
#include "rationals.h"
#include "arith_buffers.h"



/*
 * Display power products
 */
static void print_varexp_array(FILE *f, varexp_t *a, uint32_t n) {
  uint32_t i, d;

  if (n == 0) {
    fprintf(f, "1");
    return;
  }
  d = a[0].exp;
  fprintf(f, "x_%"PRId32, a[0].var);
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
}

static void print_pprod0(FILE *f, pprod_t *p) {
  if (pp_is_var(p)) {
    fprintf(f, "x_%"PRId32, var_of_pp(p));
  } else if (pp_is_empty(p)) {
    fprintf(f, "1");
  } else {
    print_varexp_array(f, p->prod, p->len);
  }
}




/*
 * Print buffer b
 */
static void print_monomial(FILE *f, rational_t *coeff, pprod_t *r, bool first) {
  bool negative;
  bool abs_one;

  negative = q_is_neg(coeff);
  if (negative) {
    if (first) {
      fprintf(f, "- ");     
    } else {
      fprintf(f, " - ");
    }
    abs_one = q_is_minus_one(coeff);
  } else {
    if (! first) {
      fprintf(f, " + ");
    }
    abs_one = q_is_one(coeff);
  }

  if (pp_is_empty(r)) {
    q_print_abs(f, coeff);
  } else {
    if (! abs_one) {
      q_print_abs(f, coeff);
      fprintf(f, " ");
    }
    print_pprod0(f, r);
  }

}

static void print_arith_buffer(FILE *f, arith_buffer_t *b) {
  mlist_t *p;
  bool first;

  if (arith_buffer_is_zero(b)) {
    fprintf(f, "0");
  } else {
    p = b->list;
    first = true;
    while (p->next != NULL) {
      print_monomial(f, &p->coeff, p->prod, first);
      first = false;
      p = p->next;
    }
  }
}



/*
 * Test basic operations: b must be normalized
 */
static void test_buffer_pred(char *s, arith_buffer_t *b, bool (*f)(arith_buffer_t *)) {
  printf("  test %s: ", s);
  if (f(b)) {
    printf("yes\n");
  } else {
    printf("no\n");
  }
}

static void test_buffer(arith_buffer_t *b) {
  int32_t x;
  mlist_t *m;

  printf("Buffer %p: ", b);
  print_arith_buffer(stdout, b);
  printf("\n");

  test_buffer_pred("is_zero", b, arith_buffer_is_zero);
  test_buffer_pred("is_constant", b, arith_buffer_is_constant);
  test_buffer_pred("is_nonzero", b, arith_buffer_is_nonzero);
  test_buffer_pred("is_pos", b, arith_buffer_is_pos);
  test_buffer_pred("is_neg", b, arith_buffer_is_neg);
  test_buffer_pred("is_nonneg", b, arith_buffer_is_nonneg);
  test_buffer_pred("is_nonpos", b, arith_buffer_is_nonpos);

  printf("  size: %"PRIu32"\n", arith_buffer_size(b));
  printf("  degree: %"PRIu32"\n", arith_buffer_degree(b));
  if (! arith_buffer_is_zero(b)) {
    printf("  main term: ");
    print_pprod0(stdout, arith_buffer_main_term(b));
    printf("\n");
    m = arith_buffer_main_mono(b);
    printf("  main monomial: ");
    q_print(stdout, &m->coeff);
    printf(" * ");
    print_pprod0(stdout, m->prod);
    printf("\n");
  }

  for (x=0; x<5; x++) {
    printf("  degree in x_%"PRId32": %"PRIu32"\n", 
	   x, arith_buffer_var_degree(b, x));
  }
  printf("---\n");
}



/*
 * Global variables:
 * - global prod table and store
 */
static pprod_table_t prod_table;
static object_store_t store;


/*
 * Initialize table and store
 */
static void init_globals(void) {
  init_rationals();
  init_mlist_store(&store);
  init_pprod_table(&prod_table, 0);
}

/*
 * Delete table and store
 */
static void delete_globals(void) {
  delete_pprod_table(&prod_table);
  delete_mlist_store(&store);
  cleanup_rationals();
}



int main() {
  arith_buffer_t buffer;

  init_globals();
  init_arith_buffer(&buffer, &prod_table, &store);

  printf("Empty buffer\n");
  test_buffer(&buffer);

  printf("x_0 + x_1\n");
  arith_buffer_add_var(&buffer, 0);
  arith_buffer_add_var(&buffer, 1);
  arith_buffer_normalize(&buffer);
  test_buffer(&buffer);

  printf("After reset\n");
  arith_buffer_reset(&buffer);
  test_buffer(&buffer);

  printf("x_2 - x_0\n");
  arith_buffer_add_var(&buffer, 2);
  arith_buffer_sub_var(&buffer, 0);
  arith_buffer_normalize(&buffer);
  test_buffer(&buffer);

  printf("x_2 - x_0 + x_1 + x_0\n");
  arith_buffer_add_var(&buffer, 2);
  arith_buffer_sub_var(&buffer, 0);
  arith_buffer_add_var(&buffer, 1);
  arith_buffer_add_var(&buffer, 0);  
  arith_buffer_normalize(&buffer);
  test_buffer(&buffer);

  delete_globals();

  return 0;
}
