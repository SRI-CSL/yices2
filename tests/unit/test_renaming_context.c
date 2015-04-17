/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Renaming context
 */

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include "terms/pprod_table.h"
#include "terms/renaming_context.h"
#include "terms/terms.h"
#include "terms/types.h"


/*
 * Global variables
 */
static type_table_t types;
static pprod_table_t pprods;
static term_table_t terms;
static renaming_ctx_t ctx;

// array of variables
#define NVARS 10
static term_t var[NVARS];


/*
 * Initialize all
 */
static void init(void) {
  init_type_table(&types, 10);
  init_pprod_table(&pprods, 0);
  init_term_table(&terms, 20, &types, &pprods);
  init_renaming_ctx(&ctx, &terms, 1);
}


/*
 * Delete all
 */
static void delete(void) {
  delete_renaming_ctx(&ctx);
  delete_term_table(&terms);
  delete_pprod_table(&pprods);
  delete_type_table(&types);
}


/*
 * Initialize the variable array
 */
static void init_variables(void) {
  type_t tau;
  uint32_t i;

  tau = int_type(&types);
  for (i=0; i<NVARS; i++) {
    var[i] = new_variable(&terms, tau);
  }
}


/*
 * Display the current renaming + harray and hash code
 */
static void show_renaming(void) {
  harray_t *h;
  uint32_t i;
  int32_t x, y;

  printf("renaming:\n");
  for (i=0; i<NVARS; i++) {
    x = var[i];
    y = renaming_ctx_lookup(&ctx, x);
    if (y >= 0) {
      printf("x_%"PRId32" --> x_%"PRId32"\n", x, y);
    }
  }

  h = renaming_ctx_hash(&ctx);
  printf("hash: %p\n", h);
  for (i=0; i<h->nelems; i += 2) {
    x = h->data[i];
    y = h->data[i+1];
    printf("x_%"PRId32" --> x_%"PRId32"\n", x, y);
  }

  printf("---\n");
}


/*
 * Test: add renaming for vars[i] to var[i+n-1]
 */
static void test_add(uint32_t i, uint32_t n) {
  uint32_t j;
  term_t x;

  assert(i + n <= NVARS && n>0);

  printf("Test renaming:");
  for (j=i; j<i+n; j++) {
    x = var[j];
    printf(" x_%"PRId32, x);
  }
  printf("\n");

  renaming_ctx_push_vars(&ctx, n, var + i);
  show_renaming();
  printf("\n");
}


/*
 * Test: remove last n renamings
 */
static void test_remove(uint32_t n) {
  printf("Test pop last %"PRIu32" renamings\n", n);
  renaming_ctx_pop_vars(&ctx, n);
  show_renaming();
  printf("\n");
}

int main(void) {
  uint32_t n;

  init();
  init_variables();

  printf("Initial context\n");
  show_renaming();
  printf("\n");

  for (n=0; n<NVARS-5; n++) {
    test_add(n, 5);
  }
  for (n=0; n<NVARS-5; n++) {
    test_remove(5);
  }

  for (n=0; n<NVARS-5; n++) {
    test_add(n, 5);
  }
  for (n=0; n<NVARS-5; n++) {
    test_remove(5);
  }


  delete();

  return 0;
}
