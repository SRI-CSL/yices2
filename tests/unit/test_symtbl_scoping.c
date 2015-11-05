/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * More test of the symbol table
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "utils/refcount_strings.h"
#include "utils/symbol_tables.h"

#ifdef MINGW
static inline long int random(void) {
  return rand();
}
#endif



/*
 * We use a fixed sets of symbols
 * - in scope i, each symbol is assigned to i
 */
#define NSYMBOLS 10

static const char *name[NSYMBOLS] = {
  "a", "b", "c", "d", "e",
  "f", "g", "h", "i", "j",
};

static uint32_t scope[NSYMBOLS];

static stbl_t sym_table;


/*
 * All names in sym_table are built with clone_string.
 * Finalizer: decrement the refcount for a string.
 */
static void finalize(stbl_rec_t *r) {
  string_decref(r->string);
}

/*
 * Initialize: empty symbol table
 * - all symbols have scope 0 (unassigned)
 */
static void init(void) {
  uint32_t i;

  init_stbl(&sym_table, 2); // use a small initial size to trigger resizing
  stbl_set_finalizer(&sym_table, finalize);

  for (i=0; i<NSYMBOLS; i++) {
    scope[i] = 0;
  }
}


/*
 * Check the state:
 * - if scope[i] > 0, then symbol[i] shoulld be mapped to scope[i]
 * - is scope[i] = 0, then symbol[i] should not be mapped
 */
static void check(void) {
  uint32_t i;
  int32_t k;

  for (i=0; i<NSYMBOLS; i++) {
    k = stbl_find(&sym_table, name[i]);
    if (k < 0) {
      if (scope[i] != 0) {
	printf("*** BUG: %s is not mapped. Should be mapped to %"PRIu32" ***\n", name[i], scope[i]);
	fflush(stdout);
	exit(1);
      }
    } else {
      if (k != scope[i]) {
	printf("*** BUG: %s is mapped to %"PRId32". It should be mapped to %"PRIu32" ***\n", name[i], k, scope[i]);
	fflush(stdout);
	exit(1);
      }
    }
  }
}


/*
 * Map name[i] to a new scope
 */
static void map(uint32_t i) {
  char *clone;

  assert(i < NSYMBOLS);
  if (scope[i] < UINT32_MAX) {
    clone = clone_string(name[i]);
    string_incref(clone);
    scope[i] ++;
    stbl_add(&sym_table, clone, scope[i]);
  }
}


/*
 * Remove the current map for name[i]
 * - do nothing if scope[i] == 0
 */
static void unmap(uint32_t i) {
  assert(i < NSYMBOLS);
  if (scope[i] > 0) {
    scope[i] --;
    stbl_remove(&sym_table, name[i]);
  }
}


/*
 * Random test: either map or unmap
 */
static void random_test(void) {
  uint32_t r, i;

  r = ((uint32_t) random()) % ( 2 * NSYMBOLS);
  if (r >= NSYMBOLS) {
    // add
    i = r - NSYMBOLS;
    printf("map %s\n", name[i]);
    map(i);
  } else {
    // remove
    i = r;
    printf("unmap %s\n", name[i]);
    unmap(i);
  }

  check();
}

static void random_tests(uint32_t n) {
  while (n > 0) {
    random_test();
    n --;
  }
}


int main(void) {
  uint32_t i;

  init();

  check();
  random_tests(1000000);

  reset_stbl(&sym_table);
  for (i=0; i<NSYMBOLS; i++) {
    scope[i] = 0;
  }
  check();

  printf("\n*** AFTER RESET ***\n");
  random_tests(1000000);

  delete_stbl(&sym_table);

  return 0;
}
