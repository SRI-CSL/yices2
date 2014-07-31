/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * INTEGER ARRAYS WITH REFERENCE COUNTERS
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "utils/refcount_int_arrays.h"


/*
 * Allocate an array of n elements
 * - set ref counter to zero
 */
int32_t *alloc_int_array(uint32_t n) {
  int_array_t *tmp;

  if (n > MAX_REFCOUNT_INT_ARRAY_SIZE) {
    out_of_memory();
  }

  tmp = (int_array_t *) safe_malloc(sizeof(int_array_t) + n * sizeof(int32_t));
  tmp->ref = 0;
  return tmp->data;
}


/*
 * Decrement the reference counter for a
 * - if the counter reaches zero, delete a
 */
void int_array_decref(int32_t *a) {
  int_array_t *h;

  if (a != NULL) {
    h = int_array_header(a);
    assert(h->ref > 0);
    h->ref --;
    if (h->ref == 0) free(h);
  }
}
