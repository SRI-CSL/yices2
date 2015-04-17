/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "terms/term_sets.h"
#include "utils/memalloc.h"


/*
 * Initialize set:
 * - initial content = all terms in a[0 ... n-1]
 */
void init_term_set(int_hset_t *set, uint32_t n, const term_t *a) {
  uint32_t i;

  init_int_hset(set, 0);
  for (i=0; i<n; i++) {
    (void) int_hset_add(set, a[i]);
  }
}


/*
 * Build the set that contains terms a[0 ... n-1]
 * - a may contain several times the same term.
 * - duplicates are ignored
 */
int_hset_t *new_term_set(uint32_t n, const term_t *a) {
  int_hset_t *tmp;

  tmp = (int_hset_t *) safe_malloc(sizeof(int_hset_t));
  init_term_set(tmp, n, a);
  return tmp;
}

/*
 * Delete a set constructed by the previous function
 */
void free_term_set(int_hset_t *s) {
  delete_int_hset(s);
  safe_free(s);
}

