/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * STRINGS WITH REFERENCE COUNTERS
 */

#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "utils/memalloc.h"
#include "utils/refcount_strings.h"


/*
 * Allocate character string with reference counting
 * Make a copy of str and set ref count to 0.
 */
char *clone_string(const char *str) {
  string_t *tmp;
  size_t l;

  l = strlen(str);
  if (l > MAX_REFCOUNT_STRING_SIZE) {
    out_of_memory();
  }
  tmp = (string_t *) safe_malloc(sizeof(string_t) + l + 1);
  tmp->ref = 0;
  strcpy(tmp->str, str);
  return tmp->str;
}


/*
 * Decrement s's reference counter
 * free the string if the ref count gets to 0.
 */
void string_decref(char *s) {
  string_t *h;
  h = string_header(s);
  assert(h->ref > 0);
  h->ref --;
  if (h->ref == 0) free(h);
}


