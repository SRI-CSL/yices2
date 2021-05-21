/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
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


