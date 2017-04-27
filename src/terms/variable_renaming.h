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
 * Data structure to rename bound variables
 *
 * For a variable x, we store an array of variables x_1,...,x_n.
 * These variables are used in turn to rename x in different scopes.
 * Example: in (forall x: (and p(x) (forall x, y: q(x, y))))
 * then the first x is renamed to x_1, and the second to x_2
 * to give: (forall x_1: (and p(x_1) (forall x_2, y_1: q(x_2, y_1)))).
 *
 * We store the renaming for x in an array a of 32bit integers:
 *    a[0] = x
 *    a[1] = index k between 1 and n+1
 *    a[2] = x_1
 *    ...
 *    a[n+1] = x_n
 * This is interpreted as follows:
 * - if k=1, then x is not renamed in the current scope
 * - otherwise, x is renamed to a[k] = x_{k-1}
 */

#ifndef __VARIABLE_RENAMING_H
#define __VARIABLE_RENAMING_H

#include <stdint.h>

#include "terms/terms.h"


/*
 * Renaming structure: array of index vectors
 */
typedef struct renaming_s {
  int32_t **data;
  term_table_t *terms;
  uint32_t size;
} renaming_t;

#define DEF_RENAMING_SIZE 20
#define MAX_RENAMING_SIZE (UINT32_MAX/sizeof(int32_t *))


/*
 * Initialize a renaming structure:
 * - ttbl = attached term table
 * - initial size = 0
 */
extern void init_renaming(renaming_t *s, term_table_t *ttbl);


/*
 * Free all memory used
 */
extern void delete_renaming(renaming_t *s);


/*
 * Reset: delete all renamings stored in s
 */
extern void reset_renaming(renaming_t *s);


/*
 * Get the renaming of x in a new scope
 * - x must be a variable in s->terms
 * - if x is attached to x_1, ..., x_n and the current scope is i
 *   (i.e., x is currently renamed to x_i) then the scope is incremented
 *   and x_{i+1} is returned.
 * - if i=n, then a fresh variable x_{n+1} is created and returned
 * - if x is not attached to anything yet, then a fresh array a is
 *   created and x is renamed to a fresh variable x_1 that gets
 *   stored in a.
 */
extern term_t get_var_renaming(renaming_t *s, term_t x);


/*
 * Clear the current renaming of x
 * - no change if x has not been renamed
 */
extern void clear_var_renaming(renaming_t *s, term_t x);


#endif /* __VARIABLE_RENAMING_H */
