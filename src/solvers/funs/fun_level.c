/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2020 SRI International.
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
 * SUPPORT FOR STRATIFICATION
 */

#include <assert.h>

#include "utils/memalloc.h"
#include "solvers/funs/fun_level.h"

/*
 * Initialize: types = the relevant type table
 */
void init_flevel_table(flevel_table_t *table, type_table_t *types) {
  table->types = types;
  table->level = NULL;
  table->size = 0;
}

/*
 * Resize: make sure size > n
 */
static void resize_flevel_table(flevel_table_t *table, uint32_t n) {
  uint32_t i, s;

  s = table->size;
  assert(s <= n);

  if (n >= MAX_FLEVEL_TABLE_SIZE) {
    out_of_memory();
  }

  // try new_size = min(2s, default size)
  s <<= 1;
  if (s < DEF_FLEVEL_TABLE_SIZE) s = DEF_FLEVEL_TABLE_SIZE;
  // make sure new size <= max size and new_size >= n+1
  if (s > MAX_FLEVEL_TABLE_SIZE) s = MAX_FLEVEL_TABLE_SIZE;
  if (s <= n) s = n+1;

  assert(s > n && s <= MAX_FLEVEL_TABLE_SIZE);
  table->level = safe_realloc(table->level, s * sizeof(int32_t));
  for (i=table->size; i<s; i++) {
    table->level[i] = -1; // mark as unknown
  }
  table->size = s;
}

/*
 * Delete: free memory
 */
void delete_flevel_table(flevel_table_t *table) {
  safe_free(table->level);
  table->level = NULL;
}

/*
 * Get level of tau: return -1 if not known
 */
static int32_t get_flevel(const flevel_table_t *table, type_t tau) {
  assert(good_type(table->types, tau));
  return tau < table->size ? table->level[tau] : -1;
}

/*
 * Store level[tau] := k
 */
static void store_flevel(flevel_table_t *table, type_t tau, uint32_t k) {
  assert(good_type(table->types, tau));
  assert(k < (uint32_t) INT32_MAX);

  if (tau >= table->size) {
    resize_flevel_table(table, (uint32_t) tau);
  }
  assert(table->level[tau] == -1);
  table->level[tau] = k;
}


/*
 * Compute the level
 */
static uint32_t flevel_of_tuple_type(flevel_table_t *table, const tuple_type_t *d) {
  uint32_t i, n, k, max;

  max = 0;
  n = d->nelem;
  for (i=0; i<n; i++) {
    k = flevel(table, d->elem[i]);
    if (k > max) max = k;
  }
  return max;
}

static uint32_t flevel_of_function_type(flevel_table_t *table, const function_type_t *d) {
  uint32_t i, n, k, max;

  max = flevel(table, d->range);
  n = d->ndom;
  for (i=0; i<n; i++) {
    k = flevel(table, d->domain[i]);
    if (k > max) max = k;
  }
  return max + 1;
}

static uint32_t compute_flevel(flevel_table_t *table, type_t tau) {
  type_table_t *types;

  assert(good_type(table->types, tau));

  types = table->types;
  switch (type_kind(types, tau)) {
  case TUPLE_TYPE:
    return flevel_of_tuple_type(table, tuple_type_desc(types, tau));

  case FUNCTION_TYPE:
    return flevel_of_function_type(table, function_type_desc(types, tau));

  default:
    return 0;
  }
}


/*
 * Compute and return the level of type tau
 * - tau must be a valid table in table->types
 */
uint32_t flevel(flevel_table_t *table, type_t tau) {
  int32_t k;

  k = get_flevel(table, tau);
  if (k < 0) {
    k = compute_flevel(table, tau);
    store_flevel(table, tau, k);
  }
  assert(k >= 0);

  return k;
}
