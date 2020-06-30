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
 * QUANTIFIER PATTERNS
 */


#include "solvers/quant/quant_pattern.h"



/*******************
 *  PATTERN TABLE  *
 ******************/

/*
 * Make the table 50% larger
 */
static void extend_pattern_table(pattern_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_PATTERN_TABLE_SIZE) {
    out_of_memory();
  }
  table->data = (pattern_t *) safe_realloc(table->data, n * sizeof(pattern_t));
  table->size = n;
}


/*
 * Remove all patterns of index >= n
 */
static void shrink_pattern_table(pattern_table_t *table, uint32_t n) {
  assert(n <= table->npatterns);

  table->npatterns = n;
}


/*
 * Initialize: default size
 */
void init_pattern_table(pattern_table_t *table) {
  assert(DEF_PATTERN_TABLE_SIZE < MAX_PATTERN_TABLE_SIZE);

  table->size = DEF_PATTERN_TABLE_SIZE;
  table->npatterns = 0;
  table->data = (pattern_t *) safe_malloc(DEF_PATTERN_TABLE_SIZE * sizeof(pattern_t));
}


/*
 * Empty the table: delete all pattern objects
 */
void reset_pattern_table(pattern_table_t *table) {
  shrink_pattern_table(table, 0);
}


/*
 * Delete the table
 */
void delete_pattern_table(pattern_table_t *table) {
  shrink_pattern_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new pattern index i
 * - data[i] is not initialized
 */
int32_t pattern_table_alloc(pattern_table_t *table) {
  uint32_t i;

  i = table->npatterns;
  if (i == table->size) {
    extend_pattern_table(table);
  }
  assert(i < table->size);
  table->npatterns = i+1;

  return i;
}

