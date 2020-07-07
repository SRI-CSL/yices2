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

#ifndef __QUANT_PATTERN_H
#define __QUANT_PATTERN_H


#include "context/context_types.h"

/*
 * PATTERNS
 */

/*
 * Single pattern
 */
typedef struct pattern_s {
  term_t p;         // pattern expression
  term_t *pvars;    // pattern variables
  term_t *fun;      // functions that appear in the pattern
  term_t *fapps;    // function applications that appear in the pattern
  term_t *consts;   // constants that appear in the pattern

  int32_t code;     // index in ematch instruction table
  ptr_hmap_t matches;  // map from top fapp to set of indices in instance table
} pattern_t;

/*
 * Pattern table
 */
typedef struct pattern_table_s {
  uint32_t size;
  uint32_t npatterns;
  pattern_t *data;
} pattern_table_t;

#define DEF_PATTERN_TABLE_SIZE  20
#define MAX_PATTERN_TABLE_SIZE  (UINT32_MAX/8)



/*
 * Initialize: default size
 */
extern void init_pattern_table(pattern_table_t *table);

/*
 * Empty the table: delete all pattern objects
 */
extern void reset_pattern_table(pattern_table_t *table);

 /*
 * Delete the table
 */
extern void delete_pattern_table(pattern_table_t *table);

/*
 * Allocate a new pattern index i
 * - data[i] is not initialized
 */
extern int32_t pattern_table_alloc(pattern_table_t *table);

/*
 * Create a new pattern
 */
extern int32_t pattern_table_add_pattern(pattern_table_t *ptbl, term_t p, term_t *pv, uint32_t npv,
    term_t *f, uint32_t nf, term_t *fa, uint32_t nfa, term_t *c, uint32_t nc);


#endif /* __QUANT_PATTERN_H */
