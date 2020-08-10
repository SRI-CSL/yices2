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
 * EMATCH LEARNER
 */

#ifndef __EMATCH_LEARN_H
#define __EMATCH_LEARN_H


#include "solvers/quant/quant_pattern.h"


/*
 * Single quantifier constraint
 */
typedef struct quant_cnstr_s {
  term_t t;
  int32_t *patterns;  // pattern indices in pattern table
  int_hset_t instances; // match indices in instance table for whom instances are learnt

  term_t *uvars;    // universal variables
  term_t *fun;      // functions that appear in the constraint
  term_t *fapps;    // function applications that appear in the constraint
  term_t *consts;   // constants that appear in the constraint

  term_t enable;        // boolean term that enables this constraint
  literal_t enable_lit; // literal corresponding to enable term
} quant_cnstr_t;

/*
 * Quantifier table
 */
typedef struct quant_table_s {
  uint32_t size;
  uint32_t nquant;
  quant_cnstr_t *data;
} quant_table_t;

#define DEF_QUANT_TABLE_SIZE  20
#define MAX_QUANT_TABLE_SIZE  (UINT32_MAX/8)




/********************
 *  QUANT TABLE  *
 *******************/

/*
 * Initialize: default size
 */
extern void init_quant_table(quant_table_t *table);

/*
 * Make the table 50% larger
 */
extern void extend_quant_table(quant_table_t *table);

/*
 * Remove all quantifiers of index >= n
 */
extern void shrink_quant_table(quant_table_t *table, uint32_t n);

/*
 * Empty the table: delete all quant objects
 */
extern void reset_quant_table(quant_table_t *table);

/*
 * Delete the table
 */
extern void delete_quant_table(quant_table_t *table);

/*
 * Allocate a new quant index i
 * - data[i] is not initialized
 */
extern int32_t quant_table_alloc(quant_table_t *table);

/*
 * Create a new quantifier constraint
 */
extern int32_t quant_table_add_cnstr(quant_table_t *qtbl, term_t t, int32_t *pv, uint32_t npv);

/*
 * Check constraint at index idx
 * - if assertion has more variables than variables in patterns, return false
 */
extern bool quant_table_check_cnstr(quant_table_t *qtbl, pattern_table_t *ptbl, uint32_t idx);

/*
 * Print constraint priority
 */
extern void quant_print_cnstr_priority(quant_table_t *qtbl, uint32_t i);

/*
 * Print all constraints priority
 */
extern void quant_print_all_cnstr_priority(quant_table_t *qtbl, const char *comment);





#endif /* __EMATCH_LEARN_H */
