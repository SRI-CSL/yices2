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


#include "solvers/quant/quant_cnstr.h"
#include "utils/index_vectors.h"



/********************
 *  QUANT TABLE  *
 *******************/

/*
 * Initialize: default size
 */
void init_quant_table(quant_table_t *table) {
  assert(DEF_QUANT_TABLE_SIZE < MAX_QUANT_TABLE_SIZE);

  table->size = DEF_QUANT_TABLE_SIZE;
  table->nquant = 0;
  table->data = (quant_cnstr_t *) safe_malloc(DEF_QUANT_TABLE_SIZE * sizeof(quant_cnstr_t));
}


/*
 * Make the table 50% larger
 */
void extend_quant_table(quant_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_QUANT_TABLE_SIZE) {
    out_of_memory();
  }
  table->data = (quant_cnstr_t *) safe_realloc(table->data, n * sizeof(quant_cnstr_t));
  table->size = n;
}


/*
 * Remove all quantifiers of index >= n
 */
void shrink_quant_table(quant_table_t *table, uint32_t n) {
  uint32_t i;
  quant_cnstr_t *cnstr;

  assert(n <= table->nquant);

  for(i=n; i<table->nquant; i++) {
    cnstr = &table->data[i];
    delete_index_vector(cnstr->patterns);
    delete_int_hset(&cnstr->instances);
  }

  table->nquant = n;
}


/*
 * Empty the table: delete all quant objects
 */
void reset_quant_table(quant_table_t *table) {
  shrink_quant_table(table, 0);
}


/*
 * Delete the table
 */
void delete_quant_table(quant_table_t *table) {
  shrink_quant_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new quant index i
 * - data[i] is not initialized
 */
int32_t quant_table_alloc(quant_table_t *table) {
  uint32_t i;

  i = table->nquant;
  if (i == table->size) {
    extend_quant_table(table);
  }
  assert(i < table->size);
  table->nquant = i+1;

  return i;
}


/*
 * Create a new quantifier constraint
 */
int32_t quant_table_add_cnstr(quant_table_t *qtbl, term_t t, int32_t *pv, uint32_t npv) {
  quant_cnstr_t *qcnstr;
  int32_t i;

  i = quant_table_alloc(qtbl);
  qcnstr = qtbl->data + i;

  qcnstr->t = t;
  qcnstr->patterns = make_index_vector(pv, npv);
  init_int_hset(&qcnstr->instances, 0);

  return i;
}

