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

    delete_index_vector(cnstr->uvars);
    delete_index_vector(cnstr->fun);
    delete_index_vector(cnstr->fapps);
    delete_index_vector(cnstr->consts);
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

/*
 * Check constraint at index idx
 * - if assertion has more variables than variables in patterns, return false
 */
bool quant_table_check_cnstr(quant_table_t *qtbl, pattern_table_t *ptbl, uint32_t idx) {
  quant_cnstr_t *cnstr;
  int_hmap_t vmap;
  int_hmap_pair_t *p;
  uint32_t i, j, m, n;
  term_t x;
  pattern_t *pat;
  bool result;

  result = true;
  cnstr = qtbl->data + idx;

  if(iv_len(cnstr->patterns) == 0) {
    return result;
  }

  init_int_hmap(&vmap, 0);
  n = iv_len(cnstr->uvars);

  for(i=0; i<n; i++) {
    x = cnstr->uvars[i];
    p = int_hmap_get(&vmap, x);
    assert(p->val < 0);
    p->val = 0;
  }

  n = iv_len(cnstr->patterns);

  for (i=0; i<n; i++) {
    pat = ptbl->data + cnstr->patterns[i];
    m = iv_len(pat->pvars);
    for(j=0; j<m; j++) {
      x = pat->pvars[j];
      p = int_hmap_find(&vmap, x);
      if (p == NULL) {
//        printf("Pattern has more variables than term\n");
//        assert(0);
      } else {
        p->val = 1;
      }
    }
  }

  for (p = int_hmap_first_record(&vmap);
       p != NULL;
       p = int_hmap_next_record(&vmap, p)) {
    if (p->val != 1) {
      result = false;
      printf("Missing variable in patterns: %d\n", p->key);
#if 0
      yices_pp_term(stdout, p->key, 120, 1, 0);
#endif
    }
  }

  delete_int_hmap(&vmap);

  return result;
}


