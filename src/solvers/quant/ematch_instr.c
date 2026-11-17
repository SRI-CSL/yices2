/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * INSTRUCTIONS/CODES FOR E-MATCHING
 */

#include "solvers/quant/ematch_instr.h"


/************************
 *  EMATCH INSTR TABLE  *
 ***********************/

/*
 * Initialize: default size
 */
void init_ematch_instr_table(ematch_instr_table_t *table) {
  assert(DEF_EMATCH_INSTR_TABLE_SIZE < MAX_EMATCH_INSTR_TABLE_SIZE);

  table->size = DEF_EMATCH_INSTR_TABLE_SIZE;
  table->ninstr = 0;
  table->data = (ematch_instr_t *) safe_malloc(DEF_EMATCH_INSTR_TABLE_SIZE * sizeof(ematch_instr_t));
}


/*
 * Make the table 50% larger
 */
static void extend_ematch_instr_table(ematch_instr_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_EMATCH_INSTR_TABLE_SIZE) {
    out_of_memory();
  }
  table->data = (ematch_instr_t *) safe_realloc(table->data, n * sizeof(ematch_instr_t));
  table->size = n;
}


/*
 * Remove all ematch_instr of index >= n
 */
static void shrink_ematch_instr_table(ematch_instr_table_t *table, uint32_t n) {
  uint32_t i;

  assert(n <= table->ninstr);

  for(i=n; i<table->ninstr; i++) {
    if (table->data[i].vdata != NULL) {
      safe_free(table->data[i].vdata);
    }
    if (table->data[i].idata != NULL) {
      safe_free(table->data[i].idata);
    }
  }

  table->ninstr = n;
}


/*
 * Empty the table: delete all ematch_instr objects
 */
void reset_ematch_instr_table(ematch_instr_table_t *table) {
  shrink_ematch_instr_table(table, 0);
}


/*
 * Delete the table
 */
void delete_ematch_instr_table(ematch_instr_table_t *table) {
  shrink_ematch_instr_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new ematch_instr index i
 * - data[i] is not initialized
 */
int32_t ematch_instr_table_alloc(ematch_instr_table_t *table) {
  uint32_t i;
  ematch_instr_t *instr;

  i = table->ninstr;
  if (i == table->size) {
    extend_ematch_instr_table(table);
  }
  assert(i < table->size);
  table->ninstr = i+1;

  instr = &table->data[i];

  instr->op = EMATCH_NOOP;
  instr->f = NULL_TERM;
  instr->occ = null_occurrence;
  instr->i = 0;
  instr->j = 0;
  instr->o = 0;
  instr->vdata = NULL;
  instr->idata = NULL;
  instr->nsubs = 0;
  instr->alt = -1;
  instr->next = -1;
  instr->idx = i;

  return i;
}

