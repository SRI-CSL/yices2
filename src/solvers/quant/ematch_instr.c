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
    if (table->data[i].subs != NULL) {
      safe_free(table->data[i].subs);
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
  instr->subs = NULL;
  instr->nsubs = 0;
  instr->alt = -1;
  instr->next = -1;
  instr->idx = i;

  return i;
}

