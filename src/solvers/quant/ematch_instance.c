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
 * EMATCHED INSTANCES
 */




#include "solvers/quant/ematch_instance.h"



/*******************
 *  INSTANCE TABLE  *
 ******************/

/*
 * Make the table 50% larger
 */
static void extend_instance_table(instance_table_t *table) {
  uint32_t n;

  n = table->size + 1;
  n += n>>1;
  if (n >= MAX_INSTANCE_TABLE_SIZE) {
    out_of_memory();
  }
  table->data = (instance_t *) safe_realloc(table->data, n * sizeof(instance_t));
  table->size = n;
}


/*
 * Remove all instances of index >= n
 */
static void shrink_instance_table(instance_table_t *table, uint32_t n) {
  uint32_t i;
  instance_t *inst;

  assert(n <= table->ninstances);

  for(i=n; i<table->ninstances; i++) {
    inst = &table->data[i];
    safe_free(inst->vdata);
    safe_free(inst->odata);
  }

  table->ninstances = n;
}


/*
 * Initialize: default size
 */
void init_instance_table(instance_table_t *table) {
  assert(DEF_INSTANCE_TABLE_SIZE < MAX_INSTANCE_TABLE_SIZE);

  table->size = DEF_INSTANCE_TABLE_SIZE;
  table->ninstances = 0;
  table->data = (instance_t *) safe_malloc(DEF_INSTANCE_TABLE_SIZE * sizeof(instance_t));
}


/*
 * Empty the table: delete all instance objects
 */
void reset_instance_table(instance_table_t *table) {
  shrink_instance_table(table, 0);
}


/*
 * Delete the table
 */
void delete_instance_table(instance_table_t *table) {
  shrink_instance_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
}


/*
 * Allocate a new instance index i of instance size n
 * - vdata/odata are not initialized
 */
int32_t instance_table_alloc(instance_table_t *table, uint32_t n) {
  uint32_t i;
  instance_t *inst;

  i = table->ninstances;
  if (i == table->size) {
    extend_instance_table(table);
  }
  assert(i < table->size);
  table->ninstances = i+1;

  inst = &table->data[i];
  inst->size = n;
  inst->vdata = (term_t *) safe_malloc(n * sizeof(term_t));
  inst->odata = (occ_t *) safe_malloc(n * sizeof(occ_t));

  return i;
}
