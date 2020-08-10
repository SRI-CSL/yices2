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
#include "utils/hash_functions.h"


typedef struct {
  int_hobj_t m;
  instance_table_t *table;
  term_t *vdata;            // variables to be replaced
  occ_t *odata;             // occurrences in egraph that replaces variables
  int32_t compile_idx;      // index of yield instruction in compile instruction table
  uint32_t nelems;
} instance_hobj_t;


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
  init_int_htbl(&table->htbl, 0);
}


/*
 * Empty the table: delete all instance objects
 */
void reset_instance_table(instance_table_t *table) {
  shrink_instance_table(table, 0);
  reset_int_htbl(&table->htbl);
}


/*
 * Delete the table
 */
void delete_instance_table(instance_table_t *table) {
  shrink_instance_table(table, 0);

  safe_free(table->data);
  table->data = NULL;
  delete_int_htbl(&table->htbl);
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
  inst->nelems = n;
  inst->vdata = (term_t *) safe_malloc(n * sizeof(term_t));
  inst->odata = (occ_t *) safe_malloc(n * sizeof(occ_t));

  return i;
}


/*
 * Deallocate the last instance
 */
void instance_table_dealloc(instance_table_t *table) {
  uint32_t n;
  n = table->ninstances;
  assert(n > 0);
  shrink_instance_table(table, n-1);
}



/***************
 *  UTILITIES  *
 **************/

/*
 * Check whether a and b are equal arrays
 * - both must have size n
 */
static bool equal_arrays(int32_t *a, int32_t *b, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/*
 * Hash for an instance match
 */
static uint32_t hash_instance(instance_hobj_t *o) {
//  return jenkins_hash_intarray2((int32_t *) o->odata, o->nelems, (uint32_t) (0x1ede2341 + o->compile_idx));
  uint32_t h1, h2;

  h1 = jenkins_hash_intarray2((int32_t *) o->odata, o->nelems, 0x1ede2341);
  h2 = jenkins_hash_intarray2((int32_t *) o->vdata, o->nelems, 0x4dde2341);
  return jenkins_hash_pair(h2, 0, h1);
}

/*
 * Check if instance object o is same as already present instance at index i
 */
static bool equal_instance(instance_hobj_t *o, uint32_t i) {
  instance_table_t *table;
  instance_t *d;

  table = o->table;
  d = table->data + i;
  return d->nelems == o->nelems &&
//         d->compile_idx == o->compile_idx &&
         equal_arrays(o->odata, d->odata, d->nelems) &&
         equal_arrays(o->vdata, d->vdata, d->nelems);
}

static int32_t build_instance(instance_hobj_t *o) {
  instance_table_t *table;
  instance_t *d;
  uint32_t j, n;
  int32_t i;


  n = o->nelems;
  table = o->table;

  i = instance_table_alloc(table, n);
  d = table->data + i;

  d->compile_idx = o->compile_idx;
  for(j=0; j<n; j++) {
    d->vdata[j] = o->vdata[j];
    d->odata[j] = o->odata[j];
  }

  return i;
}


/*
 * Create or retrieve the instance
 */
int32_t mk_instance(instance_table_t *table, int32_t compile_idx, uint32_t n, term_t *vdata, occ_t *odata) {
  instance_hobj_t inst_hobj;

  inst_hobj.m.hash = (hobj_hash_t) hash_instance;
  inst_hobj.m.eq = (hobj_eq_t) equal_instance;
  inst_hobj.m.build = (hobj_build_t) build_instance;
  inst_hobj.table = table;
  inst_hobj.compile_idx = compile_idx;
  inst_hobj.nelems = n;
  inst_hobj.vdata = vdata;
  inst_hobj.odata = odata;

  return int_htbl_get_obj(&table->htbl, (int_hobj_t *) &inst_hobj);
}

