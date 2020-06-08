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
 * Value table for the EF.
 */

#ifndef __EF_VALUES_H
#define __EF_VALUES_H

#include "utils/ptr_hash_map.h"
#include "terms/term_utils.h"

#include "yices_types.h"
#include "model/val_to_term.h"
#include "model/fresh_value_maker.h"

/*
 * Term value table object:
 * - map = hash_map from term values to term vector
 */
typedef struct ef_table_s {
  ptr_hmap_t map;
  ptr_hmap_t type_map;
  int_hmap_t val_map;
  value_table_t *vtbl;
  term_manager_t *mgr;
  term_table_t *terms;

  val_converter_t convert;
  int_hmap_t priority;
  int_hmap_t var_rep;
  fresh_val_maker_t *fval_maker;
} ef_table_t;


/*
 * Initialize the value table
 */
extern void init_ef_table(ef_table_t *vtable, value_table_t *vtbl, term_manager_t *mgr, term_table_t *terms);


/*
 * Delete the value table
 */
extern void delete_ef_table(ef_table_t *vtable);


/*
 * Reset the value table and all ivector objects
 */
extern void reset_ef_table(ef_table_t *vtable, value_table_t *vtbl, term_manager_t *mgr, term_table_t *terms);


/*
 * Print the value table
 */
extern void print_ef_table(FILE *f, ef_table_t *vtable);


/*
 * Fill the value table
 */
extern void fill_ef_table(ef_table_t *vtable, term_t *vars, value_t *values, uint32_t n);

/*
 * Add entry to type map
 */
extern void store_type_value(ef_table_t *vtable, value_t value, term_t tvalue, bool check);


/*
 * Get value representative
 */
extern term_t ef_get_value(ef_table_t *vtable, term_t value);


/*
 * Set values from the value table
 */
extern void ef_set_values_from_table(ef_table_t *vtable, term_t *vars, term_t *values, uint32_t n);


extern term_t constraint_distinct(ef_table_t *vtable);

extern term_t constraint_distinct_filter(ef_table_t *vtable, uint32_t n, term_t *vars);

extern term_t constraint_scalar(ef_table_t *vtable, uint32_t n, term_t *t, int32_t bound, bool *done);



#endif /* __EF_VALUES_H */
