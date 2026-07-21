/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
  ptr_hmap_t map;         // map from term value to vector of terms with that value
  ptr_hmap_t type_map;    // map from type to vector of term values in the model
  int_hmap_t val_map;     // map from value to term value
  value_table_t *vtbl;
  term_manager_t *mgr;
  term_table_t *terms;

  val_converter_t convert;
  int_hmap_t generation;          // map from term to generation of the term
  int_hmap_t var_rep;             // map from term value to representative
  fresh_val_maker_t *fval_maker;
  uint32_t max_generation;
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
extern void print_ef_table(FILE *f, ef_table_t *vtable, bool detailed);


/*
 * Fill the value table
 */
extern void fill_ef_table(ef_table_t *vtable, term_t *vars, value_t *values, uint32_t n);


/*
 * Post-process the value table
 */
extern void postprocess_ef_table(ef_table_t *vtable, bool check);

/*
 * Add entry to type map
 * returns true if type_map is modified
 */
extern bool store_type_value(ef_table_t *vtable, value_t value, term_t tvalue, bool check);


/*
 * Store mapping value to var
 */
extern bool store_term_value(ef_table_t *vtable, term_t var, value_t value, uint32_t gen);


/*
 * Check whether value is present in ef table or not
 */
extern bool check_value_present(ef_table_t *vtable, value_t value);


/*
 * Get value representative
 */
extern term_t ef_get_value(ef_table_t *vtable, term_t value);


/*
 * Set values from the value table
 */
extern void ef_set_values_from_table(ef_table_t *vtable, term_t *vars, term_t *values, uint32_t n);


/*
 * Get the distinct conditions over uninterpreted domain term values
 */
extern term_t constraint_distinct(ef_table_t *vtable);

/*
 * Get the distinct conditions over vars
 */
extern term_t constraint_distinct_filter(ef_table_t *vtable, uint32_t n, term_t *vars);

/*
 * Get the scalar domain constraints (upto generation) for an array of terms
 */
extern term_t constraint_scalar(ef_table_t *vtable, uint32_t n, term_t *t, int32_t generation, bool *done);



#endif /* __EF_VALUES_H */
