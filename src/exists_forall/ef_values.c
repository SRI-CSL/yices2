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
 * Build a value table mapping a value to a list of terms.
 */

#include <stdint.h>
#include <stdio.h>

#include "utils/int_vectors.h"
#include "utils/memalloc.h"
#include "exists_forall/ef_values.h"

#include "yices.h"



/*
 * Initialize the value table
 */
void init_ef_value_table(ef_value_table_t *vtable) {
  init_ptr_hmap(&vtable->map, 0);
}


/*
 * Delete the value table and all ivector objects
 */
void delete_ef_value_table(ef_value_table_t *vtable) {
  ptr_hmap_pair_t *p;
  ptr_hmap_t *map;

  map = &vtable->map;
  for (p = ptr_hmap_first_record(map);
       p != NULL;
       p = ptr_hmap_next_record(map, p)) {
    ivector_t* list_vector = p->val;
    if (list_vector != NULL) {
      delete_ivector(list_vector);
      safe_free(list_vector);
    }
  }
  delete_ptr_hmap(map);
}


/*
 * Print the value table and all ivector objects
 */
void print_ef_value_table(FILE *f, ef_value_table_t *vtable) {
  ptr_hmap_pair_t *p;
  ptr_hmap_t *map;
  ivector_t *v;

  fprintf(f, "EF VALUE TABLE\n");

  map = &vtable->map;
  for (p = ptr_hmap_first_record(map);
       p != NULL;
       p = ptr_hmap_next_record(map, p)) {
	v = p->val;
    yices_pp_term(f, p->key, 100, 1, 10);
    fprintf(f, " -> ");
    yices_pp_term_array(f, v->size, v->data, 120, UINT32_MAX, 0, 1);
  }
}


/*
 * Store mapping value to var
 */
static void store_term_value(ef_value_table_t *vtable, term_t var, term_t value) {
  ptr_hmap_pair_t *r;

  r = ptr_hmap_get(&vtable->map, value);
  if (r->val == NULL) {
    r->val = safe_malloc(sizeof(ivector_t));
    init_ivector(r->val, 0);
  }
  ivector_push(r->val, var);
}


/*
 * Fill the value table
 */
void fill_ef_value_table(ef_value_table_t *vtable, term_t *vars, term_t *values, uint32_t n) {
  uint32_t i;

  for (i=0; i<n; i++) {
    store_term_value(vtable, vars[i], values[i]);
  }
}


/*
 * Get value representative
 */
term_t get_value_rep(ef_value_table_t *vtable, term_table_t *terms, term_t value) {
  ptr_hmap_pair_t *r;

  r = ptr_hmap_get(&vtable->map, value);
  if (r->val == NULL) {
    return value;
  }
  else {
    uint32_t i, n;
    ivector_t *v;
    term_t x;

    v = r->val;
    n = v->size;

    for(i=0; i<n; i++) {
      x = v->data[i];
      if (is_utype_term(terms, x)) {
        return x;
      }
    }
    return value;
  }
}


/*
 * Set values from the value table
 */
void set_values_from_value_table(ef_value_table_t *vtable, term_table_t *terms, term_t *vars, term_t *values, uint32_t n) {
  uint32_t i;
  term_t x;

  for (i=0; i<n; i++) {
    x = values[i];
    if (is_utype_term(terms, x)) {
      // replace x by representative
      values[i] = get_value_rep(vtable, terms, x);
    }
  }
}

