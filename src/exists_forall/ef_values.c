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
#include "io/yices_pp.h"
#include "terms/term_explorer.h"
#include "terms/term_substitution.h"



/*
 * Initialize the value table
 */
void init_ef_value_table(ef_value_table_t *vtable, value_table_t *vtbl, term_manager_t *mgr, term_table_t *terms) {
  init_ptr_hmap(&vtable->map, 0);
  init_ptr_hmap(&vtable->type_map, 0);
  init_int_hmap(&vtable->val_map, 0);
  vtable->vtbl = vtbl;
  vtable->mgr = mgr;
  vtable->terms = terms;

  init_val_converter(&vtable->convert, vtbl, mgr, terms);
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

  map = &vtable->type_map;
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

  delete_int_hmap(&vtable->val_map);

  vtable->vtbl = NULL;
  vtable->mgr = NULL;
  vtable->terms = NULL;

  delete_val_converter(&vtable->convert);
}


/*
 * Reset the value table and all ivector objects
 */
void reset_ef_value_table(ef_value_table_t *vtable, value_table_t *vtbl, term_manager_t *mgr, term_table_t *terms) {
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
  ptr_hmap_reset(map);

  map = &vtable->type_map;
  for (p = ptr_hmap_first_record(map);
       p != NULL;
       p = ptr_hmap_next_record(map, p)) {
    ivector_t* list_vector = p->val;
    if (list_vector != NULL) {
      delete_ivector(list_vector);
      safe_free(list_vector);
    }
  }
  ptr_hmap_reset(map);

  int_hmap_reset(&vtable->val_map);

  vtable->vtbl = vtbl;
  vtable->mgr = mgr;
  vtable->terms = terms;

  delete_val_converter(&vtable->convert);
  init_val_converter(&vtable->convert, vtbl, mgr, terms);
}


/*
 * Print the value table and all ivector objects
 */
void print_ef_value_table(FILE *f, ef_value_table_t *vtable) {
  ptr_hmap_pair_t *p;
  ptr_hmap_t *map;
  int_hmap_t *imap;
  int_hmap_pair_t *ip;
  ivector_t *v;

  fprintf(f, "\n== EF VALUE TYPES ==\n");
  map = &vtable->type_map;
  for (p = ptr_hmap_first_record(map);
       p != NULL;
       p = ptr_hmap_next_record(map, p)) {
    v = p->val;
    yices_pp_type(f, p->key, 100, 1, 10);
    fprintf(f, " -> ");
    yices_pp_term_array(f, v->size, v->data, 120, UINT32_MAX, 0, 1);
  }

  fprintf(f, "\n== EF VALUES ==\n");
  imap = &vtable->val_map;
  for (ip = int_hmap_first_record(imap);
       ip != NULL;
       ip = int_hmap_next_record(imap, ip)) {
    pp_value(f, vtable->vtbl, ip->key);
    fprintf(f, " -> ");
    yices_pp_term(f, ip->val, 100, 1, 10);
  }

  fprintf(f, "\n== EF VALUE TERMS ==\n");
  map = &vtable->map;
  for (p = ptr_hmap_first_record(map);
       p != NULL;
       p = ptr_hmap_next_record(map, p)) {
    v = p->val;
    yices_pp_term(f, p->key, 100, 1, 10);
    fprintf(f, " -> ");
    yices_pp_term_array(f, v->size, v->data, 120, UINT32_MAX, 0, 1);
  }
  fprintf(f, "\n");
}


/*
 * Store mapping type to value
 */
void store_type_value(ef_value_table_t *vtable, value_t value, term_t tvalue, bool check) {
  ptr_hmap_pair_t *r;
  value_kind_t kind;
  type_t tau;

  if (check) {
    r = ptr_hmap_find(&vtable->map, tvalue);
    if (r != NULL)
      return;
  }

  kind = object_kind(vtable->vtbl, value);
  switch (kind) {
  case BOOLEAN_VALUE:
  case RATIONAL_VALUE:
  case BITVECTOR_VALUE:
  case UNINTERPRETED_VALUE:
    break;

  default:
    return;
  }

  tau = term_type(vtable->terms, tvalue);
  r = ptr_hmap_get(&vtable->type_map, tau);
  if (r->val == NULL) {
    r->val = safe_malloc(sizeof(ivector_t));
    init_ivector(r->val, 0);
  }
  ivector_push(r->val, tvalue);
}


/*
 * Store mapping value to var
 */
static void store_term_value(ef_value_table_t *vtable, term_t var, value_t value) {
  int_hmap_pair_t *vm;
  ptr_hmap_pair_t *m;
  term_t tvalue;

  vm = int_hmap_get(&vtable->val_map, value);
  if (vm->val < 0) {
    tvalue = convert_val(&vtable->convert, value);
    vm->val = tvalue;

    m = ptr_hmap_get(&vtable->map, tvalue);
    assert (m->val == NULL);
    m->val = safe_malloc(sizeof(ivector_t));
    init_ivector(m->val, 0);
    store_type_value(vtable, value, tvalue, false);
  }
  else {
    tvalue = vm->val;

    m = ptr_hmap_get(&vtable->map, tvalue);
    assert (m->val != NULL);
  }
  ivector_push(m->val, var);
}


/*
 * Store function mapping values to var
 */
static void store_func_values(ef_value_table_t *vtable, term_t func, value_t c) {
  val_converter_t *convert;
  value_table_t *table;
  term_table_t *terms;
  type_table_t *types;
  type_t tau;

  convert = &vtable->convert;
  table = vtable->vtbl;
  terms = vtable->terms;
  types = terms->types;
  tau = term_type(terms, func);

  assert(yices_type_is_function(tau));

  value_fun_t *fun;
  value_map_t *mp;
  uint32_t m, n, i, j;
  term_t vari;
  value_t valuei;
  term_t *args;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);

  fun = table->desc[c].ptr;
  assert(is_function_type(types, fun->type));

  m = fun->arity;
  n = fun->map_size;
  i = 0;

  if (!is_unknown(table, fun->def)) {
    valuei = fun->def;
    // TODO
  }

  if (n != 0) {
    // entries present in map
    assert(m > 0);
    args = (term_t *) safe_malloc(m * sizeof(term_t));

    for (; i<n; i++) {
      mp = vtbl_map(table, fun->map[i]);
      assert(mp->arity == m);

      for (j=0; j<m; j++) {
        args[j] = convert_value(convert, mp->arg[j]);
      }

      vari = mk_application(convert->manager, func, m, args);
      valuei = mp->val;
      store_term_value(vtable, vari, valuei);
    }

    safe_free(args);
  }
}


/*
 * Fill the value table
 */
void fill_ef_value_table(ef_value_table_t *vtable, term_t *vars, value_t *values, uint32_t n) {
  uint32_t i;
  value_kind_t kind;

  // first pass: process top-level terms
  for (i=0; i<n; i++) {
    store_term_value(vtable, vars[i], values[i]);
  }

  // second pass: process function values
  for (i=0; i<n; i++) {
    kind = object_kind(vtable->vtbl, values[i]);
    if (kind == FUNCTION_VALUE)
      store_func_values(vtable, vars[i], values[i]);
  }
}


/*
 * SUBSTITUTION
 */


/*
 * Check whether t is either a variable or an uninterpreted term
 * - t must be a good positive term
 */
static bool term_is_var(term_table_t *terms, term_t t) {
  assert(good_term(terms, t) && is_pos_term(t));
  switch (term_kind(terms, t)) {
  case UNINTERPRETED_TERM:
  case CONSTANT_TERM:
    return true;

  default:
    return false;
 }
}

/*
 * Apply the substitution defined by var and value to term t
 * - n = size of arrays var and value
 * - return code < 0 means that an error occurred during the substitution
 *   (cf. apply_term_subst in term_substitution.h).
 */
static term_t term_substitution(ef_value_table_t *vtable, term_t *var, term_t *value, uint32_t n, term_t t) {
  term_subst_t subst;
  term_t g;
  int_hmap_pair_t *p;
  uint32_t i;
  term_t x;

  subst.mngr = vtable->mgr;
  subst.terms = vtable->terms;
  init_int_hmap(&subst.map, 0);
  init_subst_cache(&subst.cache);
  init_istack(&subst.stack);
  subst.rctx = NULL;

  for (i=0; i<n; i++) {
    x = var[i];
    p = int_hmap_get(&subst.map, x);
    p->val = value[i];

    assert(is_pos_term(x));
    assert(term_is_var(subst.terms, x));
    assert(good_term(subst.terms, p->val));
  }

  g = apply_term_subst(&subst, t);
  delete_term_subst(&subst);

  return g;
}


/*
 * Get value representative
 */
term_t get_value_rep(ef_value_table_t *vtable, term_t value) {
  ptr_hmap_pair_t *r;

  r = ptr_hmap_get(&vtable->map, value);
  if (r->val == NULL) {
    return value;
  }
  else {
    uint32_t i, n, m;
    ivector_t *v;
    term_t x;
    term_t xc;

    v = r->val;
    n = v->size;
    assert(n != 0);

    for(i=0; i<n; i++) {
      x = v->data[i];
      if (yices_term_is_composite(x)) {
        xc = x;
      }
      else {
        return x;
      }
    }

    composite_term_t *app;
    ivector_t args, argsrep;
    term_t xcrep;
    term_t f, frep;

    assert(term_kind(vtable->terms, xc) == APP_TERM);

    app = app_term_desc(vtable->terms, xc);
    m = app->arity;

    init_ivector(&args, m);
    init_ivector(&argsrep, m);

    for(i=0; i<m; i++) {
      f = app->arg[i];
      frep = get_value_rep(vtable, f);

      if (f != frep) {
        ivector_push(&args, f);
        ivector_push(&argsrep, frep);
      }
    }

    xcrep = term_substitution(vtable, args.data, argsrep.data, args.size, xc);

    delete_ivector(&args);
    delete_ivector(&argsrep);

    return xcrep;
  }
}


/*
 * Set values from the value table
 */
void set_values_from_value_table(ef_value_table_t *vtable, term_t *vars, term_t *values, uint32_t n) {
  uint32_t i;
  term_t x;

  for (i=0; i<n; i++) {
    x = values[i];
    if (is_utype_term(vtable->terms, x)) {
      // replace x by representative
      values[i] = get_value_rep(vtable, x);
    }
  }
}


static term_t constraint_distinct_elements(ivector_t *v) {
  if (v->size < 2)
    return yices_true();
  else
    return yices_distinct(v->size, v->data);
}

term_t constraint_distinct(ef_value_table_t *vtable) {
  ptr_hmap_pair_t *p;
  ptr_hmap_t *map;
  type_t tau;
  ivector_t *v;
  term_t result;

  map = &vtable->type_map;
  result = yices_true();
  for (p = ptr_hmap_first_record(map);
       p != NULL;
       p = ptr_hmap_next_record(map, p)) {
    tau = p->key;
    if (yices_type_is_uninterpreted(tau)) {
      v = p->val;
      result = yices_and2(result, constraint_distinct_elements(v));
    }
  }

  return result;
}

term_t constraint_distinct_filter(ef_value_table_t *vtable, uint32_t n, term_t *vars) {
  ptr_hmap_t map;
  ptr_hmap_pair_t *p;
  uint32_t i;
  type_t tau;
  ivector_t *v;
  term_t t, result;

  init_ptr_hmap(&map, 0);
  result = yices_true();

  for(i=0; i<n; i++) {
    t = vars[i];
    tau = term_type(vtable->terms, t);

    if (yices_type_is_uninterpreted(tau)) {
      p = ptr_hmap_get(&map, tau);
      if (p->val == NULL) {
        p->val = safe_malloc(sizeof(ivector_t));
        init_ivector(p->val, 0);
      }

      ivector_push(p->val, t);
    }
  }

  for (p = ptr_hmap_first_record(&map);
       p != NULL;
       p = ptr_hmap_next_record(&map, p)) {
    v = p->val;
    result = yices_and2(result, constraint_distinct_elements(v));
  }

  for (p = ptr_hmap_first_record(&map);
       p != NULL;
       p = ptr_hmap_next_record(&map, p)) {
    ivector_t* list_vector = p->val;
    if (list_vector != NULL) {
      delete_ivector(list_vector);
      safe_free(list_vector);
    }
  }
  delete_ptr_hmap(&map);


  return result;
}

static term_t constraint_scalar_element(ef_value_table_t *vtable, term_t t) {
  term_t result;
  type_t tau;
  ptr_hmap_pair_t *r;
  ivector_t *v;
  term_t *eq;
  uint32_t n, i;

  result = yices_true();
  tau = yices_type_of_term(t);

  if (yices_type_is_uninterpreted(tau)) {
    r = ptr_hmap_find(&vtable->type_map, tau);

    if (r->val != NULL) {
      v = r->val;
      n = v->size;

      eq = (term_t *) safe_malloc(n * sizeof(term_t));
      for(i=0; i<n; i++)
        eq[i] = yices_eq(t, v->data[i]);

      result = yices_and2(result, yices_or(n, eq));
    }
  }
  return result;
}

term_t constraint_scalar(ef_value_table_t *vtable, uint32_t n, term_t *t) {
  term_t result;
  uint32_t i;

  result = yices_true();
  for(i=0; i<n; i++) {
    result = yices_and2(result, constraint_scalar_element(vtable, t[i]));
  }

  return result;
}
