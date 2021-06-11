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
 * PRETTY PRINTER FOR CONCRETE VALUES USING THE SMT2 SYNTAX
 */

#include <inttypes.h>

#include "frontend/smt2/smt2_printer.h"
#include "frontend/smt2/smt2_symbol_printer.h"
#include "frontend/smt2/smt2_type_printer.h"


/*
 * Convert a bitvector value b to an unsigned integer
 * - the integer is stored in z
 */
extern void convert_bv_to_rational(mpz_t z, const value_bv_t *b) {
  uint32_t i;

  /*
   * the size of unsigned long is at leas 32 bits
   * so we don't need special precautions here.
   */
  mpz_set_ui(z, 0);
  i = b->width;
  while (i > 0) {
    i --;
    mpz_mul_2exp(z, z, 32);       // z = z * 2^32
    mpz_add_ui(z, z, b->data[i]); // z += b->data[i] (32bit word)
  }
}


/*
 * Printing for each object type
 */
static void smt2_pp_bitvector(smt2_pp_t *printer, value_bv_t *b) {
  if (printer->bv_as_decimal) {
    pp_open_block(&printer->pp, PP_OPEN_SMT2_BV_DEC);
    convert_bv_to_rational(printer->aux, b);
    pp_mpz(&printer->pp, printer->aux);
    pp_uint32(&printer->pp, b->nbits);
    pp_close_block(&printer->pp, true);
  } else {
    pp_smt2_bv(&printer->pp, b->data, b->nbits);
  }
}


/*
 * SMT2 format for integer and rational constants
 */
// side effect on q
static void smt2_pp_integer(smt2_pp_t *printer, rational_t *q) {
  assert(q_is_integer(q));

  if (q_is_neg(q)) {
    q_neg(q); // flip the sign
    pp_open_block(&printer->pp, PP_OPEN_MINUS);
    pp_rational(&printer->pp, q);
    pp_close_block(&printer->pp, true);
  } else {
    pp_rational(&printer->pp, q);
  }
}

// integer value printed in the SMT syntax for reals
// no change to q
static void smt2_pp_integer_as_real(smt2_pp_t *printer, rational_t *q) {
  rational_t aux;

  assert(q_is_integer(q));

  if (q_is_neg(q)) {
    q_init(&aux);
    q_set_neg(&aux, q);
    pp_open_block(&printer->pp, PP_OPEN_MINUS);
    pp_smt2_integer_as_real(&printer->pp, &aux);
    pp_close_block(&printer->pp, true);
    q_clear(&aux);
  } else {
    pp_smt2_integer_as_real(&printer->pp, q);
  }
}


static void smt2_pp_rational(smt2_pp_t *printer, rational_t *q) {
  rational_t num, den;

  q_init(&num);
  q_init(&den);
  q_get_num(&num, q); // numerator
  q_get_den(&den, q); // denominator

  assert(q_is_pos(&den) && q_is_integer(&den));

  if (q_is_one(&den)) {
    smt2_pp_integer(printer, &num);
  } else {
    pp_open_block(&printer->pp, PP_OPEN_DIV);
    smt2_pp_integer(printer, &num);
    pp_rational(&printer->pp, &den);
    pp_close_block(&printer->pp, true);
  }

  q_clear(&num);
  q_clear(&den);
}

static void smt2_pp_algebraic(smt2_pp_t *printer, void *a) {
  pp_algebraic(&printer->pp, a);
}


/*
 * For uninterpreted constants: always print an abstract name
 */
static void smt2_pp_unint_name(smt2_pp_t *printer, value_t c) {
  pp_id(&printer->pp, "@const_", c);
}

/*
 * Function: always use a default name, even if fun has a name
 */
static void smt2_pp_fun_name(smt2_pp_t *printer, value_t c) {
  pp_id(&printer->pp, "@fun_", c);
}



/*
 * Print object c on stream f
 *
 * There's no support for tuples or mappings in SMT2. They should never occur here.
 */
void smt2_pp_object(smt2_pp_t *printer, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);

  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    pp_string(&printer->pp, "???");
    break;
  case BOOLEAN_VALUE:
    pp_bool(&printer->pp, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    smt2_pp_rational(printer, &table->desc[c].rational);
    break;
  case ALGEBRAIC_VALUE:
    smt2_pp_algebraic(printer, table->desc[c].ptr);
    break;
  case BITVECTOR_VALUE:
    smt2_pp_bitvector(printer, table->desc[c].ptr);
    break;
  case UNINTERPRETED_VALUE:
    smt2_pp_unint_name(printer, c);
    break;
  case FUNCTION_VALUE:
  case UPDATE_VALUE:   // updates are treated like functions
    smt2_pp_fun_name(printer, c);
    vtbl_push_object(table, c);
    break;

  case MAP_VALUE:
  case TUPLE_VALUE:
  default:
    assert(false);
  }
}


/*
 * Variant with a type argument.
 * - this is used to format integer value as reals when printing objects
 */
static void smt2_pp_typed_object(smt2_pp_t *printer, value_table_t *table, value_t c, type_t tau) {
  if (object_is_integer(table, c) && is_real_type(tau)) {
    smt2_pp_integer_as_real(printer, vtbl_rational(table, c));
  } else {
    smt2_pp_object(printer, table, c);
  }
}



/*
 * Format to display a function:
 * (function <name>
 *   (type (-> tau_1 ... tau_n sigma))
 *   (= (<name> x_1 ... x_n) y_1)
 *    ...
 *   (default z))
 */
static void smt2_pp_function_header(smt2_pp_t *printer, value_table_t *table, value_t c, type_t tau) {
  pp_open_block(&printer->pp, PP_OPEN_FUNCTION);
  pp_id(&printer->pp, "@fun_", c);
  pp_open_block(&printer->pp, PP_OPEN_TYPE);
  smt2_pp_type(printer, table->type_table, tau);
  pp_close_block(&printer->pp, true);
}


/*
 * Print the function c
 * - if show_default is true, also print the default falue
 */
void smt2_pp_function(smt2_pp_t *printer, value_table_t *table, value_t c, bool show_default) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t i, n;
  uint32_t j, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;

  smt2_pp_function_header(printer, table, c, fun->type);

  m = fun->arity;
  n = fun->map_size;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_EQ);  // (=
    pp_open_block(&printer->pp, PP_OPEN_PAR); // (fun
    smt2_pp_fun_name(printer, c);

    mp = vtbl_map(table, fun->map[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      smt2_pp_object(printer, table, mp->arg[j]);
    }
    pp_close_block(&printer->pp, true); // close of (fun ...
    smt2_pp_object(printer, table, mp->val);
    pp_close_block(&printer->pp, true); // close (= ..
  }

  if (show_default && !is_unknown(table, fun->def)) {
    pp_open_block(&printer->pp, PP_OPEN_DEFAULT); // (default
    smt2_pp_object(printer, table, fun->def);
    pp_close_block(&printer->pp, true); // close (default ..
  }
  pp_close_block(&printer->pp, true); // close (function ...
}


/*
 * Expand update c and print it as a function
 * - the name "@fun_c"
 * - if show_default is true, also print the default value
 */
void smt2_normalize_and_pp_update(smt2_pp_t *printer, value_table_t *table, value_t c, bool show_default) {
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau;
  uint32_t i, j, n, m;

  // build the mapping for c in hset1
  vtbl_expand_update(table, c, &def, &tau);
  hset = table->hset1;
  assert(hset != NULL);

  smt2_pp_function_header(printer, table, c, tau);

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  m = vtbl_update(table, c)->arity;
  n = hset->nelems;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_EQ);
    pp_open_block(&printer->pp, PP_OPEN_PAR);
    smt2_pp_fun_name(printer, c);

    mp = vtbl_map(table, hset->data[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      smt2_pp_object(printer, table, mp->arg[j]);
    }
    pp_close_block(&printer->pp, true); // close (name arg[0] ... arg[m-1])
    smt2_pp_object(printer, table, mp->val);
    pp_close_block(&printer->pp, true); // close (=
  }

  if (show_default && !is_unknown(table, def)) {
    pp_open_block(&printer->pp, PP_OPEN_DEFAULT);
    smt2_pp_object(printer, table, def);
    pp_close_block(&printer->pp, true);
  }
  pp_close_block(&printer->pp, true);  // close the (function ...
}



/*
 * Print the maps of all the queued functions (this may recursively push more
 * functions to the queue and print them).
 * - if show_default is true, print the default value for each map
 * - empty the table's queue
 */
void smt2_pp_queued_functions(smt2_pp_t *printer, value_table_t *table, bool show_default) {
  int_queue_t *q;
  value_t v;

  q = &table->queue.queue;
  while (! int_queue_is_empty(q)) {
    v = int_queue_pop(q);
    if (object_is_function(table, v)) {
      smt2_pp_function(printer, table, v, show_default);
    } else {
      assert(object_is_update(table, v));
      smt2_normalize_and_pp_update(printer, table, v, show_default);
    }
  }
  vtbl_empty_queue(table);
}



/*
 * VARIANT: TRY TO USE SMT2 SYNTAX
 */

/*
 * Variant of smt2_pp_object that uses SMT2 syntax for arrays
 * and add explict type when printing uninterpreted constants.
 */
static void smt2_pp_object_in_def(smt2_pp_t *printer, value_table_t *table, type_t tau, value_t c);

/*
 * Default value in a function/update
 */
static void smt2_pp_default_value(smt2_pp_t *printer, value_table_t *table, type_t tau, value_t def) {
  if (is_unknown(table, def)) {
    pp_string(&printer->pp, "???");
  } else {
    smt2_pp_object_in_def(printer, table, tau, def);
  }
}

/*
 * Variant of pp_function using SMT2-like syntax:
 *   (store (store ((as const tau) v0) i1 v1) i2 v2)
 * - tau = type of the function
 */
static void smt2_pp_array(smt2_pp_t *printer, value_table_t *table, type_t tau, value_t c) {
  type_table_t *types;
  value_fun_t *fun;
  value_map_t *mp;
  type_t sigma, range;
  uint32_t i, n;
  uint32_t j, m;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;

  types = table->type_table;
  range = function_type_range(types, tau);
  m = fun->arity;

  n = fun->map_size;
  // (store (store ....
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_SMT2_STORE);
  }
  // ((as const tau) <default value>)
  pp_open_block(&printer->pp, PP_OPEN_PAR);
  pp_open_block(&printer->pp, PP_OPEN_SMT2_AS_CONST);
  smt2_pp_type(printer, types, tau);
  pp_close_block(&printer->pp, true);
  smt2_pp_default_value(printer, table, range, fun->def);
  pp_close_block(&printer->pp, true);

  // one update for each element in the map
  i = n;
  while (i > 0) {
    i --;
    mp = vtbl_map(table, fun->map[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      sigma = function_type_domain(types, tau, j);
      smt2_pp_object_in_def(printer, table, sigma, mp->arg[j]);
    }
    smt2_pp_object_in_def(printer, table, range, mp->val);
    pp_close_block(&printer->pp, true);
  }
}

/*
 * Expand update c and print it as a function.
 * - use the SMT2-like syntax
 */
static void smt2_pp_array_update(smt2_pp_t *printer, value_table_t *table, value_t c) {
  type_table_t *types;
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau, range, sigma;
  uint32_t i, j, n, m;

  // build the mapping for c in table->hset1
  vtbl_expand_update(table, c, &def, &tau);
  hset = table->hset1;
  assert(hset != NULL);

  types = table->type_table;

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  m = vtbl_update(table, c)->arity;
  range = function_type_range(types, tau);
  n = hset->nelems;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_SMT2_STORE);
  }
  // default value: ((as const tau) <default>)
  pp_open_block(&printer->pp, PP_OPEN_PAR);
  pp_open_block(&printer->pp, PP_OPEN_SMT2_AS_CONST);
  smt2_pp_type(printer, types, tau);
  pp_close_block(&printer->pp, true);
  smt2_pp_default_value(printer, table, range, def);
  pp_close_block(&printer->pp, true);

  // one store for each element in the map
  i = n;
  while (i>0) {
    i --;
    mp = vtbl_map(table, hset->data[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      sigma = function_type_domain(types, tau, j);
      smt2_pp_object_in_def(printer, table, sigma, mp->arg[j]);
    }
    smt2_pp_object_in_def(printer, table, range, mp->val);
    pp_close_block(&printer->pp, true);
  }
}


/*
 * Print an uninterpreted constant value with explicit type
 */
static void smt2_pp_unint_with_type(smt2_pp_t *printer, type_table_t *ttbl, value_t c, type_t tau) {
  // (as @const_c <tau>)
  pp_open_block(&printer->pp, PP_OPEN_SMT2_AS);
  smt2_pp_unint_name(printer, c);
  smt2_pp_type(printer, ttbl, tau);
  pp_close_block(&printer->pp, true);
}

static void smt2_pp_object_in_def(smt2_pp_t *printer, value_table_t *table, type_t tau, value_t c) {
  assert(0 <= c && c < table->nobjects);

  if (object_is_function(table, c)) {
    smt2_pp_array(printer, table, tau, c);
  } else if (object_is_update(table, c)) {
    smt2_pp_array_update(printer, table, c);
  } else if (object_is_unint(table, c)) {
    smt2_pp_unint_with_type(printer, table->type_table, c, tau);
  } else {
    smt2_pp_typed_object(printer, table, c, tau);
  }
}


/*
 * Print a function parameters and range
 * This prints ((x!0 tau0) ... (x!k tau_k)) sigma
 * where tau0 .. tau_k = function domain and sigma = range
 */
static void smt2_pp_function_params(smt2_pp_t *printer, type_table_t *types, type_t tau) {
  uint32_t i, n;
  function_type_t *fun;

  fun = function_type_desc(types, tau);

  pp_open_block(&printer->pp, PP_OPEN_PAR);
  n = fun->ndom;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_PAR);
    pp_id(&printer->pp, "x!", i);
    smt2_pp_type(printer, types, fun->domain[i]);
    pp_close_block(&printer->pp, true);
  }
  pp_close_block(&printer->pp, true);
  smt2_pp_type(printer, types, fun->range);
}

/*
 * Print a predicate for map :=  [v!0 ... v!k -> g]
 * - if map has arity one, this prints (= x!0 v!0)
 * - otherwise, tthis prints (and (= x!0 v!0) ... (x!k vk))
 * - tau is the type of map
 */
static void smt2_pp_map(smt2_pp_t *printer, value_table_t *table, type_t tau, value_map_t *map) {
  type_table_t *types;
  function_type_t *fun;
  uint32_t i, n;

  types = table->type_table;
  fun = function_type_desc(types, tau);

  n = map->arity;
  assert(n > 0 && n == fun->ndom);
  if (n > 1) pp_open_block(&printer->pp, PP_OPEN_AND);
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_EQ);
    pp_id(&printer->pp, "x!", i);
    smt2_pp_object_in_def(printer, table, fun->domain[i], map->arg[i]);
    pp_close_block(&printer->pp, true);
  }
  if (n > 1) pp_close_block(&printer->pp, true);
}

/*
 * Print a function definition as a cascade of if-then-elses
 * - tau = type of the function
 * - c = function value
 */
static void smt2_pp_function_definition(smt2_pp_t *printer, value_table_t *table, type_t tau, value_t c) {
  value_fun_t *fun;
  value_map_t *mp;
  uint32_t i, n;
  type_t range;

  assert(0 <= c && c < table->nobjects && table->kind[c] == FUNCTION_VALUE);
  fun = table->desc[c].ptr;

  range = function_type_range(table->type_table, tau);

  n = fun->map_size;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_ITE);
    mp = vtbl_map(table, fun->map[i]);
    smt2_pp_map(printer, table, tau, mp);
    smt2_pp_object_in_def(printer, table, range, mp->val);
  }
  // default value
  smt2_pp_default_value(printer, table, range, fun->def);

  for (i=0; i<n; i++) {
    pp_close_block(&printer->pp, true);
  }
}

/*
 * Normalize c then print if as a cascade of if-then-else
 */
static void smt2_pp_update_definition(smt2_pp_t *printer, value_table_t *table, value_t c) {
  map_hset_t *hset;
  value_map_t *mp;
  value_t def;
  type_t tau, range;
  uint32_t i, n;

  // build the mapping for c in hset1
  vtbl_expand_update(table, c, &def, &tau);
  hset = table->hset1;
  assert(hset != NULL);

  range = function_type_range(table->type_table, tau);

  /*
   * hset->data contains an array of mapping objects
   * hset->nelems = number of elements in hset->data
   */
  n = hset->nelems;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_ITE);
    mp = vtbl_map(table, hset->data[i]);
    smt2_pp_map(printer, table, tau, mp);
    smt2_pp_object_in_def(printer, table, range, mp->val);
  }
  smt2_pp_default_value(printer, table, range, def);

  for (i=0; i<n; i++) {
    pp_close_block(&printer->pp, true);
  }
}


/*
 * Print a definition in the SMT2 style.
 * - this prints (define-fun name () tau value)
 */
void smt2_pp_def(smt2_pp_t *printer, value_table_t *table, const char *name, type_t tau, value_t c) {
  type_table_t *types;

  types = table->type_table;
  pp_open_block(&printer->pp, PP_OPEN_SMT2_DEF);
  smt2_pp_symbol(printer, name);
  if (object_is_function(table, c)) {
    smt2_pp_function_params(printer, types, tau);
    smt2_pp_function_definition(printer, table, tau, c);
  } else if (object_is_update(table, c)) {
    smt2_pp_function_params(printer, types, tau);
    smt2_pp_update_definition(printer, table, c);
  } else {
    pp_string(&printer->pp, "()");
    smt2_pp_type(printer, types, tau);
    smt2_pp_object_in_def(printer, table, tau, c);
  }
  pp_close_block(&printer->pp, true);
}


/*
 * Variant of smt2_pp_object that uses SMT2 syntax for arrays
 */
void smt2_pp_smt2_object(smt2_pp_t *printer, value_table_t *table, value_t c, type_t tau) {
  value_fun_t *fun;

  if (object_is_function(table, c)) {
    fun = vtbl_function(table, c);
    smt2_pp_array(printer, table, fun->type, c);
  } else if (object_is_update(table, c)) {
    smt2_pp_array_update(printer, table, c);
  } else {
    smt2_pp_typed_object(printer, table, c, tau);
  }
}
