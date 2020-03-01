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
 * Print a definition in the SMT2 style.
 * - this prints (define-fun name () tau value)
 */
void smt2_pp_def(smt2_pp_t *printer, value_table_t *table, const char *name, type_t tau, value_t c) {
  pp_open_block(&printer->pp, PP_OPEN_SMT2_DEF);
  smt2_pp_symbol(printer, name);
  pp_string(&printer->pp, "()");
  smt2_pp_type(printer, table->type_table, tau);
  smt2_pp_object(printer, table, c);
  pp_close_block(&printer->pp, true);
}

