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

#ifdef HAVE_MCSAT
#include <poly/algebraic_number.h>
#include <poly/upolynomial.h>
#include <poly/integer.h>
#include <poly/dyadic_rational.h>
#endif

#include "frontend/smt2/smt2_printer.h"
#include "frontend/smt2/smt2_symbol_printer.h"
#include "frontend/smt2/smt2_type_printer.h"
#include "utils/memalloc.h"
#include "utils/string_buffers.h"


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

static void smt2_pp_finitefield(smt2_pp_t *printer, value_ff_t *v) {
  pp_finitefield(&printer->pp, v);
}

#ifdef HAVE_MCSAT
/*
 * Append an lp_integer_t as an SMT2 integer numeral into buf.
 * Negative values use the (- N) form required by SMT2.
 */
static void append_lp_integer_smt2_coeff(string_buffer_t *buf, const lp_integer_t *c) {
  int sgn = lp_integer_sgn(lp_Z, c);
  if (sgn == 0) {
    string_buffer_append_string(buf, "0");
    return;
  }
  char *s = lp_integer_to_string(c);  // decimal string, includes '-' if negative
  if (sgn < 0) {
    string_buffer_append_string(buf, "(- ");
    string_buffer_append_string(buf, s + 1);  // skip leading '-'
    string_buffer_append_char(buf, ')');
  } else {
    string_buffer_append_string(buf, s);
  }
  free(s);
}

/*
 * Append a lp_dyadic_rational_t as an SMT2 real literal into buf.
 * Dyadic rational q = q->a / 2^(q->n).
 * Formats: 0.0 | a.0 | (- a.0) | (/ a.0 2^k.0) | (/ (- a.0) 2^k.0)
 */
static void append_dyadic_rational_smt2_real(string_buffer_t *buf, const lp_dyadic_rational_t *q) {
  int sgn = lp_dyadic_rational_sgn(q);
  if (sgn == 0) {
    string_buffer_append_string(buf, "0.0");
    return;
  }

  char *num_str = lp_integer_to_string(&q->a);  // includes '-' if negative
  const char *abs_str = (sgn < 0) ? num_str + 1 : num_str;
  unsigned long k = q->n;

  if (k == 0) {
    if (sgn < 0) string_buffer_append_string(buf, "(- ");
    string_buffer_append_string(buf, abs_str);
    string_buffer_append_string(buf, ".0");
    if (sgn < 0) string_buffer_append_char(buf, ')');
  } else {
    mpz_t pow2;
    mpz_init(pow2);
    mpz_ui_pow_ui(pow2, 2, k);
    char *den_str = mpz_get_str(NULL, 10, pow2);  // caller must free
    mpz_clear(pow2);

    string_buffer_append_string(buf, "(/ ");
    if (sgn < 0) string_buffer_append_string(buf, "(- ");
    string_buffer_append_string(buf, abs_str);
    string_buffer_append_string(buf, ".0");
    if (sgn < 0) string_buffer_append_char(buf, ')');
    string_buffer_append_char(buf, ' ');
    string_buffer_append_string(buf, den_str);
    string_buffer_append_string(buf, ".0)");
    free(den_str);
  }

  free(num_str);
}
#endif /* HAVE_MCSAT */

static void smt2_pp_algebraic(smt2_pp_t *printer, void *a) {
#ifdef HAVE_MCSAT
  const lp_algebraic_number_t *an = (const lp_algebraic_number_t *) a;
  string_buffer_t buf;

  if (an->f == NULL) {
    /*
     * Rational point: the value is exactly the dyadic rational an->I.a.
     * Print it as a real literal.
     */
    init_string_buffer(&buf, 32);
    append_dyadic_rational_smt2_real(&buf, &an->I.a);
    string_buffer_close(&buf);
    pp_clone_string(&printer->pp, buf.data);
    delete_string_buffer(&buf);
    return;
  }

  /*
   * Proper algebraic: output (root-of-with-interval (coeffs p0 ... pn) min max)
   *
   * Normalize the polynomial: compute the square-free part via
   *   f_sqfree = f / gcd(f, f')
   * then take the primitive part (coprime coefficients, positive leading coeff).
   * This is done at print time so it never affects solving performance.
   */
  lp_upolynomial_t *f_deriv  = lp_upolynomial_derivative(an->f);
  lp_upolynomial_t *g        = lp_upolynomial_gcd(an->f, f_deriv);
  lp_upolynomial_delete(f_deriv);

  lp_upolynomial_t *f_sqfree;
  bool sqfree_allocated;
  if (lp_upolynomial_degree(g) == 0) {
    f_sqfree = an->f;
    sqfree_allocated = false;
  } else {
    f_sqfree = lp_upolynomial_div_exact(an->f, g);
    sqfree_allocated = true;
  }
  lp_upolynomial_delete(g);

  lp_upolynomial_t *f_prim = lp_upolynomial_primitive_part_Z(f_sqfree);
  if (sqfree_allocated) lp_upolynomial_delete(f_sqfree);

  size_t deg = lp_upolynomial_degree(f_prim);
  lp_integer_t *coeffs = safe_malloc((deg + 1) * sizeof(lp_integer_t));
  for (size_t i = 0; i <= deg; i++) lp_integer_construct(&coeffs[i]);
  lp_upolynomial_unpack(f_prim, coeffs);

  init_string_buffer(&buf, 128);
  string_buffer_append_string(&buf, "(root-of-with-interval (coeffs");
  for (size_t i = 0; i <= deg; i++) {
    string_buffer_append_char(&buf, ' ');
    append_lp_integer_smt2_coeff(&buf, &coeffs[i]);
  }
  string_buffer_append_string(&buf, ") ");
  append_dyadic_rational_smt2_real(&buf, &an->I.a);
  string_buffer_append_char(&buf, ' ');
  append_dyadic_rational_smt2_real(&buf, &an->I.b);
  string_buffer_append_char(&buf, ')');
  string_buffer_close(&buf);

  pp_clone_string(&printer->pp, buf.data);
  delete_string_buffer(&buf);

  for (size_t i = 0; i <= deg; i++) lp_integer_destruct(&coeffs[i]);
  safe_free(coeffs);
  lp_upolynomial_delete(f_prim);
#else
  pp_algebraic(&printer->pp, a);
#endif
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
  case FINITEFIELD_VALUE:
    smt2_pp_finitefield(printer, table->desc[c].ptr);
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
  value_map_t *mp;
  value_t *maps;
  value_t def;
  type_t tau;
  uint32_t i, j, n, m;

  maps = vtbl_copy_update_maps(table, c, &def, &tau, &n);

  smt2_pp_function_header(printer, table, c, tau);

  /*
   * maps contains an array of mapping objects
   * n = number of elements in maps
   */
  m = vtbl_update(table, c)->arity;
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_EQ);
    pp_open_block(&printer->pp, PP_OPEN_PAR);
    smt2_pp_fun_name(printer, c);

    mp = vtbl_map(table, maps[i]);
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

  safe_free(maps);
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
  value_map_t *mp;
  value_t *maps;
  value_t def;
  type_t tau, range, sigma;
  uint32_t i, j, n, m;

  maps = vtbl_copy_update_maps(table, c, &def, &tau, &n);

  types = table->type_table;

  /*
   * maps contains an array of mapping objects
   * n = number of elements in maps
   */
  m = vtbl_update(table, c)->arity;
  range = function_type_range(types, tau);
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
    mp = vtbl_map(table, maps[i]);
    assert(mp->arity == m);
    for (j=0; j<m; j++) {
      sigma = function_type_domain(types, tau, j);
      smt2_pp_object_in_def(printer, table, sigma, mp->arg[j]);
    }
    smt2_pp_object_in_def(printer, table, range, mp->val);
    pp_close_block(&printer->pp, true);
  }

  safe_free(maps);
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
  value_map_t *mp;
  value_t *maps;
  value_t def;
  type_t tau, range;
  uint32_t i, n;

  maps = vtbl_copy_update_maps(table, c, &def, &tau, &n);

  range = function_type_range(table->type_table, tau);

  /*
   * maps contains an array of mapping objects
   * n = number of elements in maps
   */
  for (i=0; i<n; i++) {
    pp_open_block(&printer->pp, PP_OPEN_ITE);
    mp = vtbl_map(table, maps[i]);
    smt2_pp_map(printer, table, tau, mp);
    smt2_pp_object_in_def(printer, table, range, mp->val);
  }
  smt2_pp_default_value(printer, table, range, def);

  for (i=0; i<n; i++) {
    pp_close_block(&printer->pp, true);
  }

  safe_free(maps);
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
