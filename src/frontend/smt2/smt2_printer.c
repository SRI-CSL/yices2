/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRETTY PRINTER FOR CONCRETE VALUES USING THE SMT2 SYNTAX
 */

#include <inttypes.h>

#include "frontend/smt2/smt2_printer.h"
#include "io/type_printer.h"


/*
 * Printing for each object type
 */
static inline void smt2_pp_bitvector(yices_pp_t *printer, value_bv_t *b) {
  pp_smt2_bv(printer, b->data, b->nbits);
}


/*
 * SMT2 format for integer and rational constants
 */

// side effect on q
static void smt2_pp_integer(yices_pp_t *printer, rational_t *q) {
  assert(q_is_integer(q));

  if (q_is_neg(q)) {
    q_neg(q); // flip the sign
    pp_open_block(printer, PP_OPEN_MINUS);
    pp_rational(printer, q);
    pp_close_block(printer, true);
  } else {
    pp_rational(printer, q);
  }
}

static void smt2_pp_rational(yices_pp_t *printer, rational_t *q) {
  rational_t num, den;

  q_init(&num);
  q_init(&den);
  q_get_num(&num, q); // numerator
  q_get_den(&den, q); // denominator

  assert(q_is_pos(&den) && q_is_integer(&den));

  if (q_is_one(&den)) {
    smt2_pp_integer(printer, &num);
  } else {
    pp_open_block(printer, PP_OPEN_DIV);
    smt2_pp_integer(printer, &num);
    pp_rational(printer, &den);
    pp_close_block(printer, true);
  }

  q_clear(&num);
  q_clear(&den);
}


/*
 * Print object c on stream f
 *
 * There's no support for tuples or mappings in SMT2. They should never occur here.
 */
void smt2_pp_object(yices_pp_t *printer, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);

  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    pp_string(printer, "???");
    break;
  case BOOLEAN_VALUE:
    pp_bool(printer, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    smt2_pp_rational(printer, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    smt2_pp_bitvector(printer, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}


