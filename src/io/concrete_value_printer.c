/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * OUTPUT FUNCTIONS FOR CONCRETE VALUES
 */

#include <inttypes.h>
#ifdef HAVE_MCSAT
#include <poly/algebraic_number.h>
#endif

#include "io/concrete_value_printer.h"
#include "io/type_printer.h"


/*
 * Printing for each object type
 */
static inline void vtbl_print_unknown(FILE *f) {
  fputs("???", f);
}

static inline void vtbl_print_bool(FILE *f, int32_t b) {
  if (b) {
    fputs("true", f);
  } else {
    fputs("false", f);
  }
}

static inline void vtbl_print_rational(FILE *f, rational_t *v) {
  q_print(f, v);
}

static inline void vtbl_print_bitvector(FILE *f, value_bv_t *b) {
  bvconst_print(f, b->data, b->nbits);
}



/*
 * Print object c on stream f
 */
void vtbl_print_object(FILE *f, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);
  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    vtbl_print_unknown(f);
    break;
  case BOOLEAN_VALUE:
    vtbl_print_bool(f, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    vtbl_print_rational(f, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    vtbl_print_bitvector(f, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}





/*********************
 *  PRETTY PRINTING  *
 ********************/

/*
 * Printing for each object type
 */
static inline void vtbl_pp_bitvector(yices_pp_t *printer, value_bv_t *b) {
  pp_bv(printer, b->data, b->nbits);
}

/*
 * Print object c
 */
void vtbl_pp_object(yices_pp_t *printer, value_table_t *table, value_t c) {
  assert(0 <= c && c < table->nobjects);

  switch (table->kind[c]) {
  case UNKNOWN_VALUE:
    pp_string(printer, "???");
    break;
  case BOOLEAN_VALUE:
    pp_bool(printer, table->desc[c].integer);
    break;
  case RATIONAL_VALUE:
    pp_rational(printer, &table->desc[c].rational);
    break;
  case BITVECTOR_VALUE:
    vtbl_pp_bitvector(printer, table->desc[c].ptr);
    break;
  default:
    assert(false);
  }
}


