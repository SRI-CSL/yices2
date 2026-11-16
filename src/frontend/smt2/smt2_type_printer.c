/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * PRETTY PRINTER FOR TYPES USING THE SMT2 FORMAT
 */

#include <assert.h>
#include <stdint.h>

#include "frontend/smt2/smt2_symbol_printer.h"
#include "frontend/smt2/smt2_type_printer.h"


/*
 * Atomic type without name should not happen in SMT2.
 * Just in case there's a bug somewhere, we print something here.
 */
static void pp_anonymous_type(smt2_pp_t *printer, type_t tau) {
  pp_quoted_id(&printer->pp, "tau", tau, '|', '|');
}

/*
 * Symbol we use for function types.
 * In SMT2, we should only see function types of arity 1, which we
 * treat as (Array X Y). For anything else, we print (FunType<arity> ....)
 */
static void pp_funtype_sort(smt2_pp_t *printer, uint32_t arity) {
  if (arity == 1) {
    pp_string(&printer->pp, "Array");
  } else {
    pp_id(&printer->pp, "FunType", arity);
  }
}

/*
 * Print tau as a type expression.
 * If tau has a name, and level > 0, expand its definition.
 * If tau has a name and level <= 0, we print its name.
 */
static void smt2_pp_type_recur(smt2_pp_t *printer, type_table_t *tbl, type_t tau, int32_t level) {
  char *name;
  uint32_t i, n;

  assert(good_type(tbl, tau));

  name = type_name(tbl, tau);

  switch (type_kind(tbl, tau)) {
  case BOOL_TYPE:
    pp_string(&printer->pp, "Bool");
    break;

  case INT_TYPE:
    pp_string(&printer->pp, "Int");
    break;

  case REAL_TYPE:
    pp_string(&printer->pp, "Real");
    break;

  case BITVECTOR_TYPE:
    if (name != NULL && level <= 0) {
      smt2_pp_symbol(printer, name);
    } else {
      pp_open_block(&printer->pp, PP_OPEN_SMT2_BV_TYPE);
      pp_uint32(&printer->pp, bv_type_size(tbl, tau));
      pp_close_block(&printer->pp, true);
    }
    break;

  case FF_TYPE:
    if (name != NULL && level <= 0) {
      smt2_pp_symbol(printer, name);
    } else {
      pp_open_block(&printer->pp, PP_OPEN_SMT2_FF_TYPE);
      pp_rational(&printer->pp, ff_type_size(tbl, tau));
      pp_close_block(&printer->pp, true);
    }
    break;

  case UNINTERPRETED_TYPE:
    if (name != NULL) {
      smt2_pp_symbol(printer, name);
    } else {
      pp_anonymous_type(printer, tau);
    }
    break;

  case INSTANCE_TYPE:
    if (name != NULL && level <= 0) {
      smt2_pp_symbol(printer, name);
    } else {
      pp_open_block(&printer->pp, PP_OPEN_PAR);
      assert(tbl->macro_tbl != NULL);
      smt2_pp_symbol(printer, type_macro_name(tbl->macro_tbl, instance_type_cid(tbl, tau)));
      n = instance_type_arity(tbl, tau);
      for (i=0; i<n; i++) {
	smt2_pp_type_recur(printer, tbl, instance_type_param(tbl, tau, i), level - 1);
      }
      pp_close_block(&printer->pp, true);
    }
    break;

  case FUNCTION_TYPE:
    if (name != NULL && level <= 0) {
      smt2_pp_symbol(printer, name);
    } else {
      pp_open_block(&printer->pp, PP_OPEN_PAR);
      n = function_type_arity(tbl, tau);
      pp_funtype_sort(printer, n);
      for (i=0; i<n; i++) {
	smt2_pp_type_recur(printer, tbl, function_type_domain(tbl, tau, i), level - 1);
      }
      smt2_pp_type_recur(printer, tbl, function_type_range(tbl, tau), level - 1);
      pp_close_block(&printer->pp, true);
    }
    break;

  case SCALAR_TYPE:
  case VARIABLE_TYPE:
  case UNUSED_TYPE:
  case TUPLE_TYPE:
  default:
    // Should not occur in SMT2
    pp_anonymous_type(printer, tau);
    break;
  }  
  
}

/*
 * Print type tau using the given pretty printer
 * - this is equivalent to pp_type in the default type_printer
 * - tau must be defined in tbl
 */
void smt2_pp_type(smt2_pp_t *printer, type_table_t *tbl, type_t tau) {
  smt2_pp_type_recur(printer, tbl, tau, 0);
}
