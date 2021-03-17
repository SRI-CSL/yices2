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
 * ERROR MESSAGE
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdint.h>
#include <string.h>
#include <inttypes.h>

#include "api/yices_globals.h"
#include "utils/memalloc.h"
#include "yices.h"


int32_t print_error(FILE *f) {
  error_report_t *error;
  int code;

  error = yices_error_report();
  switch (error->code) {
  case NO_ERROR:
    code = fprintf(f, "no error\n");
    break;

    /*
     * Term/type construction errors
     */
  case INVALID_TYPE:
    code = fprintf(f, "invalid type: (index = %"PRId32")\n", error->type1);
    break;

  case INVALID_TERM:
    code = fprintf(f, "invalid term: (index = %"PRId32")\n", error->term1);
    break;

  case INVALID_CONSTANT_INDEX:
    code = fprintf(f, "invalid index %"PRId64" in constant creation\n", error->badval);
    break;

  case INVALID_VAR_INDEX:
    code = fprintf(f, "invalid index %"PRId64" in variable creation\n", error->badval);
    break;

  case INVALID_TUPLE_INDEX:
    code = fprintf(f, "invalid tuple index: %"PRId64"\n", error->badval);
    break;

  case INVALID_RATIONAL_FORMAT:
    code = fprintf(f, "invalid rational format\n");
    break;

  case INVALID_FLOAT_FORMAT:
    code = fprintf(f, "invalid floating-point format\n");
    break;

  case INVALID_BVBIN_FORMAT:
    code = fprintf(f, "invalid bitvector binary format\n");
    break;

  case INVALID_BVHEX_FORMAT:
    code = fprintf(f, "invalid bitvector hexadecimal format\n");
    break;

  case INVALID_BITSHIFT:
    code = fprintf(f, "invalid index in shift or rotate\n");
    break;

  case INVALID_BVEXTRACT:
    code = fprintf(f, "invalid indices in bv-extract\n");
    break;

  case INVALID_BITEXTRACT:
    code = fprintf(f, "invalid index in bit extraction\n");
    break;

  case TOO_MANY_ARGUMENTS:
    code = fprintf(f, "too many arguments (max arity is %"PRIu32")\n", YICES_MAX_ARITY);
    break;

  case TOO_MANY_VARS:
    code = fprintf(f, "too many variables in quantifier (max is %"PRIu32")\n", YICES_MAX_VARS);
    break;

  case MAX_BVSIZE_EXCEEDED:
    code = fprintf(f, "bitvector size is too large (max is %"PRIu32")\n", YICES_MAX_BVSIZE);
    break;

  case DEGREE_OVERFLOW:
    code = fprintf(f, "overflow in polynomial: degree is too large\n");
    break;

  case DIVISION_BY_ZERO:
    code = fprintf(f, "division by zero\n");
    break;

  case POS_INT_REQUIRED:
    code = fprintf(f, "integer argument must be positive\n");
    break;

  case NONNEG_INT_REQUIRED:
    code = fprintf(f, "integer argument must be non-negative\n");
    break;

  case SCALAR_OR_UTYPE_REQUIRED:
    code = fprintf(f, "invalid type in constant creation\n");
    break;

  case FUNCTION_REQUIRED:
    code = fprintf(f, "argument is not a function\n");
    break;

  case TUPLE_REQUIRED:
    code = fprintf(f, "argument is not a tuple\n");
    break;

  case VARIABLE_REQUIRED:
    code = fprintf(f, "argument is not a variable\n");
    break;

  case ARITHTERM_REQUIRED:
    code = fprintf(f, "argument is not an arithmetic term\n");
    break;

  case BITVECTOR_REQUIRED:
    code = fprintf(f, "argument is not a bitvector\n");
    break;

  case SCALAR_TERM_REQUIRED:
    code = fprintf(f, "argument is not a scalar term\n");
    break;

  case WRONG_NUMBER_OF_ARGUMENTS:
    code = fprintf(f, "wrong number of arguments\n");
    break;

  case TYPE_MISMATCH:
    code = fprintf(f, "type mismatch: invalid argument\n");
    break;

  case INCOMPATIBLE_TYPES:
    code = fprintf(f, "incompatible types\n");
    break;

  case DUPLICATE_VARIABLE:
    code = fprintf(f, "duplicate variable in quantifier or lambda\n");
    break;

  case INCOMPATIBLE_BVSIZES:
    code = fprintf(f, "arguments have incompatible bitsizes\n");
    break;

  case EMPTY_BITVECTOR:
    code = fprintf(f, "bitvector must have positive bitsize\n");
    break;

  case ARITHCONSTANT_REQUIRED:
    code = fprintf(f, "argument is not an arithmetic constant\n");
    break;

  case INVALID_MACRO:
    code = fprintf(f, "invalid macro id: %"PRId64"\n", error->badval);
    break;

  case TOO_MANY_MACRO_PARAMS:
    code = fprintf(f, "too many arguments in type constructor or macro (max = %"PRIu32")\n", TYPE_MACRO_MAX_ARITY);
    break;

  case TYPE_VAR_REQUIRED:
    code = fprintf(f, "argument is not a type variable\n");
    break;

  case DUPLICATE_TYPE_VAR:
    code = fprintf(f, "duplicate variable in type macro definition\n");
    break;

  case BVTYPE_REQUIRED:
    code = fprintf(f, "bitvector type required\n");
    break;

  case BAD_TERM_DECREF:
    code = fprintf(f, "Invalid decref: term has refcount zero\n");
    break;

  case BAD_TYPE_DECREF:
    code = fprintf(f, "Invalid decref: type has refcount zero\n");
    break;

  case INVALID_TYPE_OP:
    code = fprintf(f, "Invalid type-exploration query\n");
    break;

  case INVALID_TERM_OP:
    code = fprintf(f, "Invalid term-exploration query\n");
    break;

    /*
     * Parser errors
     */
  case INVALID_TOKEN:
    code = fprintf(f, "invalid token (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case SYNTAX_ERROR:
    code = fprintf(f, "syntax error (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case UNDEFINED_TYPE_NAME:
    code = fprintf(f, "undefined type name (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case UNDEFINED_TERM_NAME:
    code = fprintf(f, "undefined term name (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case REDEFINED_TYPE_NAME:
    code = fprintf(f, "cannot redefine type (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case REDEFINED_TERM_NAME:
    code = fprintf(f, "cannot redefine term (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case DUPLICATE_NAME_IN_SCALAR:
    code = fprintf(f, "duplicate name in scalar type definition (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case  DUPLICATE_VAR_NAME:
    code = fprintf(f, "duplicate variable in quantifier (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case INTEGER_OVERFLOW:
    code = fprintf(f, "integer overflow (constant does not fit in 32bits) (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case INTEGER_REQUIRED:
    code = fprintf(f, "integer required (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case RATIONAL_REQUIRED:
    code = fprintf(f, "numeric constant required (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case SYMBOL_REQUIRED:
    code = fprintf(f, "symbol required (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case TYPE_REQUIRED:
    code = fprintf(f, "type required (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case NON_CONSTANT_DIVISOR:
    code = fprintf(f, "invalid division (divisor is not a constant) (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case NEGATIVE_BVSIZE:
    code = fprintf(f, "invalid bitvector size (negative number) (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case INVALID_BVCONSTANT:
    code = fprintf(f, "invalid number in 'mk-bv' (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case TYPE_MISMATCH_IN_DEF:
    code = fprintf(f, "type mismatch in 'define' (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case ARITH_ERROR:
    code = fprintf(f, "error in arithmetic operation (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

  case BVARITH_ERROR:
    code = fprintf(f, "error in bitvector operation (line %"PRIu32", column %"PRIu32")\n", error->line, error->column);
    break;

    /*
     * Errors in assertion processing
     */
  case CTX_FREE_VAR_IN_FORMULA:
    code = fprintf(f, "assertion contains a free variable\n");
    break;

  case CTX_LOGIC_NOT_SUPPORTED:
    code = fprintf(f, "logic not supported\n");
    break;

  case CTX_UF_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support uninterpreted functions\n");
    break;

  case CTX_ARITH_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support arithmetic\n");
    break;

  case CTX_BV_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support bitvectors\n");
    break;

  case CTX_ARRAYS_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support arrays or function equalities\n");
    break;

  case CTX_QUANTIFIERS_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support quantifiers\n");
    break;

  case CTX_LAMBDAS_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support lambda terms\n");
    break;

  case CTX_NONLINEAR_ARITH_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support non-linear arithmetic\n");
    break;

  case CTX_FORMULA_NOT_IDL:
    code = fprintf(f, "assertion is not in the IDL fragment\n");
    break;

  case CTX_FORMULA_NOT_RDL:
    code = fprintf(f, "assertion is not in the RDL fragment\n");
    break;

  case CTX_TOO_MANY_ARITH_VARS:
    code = fprintf(f, "too many variables for the arithmetic solver\n");
    break;

  case CTX_TOO_MANY_ARITH_ATOMS:
    code = fprintf(f, "too many atoms for the arithmetic solver\n");
    break;

  case CTX_TOO_MANY_BV_VARS:
    code = fprintf(f, "too many variables for the bitvector solver\n");
    break;

  case CTX_TOO_MANY_BV_ATOMS:
    code = fprintf(f, "too many atoms for the bitvector solver\n");
    break;

  case CTX_ARITH_SOLVER_EXCEPTION:
    code = fprintf(f, "arithmetic solver exception\n");
    break;

  case CTX_BV_SOLVER_EXCEPTION:
    code = fprintf(f, "bitvector solver exception\n");
    break;

  case CTX_ARRAY_SOLVER_EXCEPTION:
    code = fprintf(f, "array solver exception\n");
    break;

  case CTX_SCALAR_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support scalar types\n");
    break;

  case CTX_TUPLE_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support tuples\n");
    break;

  case CTX_UTYPE_NOT_SUPPORTED:
    code = fprintf(f, "the context does not support uninterpreted types\n");
    break;

  case CTX_INVALID_OPERATION:
    code = fprintf(f, "the context state does not allow operation\n");
    break;

  case CTX_OPERATION_NOT_SUPPORTED:
    code = fprintf(f, "operation not supported by the context\n");
    break;

  case CTX_UNKNOWN_DELEGATE:
    code = fprintf(f, "unknown delegate\n");
    break;

  case CTX_DELEGATE_NOT_AVAILABLE:
    code = fprintf(f, "delegate not available\n");
    break;

  case CTX_INVALID_CONFIG:
    code = fprintf(f, "invalid context configuration\n");
    break;

  case CTX_UNKNOWN_PARAMETER:
    code = fprintf(f, "invalid parameter\n");
    break;

  case CTX_INVALID_PARAMETER_VALUE:
    code = fprintf(f, "value not valid for parameter\n");
    break;

  case CTX_UNKNOWN_LOGIC:
    code = fprintf(f, "unknown logic\n");
    break;

  case EVAL_UNKNOWN_TERM:
    code = fprintf(f, "eval error: term value not available in the model\n");
    break;

  case EVAL_FREEVAR_IN_TERM:
    code = fprintf(f, "eval error: free variable in term\n");
    break;

  case EVAL_QUANTIFIER:
    code = fprintf(f, "eval error: term contains quantifiers\n");
    break;

  case EVAL_LAMBDA:
    code = fprintf(f, "eval error: term contains lambdas\n");
    break;

  case EVAL_OVERFLOW:
    code = fprintf(f, "eval error: the term value does not fit the expected type\n");
    break;

  case EVAL_FAILED:
    code = fprintf(f, "exception in term evaluation\n");
    break;

  case EVAL_CONVERSION_FAILED:
    code = fprintf(f, "could not convert value (in model) to a term\n");
    break;

  case EVAL_NO_IMPLICANT:
    code = fprintf(f, "can't build an implicant: input formula is false in the model\n");
    break;

  case MDL_UNINT_REQUIRED:
    code = fprintf(f, "argument is not an uninterpreted term\n");
    break;

  case MDL_CONSTANT_REQUIRED:
    code = fprintf(f, "value is not a constant term\n");
    break;

  case MDL_DUPLICATE_VAR:
    code = fprintf(f, "duplicate term in input array\n");
    break;

  case MDL_FTYPE_NOT_ALLOWED: // not used
    code = fprintf(f, "function-types are not supported\n");
    break;

  case MDL_CONSTRUCTION_FAILED: // not used
    code = fprintf(f, "model-construction failed\n");
    break;

  case MDL_NONNEG_INT_REQUIRED:
    code = fprintf(f, "model value must be non-negative\n");
    break;

  case YVAL_INVALID_OP:
    code = fprintf(f, "invalid operation on yval\n");
    break;

  case YVAL_OVERFLOW:
    code = fprintf(f, "yval overflow: rational does not fit the expected type\n");
    break;

  case MDL_GEN_TYPE_NOT_SUPPORTED:
    code = fprintf(f, "generalization failed: bad variable type\n");
    break;

  case MDL_GEN_NONLINEAR:
    code = fprintf(f, "generalization failed: nonlinear arithmetic\n");
    break;

  case MDL_GEN_FAILED:
    code = fprintf(f, "generalization failed\n");
    break;

  case OUTPUT_ERROR:
    code = fprintf(f, "output error\n");
    break;

  case MCSAT_ERROR_UNSUPPORTED_THEORY:
    code = fprintf(f, "mcsat: unsupported theory\n");
    break;

  case MCSAT_ERROR_NAMED_TERMS_NOT_SUPPORTED:
    code = fprintf(f, "mcsat: checking with assumptions only supports variables as assumptions\n");
    break;

  case INTERNAL_EXCEPTION:
  default:
    code = fprintf(f, "internal error\n");
    break;
  }

  if (code >= 0) {
    fflush(f);
    code = 0;
  } else {
    code = -1;
  }

  return code;
}


/*
 * Construct an error string:
 * - we use an internal buffer and sprintf then we clone the result
 */
#define BUFFER_SIZE 200

char *error_string(void) {
  char buffer[BUFFER_SIZE];
  error_report_t *error;
  char *result;
  size_t size;
  int nchar;

  error = yices_error_report();
  switch (error->code) {
  case NO_ERROR:
    nchar = snprintf(buffer, BUFFER_SIZE, "no error");
    break;

    /*
     * Term/type construction errors
     */
  case INVALID_TYPE:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid type: (index = %"PRId32")", error->type1);
    break;

  case INVALID_TERM:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid term: (index = %"PRId32")", error->term1);
    break;

  case INVALID_CONSTANT_INDEX:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid index %"PRId64" in constant creation", error->badval);
    break;

  case INVALID_VAR_INDEX:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid index %"PRId64" in variable creation", error->badval);
    break;

  case INVALID_TUPLE_INDEX:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid tuple index: %"PRId64, error->badval);
    break;

  case INVALID_RATIONAL_FORMAT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid rational format");
    break;

  case INVALID_FLOAT_FORMAT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid floating-point format");
    break;

  case INVALID_BVBIN_FORMAT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid bitvector binary format");
    break;

  case INVALID_BVHEX_FORMAT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid bitvector hexadecimal format");
    break;

  case INVALID_BITSHIFT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid index in shift or rotate");
    break;

  case INVALID_BVEXTRACT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid indices in bv-extract");
    break;

  case INVALID_BITEXTRACT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid index in bit extraction");
    break;

  case TOO_MANY_ARGUMENTS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many arguments (max arity is %"PRIu32")", YICES_MAX_ARITY);
    break;

  case TOO_MANY_VARS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many variables in quantifier (max is %"PRIu32")", YICES_MAX_VARS);
    break;

  case MAX_BVSIZE_EXCEEDED:
    nchar = snprintf(buffer, BUFFER_SIZE, "bitvector size is too large (max is %"PRIu32")", YICES_MAX_BVSIZE);
    break;

  case DEGREE_OVERFLOW:
    nchar = snprintf(buffer, BUFFER_SIZE, "overflow in polynomial: degree is too large");
    break;

  case DIVISION_BY_ZERO:
    nchar = snprintf(buffer, BUFFER_SIZE, "division by zero");
    break;

  case POS_INT_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "integer argument must be positive");
    break;

  case NONNEG_INT_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "integer argument must be non-negative");
    break;

  case SCALAR_OR_UTYPE_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid type in constant creation");
    break;

  case FUNCTION_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not a function");
    break;

  case TUPLE_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not a tuple");
    break;

  case VARIABLE_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not a variable");
    break;

  case ARITHTERM_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not an arithmetic term");
    break;

  case BITVECTOR_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not a bitvector");
    break;

  case SCALAR_TERM_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not a scalar term");
    break;

  case WRONG_NUMBER_OF_ARGUMENTS:
    nchar = snprintf(buffer, BUFFER_SIZE, "wrong number of arguments");
    break;

  case TYPE_MISMATCH:
    nchar = snprintf(buffer, BUFFER_SIZE, "type mismatch: invalid argument");
    break;

  case INCOMPATIBLE_TYPES:
    nchar = snprintf(buffer, BUFFER_SIZE, "incompatible types");
    break;

  case DUPLICATE_VARIABLE:
    nchar = snprintf(buffer, BUFFER_SIZE, "duplicate variable in quantifier or lambda");
    break;

  case INCOMPATIBLE_BVSIZES:
    nchar = snprintf(buffer, BUFFER_SIZE, "arguments have incompatible bitsizes");
    break;

  case EMPTY_BITVECTOR:
    nchar = snprintf(buffer, BUFFER_SIZE, "bitvector must have positive bitsize");
    break;

  case ARITHCONSTANT_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not an arithmetic constant");
    break;

  case INVALID_MACRO:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid macro id: %"PRId64, error->badval);
    break;

  case TOO_MANY_MACRO_PARAMS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many arguments in type constructor or macro (max = %"PRIu32")", TYPE_MACRO_MAX_ARITY);
    break;

  case TYPE_VAR_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not a type variable");
    break;

  case DUPLICATE_TYPE_VAR:
    nchar = snprintf(buffer, BUFFER_SIZE, "duplicate variable in type macro definition");
    break;

  case BVTYPE_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "bitvector type required");
    break;

  case BAD_TERM_DECREF:
    nchar = snprintf(buffer, BUFFER_SIZE, "Invalid decref: term has refcount zero");
    break;

  case BAD_TYPE_DECREF:
    nchar = snprintf(buffer, BUFFER_SIZE, "Invalid decref: type has refcount zero");
    break;

  case INVALID_TYPE_OP:
    nchar = snprintf(buffer, BUFFER_SIZE, "Invalid type-exploration query");
    break;

  case INVALID_TERM_OP:
    nchar = snprintf(buffer, BUFFER_SIZE, "Invalid term-exploration query");
    break;

    /*
     * Parser errors
     */
  case INVALID_TOKEN:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid token (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case SYNTAX_ERROR:
    nchar = snprintf(buffer, BUFFER_SIZE, "syntax error (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case UNDEFINED_TYPE_NAME:
    nchar = snprintf(buffer, BUFFER_SIZE, "undefined type name (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case UNDEFINED_TERM_NAME:
    nchar = snprintf(buffer, BUFFER_SIZE, "undefined term name (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case REDEFINED_TYPE_NAME:
    nchar = snprintf(buffer, BUFFER_SIZE, "cannot redefine type (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case REDEFINED_TERM_NAME:
    nchar = snprintf(buffer, BUFFER_SIZE, "cannot redefine term (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case DUPLICATE_NAME_IN_SCALAR:
    nchar = snprintf(buffer, BUFFER_SIZE, "duplicate name in scalar type definition (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case  DUPLICATE_VAR_NAME:
    nchar = snprintf(buffer, BUFFER_SIZE, "duplicate variable in quantifier (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case INTEGER_OVERFLOW:
    nchar = snprintf(buffer, BUFFER_SIZE, "integer overflow (constant does not fit in 32bits) (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case INTEGER_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "integer required (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case RATIONAL_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "numeric constant required (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case SYMBOL_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "symbol required (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case TYPE_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "type required (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case NON_CONSTANT_DIVISOR:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid division (divisor is not a constant) (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case NEGATIVE_BVSIZE:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid bitvector size (negative number) (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case INVALID_BVCONSTANT:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid number in 'mk-bv' (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case TYPE_MISMATCH_IN_DEF:
    nchar = snprintf(buffer, BUFFER_SIZE, "type mismatch in 'define' (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case ARITH_ERROR:
    nchar = snprintf(buffer, BUFFER_SIZE, "error in arithmetic operation (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

  case BVARITH_ERROR:
    nchar = snprintf(buffer, BUFFER_SIZE, "error in bitvector operation (line %"PRIu32", column %"PRIu32")", error->line, error->column);
    break;

    /*
     * Errors in assertion processing
     */
  case CTX_FREE_VAR_IN_FORMULA:
    nchar = snprintf(buffer, BUFFER_SIZE, "assertion contains a free variable");
    break;

  case CTX_LOGIC_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "logic not supported");
    break;

  case CTX_UF_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support uninterpreted functions");
    break;

  case CTX_ARITH_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support arithmetic");
    break;

  case CTX_BV_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support bitvectors");
    break;

  case CTX_ARRAYS_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support arrays or function equalities");
    break;

  case CTX_QUANTIFIERS_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support quantifiers");
    break;

  case CTX_LAMBDAS_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support lambda terms");
    break;

  case CTX_NONLINEAR_ARITH_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support non-linear arithmetic");
    break;

  case CTX_FORMULA_NOT_IDL:
    nchar = snprintf(buffer, BUFFER_SIZE, "assertion is not in the IDL fragment");
    break;

  case CTX_FORMULA_NOT_RDL:
    nchar = snprintf(buffer, BUFFER_SIZE, "assertion is not in the RDL fragment");
    break;

  case CTX_TOO_MANY_ARITH_VARS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many variables for the arithmetic solver");
    break;

  case CTX_TOO_MANY_ARITH_ATOMS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many atoms for the arithmetic solver");
    break;

  case CTX_TOO_MANY_BV_VARS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many variables for the bitvector solver");
    break;

  case CTX_TOO_MANY_BV_ATOMS:
    nchar = snprintf(buffer, BUFFER_SIZE, "too many atoms for the bitvector solver");
    break;

  case CTX_ARITH_SOLVER_EXCEPTION:
    nchar = snprintf(buffer, BUFFER_SIZE, "arithmetic solver exception");
    break;

  case CTX_BV_SOLVER_EXCEPTION:
    nchar = snprintf(buffer, BUFFER_SIZE, "bitvector solver exception");
    break;

  case CTX_ARRAY_SOLVER_EXCEPTION:
    nchar = snprintf(buffer, BUFFER_SIZE, "array solver exception");
    break;

  case CTX_SCALAR_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support scalar types");
    break;

  case CTX_TUPLE_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support tuples");
    break;

  case CTX_UTYPE_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context does not support uninterpreted types");
    break;

  case CTX_INVALID_OPERATION:
    nchar = snprintf(buffer, BUFFER_SIZE, "the context state does not allow operation");
    break;

  case CTX_OPERATION_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "operation not supported by the context");
    break;

  case CTX_UNKNOWN_DELEGATE:
    nchar = snprintf(buffer, BUFFER_SIZE, "unknown delegate");
    break;

  case CTX_DELEGATE_NOT_AVAILABLE:
    nchar = snprintf(buffer, BUFFER_SIZE, "delegate not available");
    break;

  case CTX_INVALID_CONFIG:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid context configuration");
    break;

  case CTX_UNKNOWN_PARAMETER:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid parameter");
    break;

  case CTX_INVALID_PARAMETER_VALUE:
    nchar = snprintf(buffer, BUFFER_SIZE, "value not valid for parameter");
    break;

  case CTX_UNKNOWN_LOGIC:
    nchar = snprintf(buffer, BUFFER_SIZE, "unknown logic");
    break;

  case EVAL_UNKNOWN_TERM:
    nchar = snprintf(buffer, BUFFER_SIZE, "eval error: term value not available in the model");
    break;

  case EVAL_FREEVAR_IN_TERM:
    nchar = snprintf(buffer, BUFFER_SIZE, "eval error: free variable in term");
    break;

  case EVAL_QUANTIFIER:
    nchar = snprintf(buffer, BUFFER_SIZE, "eval error: term contains quantifiers");
    break;

  case EVAL_LAMBDA:
    nchar = snprintf(buffer, BUFFER_SIZE, "eval error: term contains lambdas");
    break;

  case EVAL_OVERFLOW:
    nchar = snprintf(buffer, BUFFER_SIZE, "eval error: the term value does not fit the expected type");
    break;

  case EVAL_FAILED:
    nchar = snprintf(buffer, BUFFER_SIZE, "exception in term evaluation");
    break;

  case EVAL_CONVERSION_FAILED:
    nchar = snprintf(buffer, BUFFER_SIZE, "could not convert value (in model) to a term");
    break;

  case EVAL_NO_IMPLICANT:
    nchar = snprintf(buffer, BUFFER_SIZE, "can't build an implicant: input formula is false in the model");
    break;

  case MDL_UNINT_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "argument is not an uninterpreted term");
    break;

  case MDL_CONSTANT_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "value is not a constant term");
    break;

  case MDL_DUPLICATE_VAR:
    nchar = snprintf(buffer, BUFFER_SIZE, "duplicate term in input array");
    break;

  case MDL_FTYPE_NOT_ALLOWED: // not used
    nchar = snprintf(buffer, BUFFER_SIZE, "function-types are not supported");
    break;

  case MDL_CONSTRUCTION_FAILED: // not used
    nchar = snprintf(buffer, BUFFER_SIZE, "model-construction failed");
    break;

  case MDL_NONNEG_INT_REQUIRED:
    nchar = snprintf(buffer, BUFFER_SIZE, "value must be non-negative");
    break;

  case YVAL_INVALID_OP:
    nchar = snprintf(buffer, BUFFER_SIZE, "invalid operation on yval");
    break;

  case YVAL_OVERFLOW:
    nchar = snprintf(buffer, BUFFER_SIZE, "yval overflow: rational does not fit the expected type");
    break;

  case MDL_GEN_TYPE_NOT_SUPPORTED:
    nchar = snprintf(buffer, BUFFER_SIZE, "generalization failed: bad variable type");
    break;

  case MDL_GEN_NONLINEAR:
    nchar = snprintf(buffer, BUFFER_SIZE, "generalization failed: nonlinear arithmetic");
    break;

  case MDL_GEN_FAILED:
    nchar = snprintf(buffer, BUFFER_SIZE, "generalization failed");
    break;

  case OUTPUT_ERROR:
    nchar = snprintf(buffer, BUFFER_SIZE, "output error");
    break;

  case MCSAT_ERROR_UNSUPPORTED_THEORY:
    nchar = snprintf(buffer, BUFFER_SIZE, "mcsat: unsupported theory");
    break;

  case INTERNAL_EXCEPTION:
  default:
    nchar = snprintf(buffer, BUFFER_SIZE, "internal error");
    break;
  }

  // make a copy
  size = nchar + 1;
  if (size > BUFFER_SIZE) {
    // the buffer is too small
    size = BUFFER_SIZE;
  }
  result = (char *) safe_malloc(size);
  assert(strlen(buffer) < size);
  strcpy(result, buffer);

  return result;
}
