/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
#include <inttypes.h>

#include "yices.h"
#include "api/yices_globals.h"


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
    code = fprintf(f, "too many arguments (max. arity is %"PRIu32")\n", YICES_MAX_ARITY);
    break;

  case TOO_MANY_VARS:
    code = fprintf(f, "too many variables in quantifier (max. is %"PRIu32")\n", YICES_MAX_VARS);
    break;

  case MAX_BVSIZE_EXCEEDED:
    code = fprintf(f, "bitvector size is too large (max. is %"PRIu32")\n", YICES_MAX_BVSIZE);
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

    /*
     * Parser errors
     */
  case INVALID_TOKEN:
    code = fprintf(f, "invalid token\n");
    break;

  case SYNTAX_ERROR:
    code = fprintf(f, "syntax error\n");
    break;

  case UNDEFINED_TYPE_NAME:
    code = fprintf(f, "undefined type name\n");
    break;

  case UNDEFINED_TERM_NAME:
    code = fprintf(f, "undefined term name\n");
    break;

  case REDEFINED_TYPE_NAME:
    code = fprintf(f, "cannot redefine type\n");
    break;

  case REDEFINED_TERM_NAME:
    code = fprintf(f, "cannot redefine term\n");
    break;

  case DUPLICATE_NAME_IN_SCALAR:
    code = fprintf(f, "duplicate name in scalar type definition\n");
    break;

  case  DUPLICATE_VAR_NAME:
    code = fprintf(f, "duplicate variable in quantifier\n");
    break;

  case INTEGER_OVERFLOW:
    code = fprintf(f, "integer overflow (constant does not fit in 32bits)\n");
    break;

  case INTEGER_REQUIRED:
    code = fprintf(f, "integer required\n");
    break;

  case RATIONAL_REQUIRED:
    code = fprintf(f, "numeric constant required\n");
    break;

  case SYMBOL_REQUIRED:
    code = fprintf(f, "symbol required\n");
    break;

  case TYPE_REQUIRED:
    code = fprintf(f, "type required\n");
    break;

  case NON_CONSTANT_DIVISOR:
    code = fprintf(f, "invalid division (divisor is not a constant)\n");
    break;

  case NEGATIVE_BVSIZE:
    code = fprintf(f, "invalid bitvector size (negative number)\n");
    break;

  case INVALID_BVCONSTANT:
    code = fprintf(f, "invalid number in 'mk-bv'\n");
    break;

  case TYPE_MISMATCH_IN_DEF:
    code = fprintf(f, "type mismatch in 'define'\n");
    break;

  case ARITH_ERROR:
    code = fprintf(f, "error in arithmetic operation\n");
    break;

  case BVARITH_ERROR:
    code = fprintf(f, "error in bitvector operation\n");
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
    code = fprintf(f, "context does not support uninterpreted functions\n");
    break;

  case CTX_ARITH_NOT_SUPPORTED:
    code = fprintf(f, "context does not support arithmetic\n");
    break;

  case CTX_BV_NOT_SUPPORTED:
    code = fprintf(f, "context does not support bitvectors\n");
    break;

  case CTX_ARRAYS_NOT_SUPPORTED:
    code = fprintf(f, "context does not support arrays or function equalities\n");
    break;

  case CTX_QUANTIFIERS_NOT_SUPPORTED:
    code = fprintf(f, "context does not support quantifiers\n");
    break;

  case CTX_LAMBDAS_NOT_SUPPORTED:
    code = fprintf(f, "context does not support lambda terms\n");
    break;

  case CTX_NONLINEAR_ARITH_NOT_SUPPORTED:
    code = fprintf(f, "context does not support non-linear arithmetic\n");
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

  case CTX_INVALID_OPERATION:
    code = fprintf(f, "the context state does not allow operation\n");
    break;

  case CTX_OPERATION_NOT_SUPPORTED:
    code = fprintf(f, "operation not supported by the context\n");
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

  case OUTPUT_ERROR:
    code = fprintf(f, "output error\n");
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
