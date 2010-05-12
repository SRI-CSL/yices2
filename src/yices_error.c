/*
 * Print an error message based on the error_report structure
 * maintained by term_api.
 */

#include <stdint.h>
#include <inttypes.h>

#include "yices.h"
#include "yices_types.h"
#include "yices_globals.h"


void yices_print_error(FILE *f) {
  error_report_t *error;

  error = yices_error_report();
  switch (error->code) {
  case NO_ERROR:
    fprintf(f, "no error\n");
    break;

  case INVALID_TYPE:
    fprintf(f, "invalid type: (index = %"PRId32")\n", error->type1);
    break;

  case INVALID_TERM:
    fprintf(f, "invalid term: (index = %"PRId32")\n", error->term1);
    break;

  case INVALID_CONSTANT_INDEX:
    fprintf(f, "invalid index %"PRId32" in constant creation\n", error->badidx);
    break;

  case INVALID_VAR_INDEX:
    fprintf(f, "invalid index %"PRId32" in variable creation\n", error->badidx);
    break;

  case INVALID_TUPLE_INDEX:
    fprintf(f, "invalid tuple index: %"PRId32"\n", error->badidx);
    break;

  case INVALID_RATIONAL_FORMAT:
    fprintf(f, "invalid rational format\n");
    break;

  case INVALID_FLOAT_FORMAT:
    fprintf(f, "invalid floating-point format\n");
    break;

  case INVALID_BVBIN_FORMAT:
    fprintf(f, "invalid bitvector binary format\n");
    break;

  case INVALID_BVHEX_FORMAT:
    fprintf(f, "invalid bitvector hexadecimal format\n");
    break;

  case INVALID_BITSHIFT:
    fprintf(f, "invalid index in shift or rotate\n");
    break;

  case INVALID_BVEXTRACT:
    fprintf(f, "invalid indices in bv-extract\n");
    break;

  case TOO_MANY_ARGUMENTS:
    fprintf(f, "too many arguments (max. arity is %"PRIu32")\n", YICES_MAX_ARITY);
    break;

  case TOO_MANY_VARS:
    fprintf(f, "too many variables in quantifier (max. is %"PRIu32")\n", YICES_MAX_VARS);
    break;

  case MAX_BVSIZE_EXCEEDED:
    fprintf(f, "bitvector size is too large (max. is %"PRIu32")\n", YICES_MAX_BVSIZE);
    break;

  case DEGREE_OVERFLOW:
    fprintf(f, "overflow in polynomial: degree is too large\n");
    break;

  case DIVISION_BY_ZERO:
    fprintf(f, "division by zero\n");
    break;

  case POS_INT_REQUIRED:
    fprintf(f, "integer argument must be positive\n");
    break;

  case NONNEG_INT_REQUIRED:
    fprintf(f, "integer argument must be non-negative\n");
    break;

  case SCALAR_OR_UTYPE_REQUIRED:
    fprintf(f, "invalid type in constant creation\n");
    break;

  case FUNCTION_REQUIRED:
    fprintf(f, "argument is not a function\n");
    break;

  case TUPLE_REQUIRED:
    fprintf(f, "argument is not a tuple\n");
    break;

  case VARIABLE_REQUIRED:
    fprintf(f, "argument is not a variable\n");
    break;

  case ARITHTERM_REQUIRED:
    fprintf(f, "argument is not an arithmetic term\n");
    break;

  case BITVECTOR_REQUIRED:
    fprintf(f, "argument is not a bitvector\n");
    break;

  case WRONG_NUMBER_OF_ARGUMENTS:
    fprintf(f, "wrong number of arguments\n");
    break;

  case TYPE_MISMATCH:
    fprintf(f, "type mismatch: invalid argument\n");
    break;

  case INCOMPATIBLE_TYPES:
    fprintf(f, "incompatible types\n");
    break;

  case DUPLICATE_VARIABLE:
    fprintf(f, "duplicate variable in quantifier\n");
    break;

  case INCOMPATIBLE_BVSIZES:
    fprintf(stderr, "arguments have incompatible bitsizes\n");
    break;    

  case EMPTY_BITVECTOR:
    fprintf(stderr, "bitvector must have positive bitsize\n");
    break;

  default:
    fprintf(stderr, "invalid error code: %"PRId32"\n", error->code);
    break;
  }

  fflush(stderr);
}
