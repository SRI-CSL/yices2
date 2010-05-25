/*
 * PUBLIC TYPES
 * 
 * All types that are part of the API must be defined here.
 */

#ifndef __YICES_TYPES_H
#define __YICES_TYPES_H

#include <stdint.h>

/*
 * Exported types
 * - term = index in a term table
 * - type = index in a type table
 */
typedef int32_t term_t;
typedef int32_t type_t;

/*
 * Error values
 */
#define NULL_TERM (-1)
#define NULL_TYPE (-1)

/*
 * Context and models (opaque types)
 */
typedef struct context_s context_t;
typedef struct model_s model_t;


/*
 * Error report for term and type construction
 * - when term or type constructor fails, it returns NULL_TYPE or NULL_TERM.
 * - details about the cause of the failure are stored in an error_record
 * - the error record contains an error code: see below
 *    + extra information that depends on the error code. 
 */
typedef enum error_code {
  NO_ERROR,
  INVALID_TYPE,
  INVALID_TERM,
  INVALID_CONSTANT_INDEX,
  INVALID_VAR_INDEX,
  INVALID_TUPLE_INDEX,
  INVALID_RATIONAL_FORMAT,
  INVALID_FLOAT_FORMAT,
  INVALID_BVBIN_FORMAT,
  INVALID_BVHEX_FORMAT,
  INVALID_BITSHIFT,
  INVALID_BVEXTRACT,
  TOO_MANY_ARGUMENTS,
  TOO_MANY_VARS,
  MAX_BVSIZE_EXCEEDED,
  DEGREE_OVERFLOW,
  DIVISION_BY_ZERO,
  POS_INT_REQUIRED,
  NONNEG_INT_REQUIRED,
  SCALAR_OR_UTYPE_REQUIRED,
  FUNCTION_REQUIRED,
  TUPLE_REQUIRED,
  VARIABLE_REQUIRED,
  ARITHTERM_REQUIRED,
  BITVECTOR_REQUIRED,
  WRONG_NUMBER_OF_ARGUMENTS,  
  TYPE_MISMATCH,
  INCOMPATIBLE_TYPES,
  DUPLICATE_VARIABLE,
  INCOMPATIBLE_BVSIZES,
  EMPTY_BITVECTOR,

  // parser errors
  INVALID_TOKEN,
  SYNTAX_ERROR,
  UNDEFINED_TYPE_NAME,
  UNDEFINED_TERM_NAME,
  REDEFINED_TYPE_NAME,
  REDEFINED_TERM_NAME,
  DUPLICATE_NAME_IN_SCALAR,
  DUPLICATE_VAR_NAME,
  INTEGER_OVERFLOW,
  INTEGER_REQUIRED,
  RATIONAL_REQUIRED,
  SYMBOL_REQUIRED,
  TYPE_REQUIRED,
  NON_CONSTANT_DIVISOR,
  NEGATIVE_BVSIZE,
  INVALID_BVCONSTANT,
  TYPE_MISMATCH_IN_DEF,
  ARITH_ERROR,
  BVARITH_ERROR,
} error_code_t;

#define NUM_YICES_ERRORS (BVARITH_ERROR+1)

/*
 * error report = a code + line and column + 1 or 2 terms + 1 or 2 types
 * + an (erroneous) integer value.
 *
 * The yices API functions return a negative number and set an error code
 * on error. The fields other than the error code depend on the code.
 * In addition, the parsing functions (yices_parse_type and yices_parse_term) 
 * set the line/column fields on error.
 *
 *  error code                 meaningful fields
 *
 *  NO_ERROR                   none
 *
 *  INVALID_TYPE               type1
 *  INVALID_TERM               term1
 *  INVALID_CONSTANT_INDEX     type1, badval
 *  INVALID_VAR_INDEX          badval
 *  INVALID_TUPLE_INDEX        type1, badval
 *  INVALID_RATIONAL_FORMAT    none
 *  INVALID_FLOAT_FORMAT       none
 *  INVALID_BVBIN_FORMAT       none
 *  INVALID_BVHEX_FORMAT       none
 *  INVALID_BITSHIFT           badval
 *  INVALID_BVEXTRACT          none
 *  TOO_MANY_ARGUMENTS         badval
 *  TOO_MANY_VARS              badval
 *  MAX_BVSIZE_EXCEEDED        badval
 *  DEGREE_OVERFLOW            badval
 *  DIVISION_BY_ZERO           none
 *  POS_INT_REQUIRED           badval
 *  NONNEG_INT_REQUIRED        none
 *  SCALAR_OR_UTYPE_REQUIRED   type1
 *  FUNCTION_REQUIRED          term1
 *  TUPLE_REQUIRED             term1
 *  VARIABLE_REQUIRED          term1
 *  ARITHTERM_REQUIRED         term1
 *  BITVECTOR_REQUIRED         term1
 *  WRONG_NUMBER_OF_ARGUMENTS  type1, badval
 *  TYPE_MISMATCH              term1, type1
 *  INCOMPATIBLE_TYPES         term1, type1, term2, type2
 *  DUPLICATE_VARIABLE         term1
 *  INCOMPATIBLE_BVSIZES       term1, type1, term2, type2
 *  EMPTY_BITVECTOR            none
 *
 * The following error codes are only used by the parsing functions. 
 * No field other than line/column is set:
 * 
 *  INVALID_TOKEN
 *  SYNTAX_ERROR
 *  UNDEFINED_TERM_NAME
 *  UNDEFINED_TYPE_NAME
 *  REDEFINED_TERM_NAME
 *  REDEFINED_TYPE_NAME
 *  DUPLICATE_VAR_NAME
 *  DUPLICATE_NAME_IN_SCALAR
 *  INTEGER_OVERFLOW
 *  INTEGER_REQUIRED
 *  RATIONAL_REQUIRED
 *  SYMBOL_REQUIRED
 *  NON_CONSTANT_DIVISOR
 *  INVALID_BVCONSTANT
 *  TYPE_MISMATCH_IN_DEF
 *  NEGATIVE_BVSIZE
 *  ARITH_ERROR
 *  BVARITH_ERROR
 */
typedef struct error_report_s {
  error_code_t code;
  uint32_t line;
  uint32_t column;
  term_t term1;
  type_t type1;
  term_t term2;
  type_t type2;
  int64_t badval;
} error_report_t;

#endif  /* YICES_TYPES_H */
