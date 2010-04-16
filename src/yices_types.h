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
 * - when term or type construction fails, the functions return NULL_TYPE or NULL_TERM.
 * - details about the cause of the failure is stored in an error_record
 * - the error record contains an error code: see below
 *    + extra information that depends on the error code. 
 */
typedef enum {
  NO_ERROR,
  INVALID_TYPE,
  INVALID_TERM,
  POS_INT_REQUIRED,
  NONNEG_INT_REQUIRED,
  TOO_MANY_ARGUMENTS,
  TOO_MANY_VARS,  
  MAX_BVSIZE_EXCEEDED,
  SCALAR_OR_UTYPE_REQUIRED,
  FUNCTION_REQUIRED,
  TUPLE_REQUIRED,
  VARIABLE_REQUIRED,
  INVALID_CONSTANT_INDEX,
  WRONG_NUMBER_OF_ARGUMENTS,  
  TYPE_MISMATCH,
  INCOMPATIBLE_TYPES,
  INVALID_TUPLE_INDEX,
  DUPLICATE_VARIABLE,
  DIVISION_BY_ZERO,
  ARITHTERM_REQUIRED,
  DEGREE_OVERFLOW,
  BITVECTOR_REQUIRED,
  INCOMPATIBLE_BVSIZES,
  INVALID_BITSHIFT,
  INVALID_BVEXTRACT,
  INVALID_BVSIGNEXTEND,
  INVALID_BVZEROEXTEND,
  EMPTY_BITVECTOR,
} error_code_t;


/*
 * error report = a code + 1 or 2 terms + 1 or 2 types + an integer index.
 * + an (erroneous) integer value.
 *
 * Meaningful fields are set depending on the error code: 
 * 
 *  error code                 meaningful fields
 *
 *  NO_ERROR                   none
 *
 *  INVALID_TYPE               type1, index
 *  INVALID_TERM               term1, index
 *  POS_INT_REQUIRED           badval
 *  NONNEG_INT_REQUIRED        badval
 *  TOO_MANY_ARGS              badval
 *  TOO_MANY_VARS              badval
 *  SCALAR_OR_UTYPE_REQUIRED   type1
 *  FUNCTION_REQUIRED          term1
 *  TUPLE_REQUIRED             term1
 *  VARIABLE_REQUIRED          term1, index
 *  INVALID_CONSTANT_INDEX     type1, badval
 *  WRONG_NUMBER_OF_ARGUMENTS  type1, badval
 *  TYPE_MISMATCH              term1, type1, index
 *  INCOMPATIBLE_TYPES         term1, type1, term2, type2
 *  INVALID_TUPLE_INDEX        type1, badval
 *  DUPLICATE_VARIABLE         term1, index
 *
 *  ARITHTERM_REQUIRED         term1
 *  DEGREE_OVERFLOW            none
 *
 *  BITVECTOR_REQUIRED         term1
 *  INCOMPATIBLE_BVSIZES       badval
 *  INVALID_BITSHIFT           badval
 *  INVALID_BVEXTRACT          none
 *  INVALID_BVSIGNEXTEND       none
 *  INVALID_BVZEROEXTEND       none
 *  EMPTY_BITVECTOR            none
 */
typedef struct error_report_s {
  error_code_t code;
  term_t term1;
  type_t type1;
  term_t term2;
  type_t type2;
  int32_t index;
  int32_t badval;
} error_report_t;

#endif  /* YICES_TYPES_H */
