/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PUBLIC TYPES
 *
 * All types that are part of the API must be defined here.
 */

#ifndef __YICES_TYPES_H
#define __YICES_TYPES_H

#include <stdint.h>


/*********************
 *  TERMS AND TYPES  *
 ********************/

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



/************************
 *  CONTEXT AND MODELS  *
 ***********************/

/*
 * Context and models (opaque types)
 */
typedef struct context_s context_t;
typedef struct model_s model_t;


/*
 * Context configuration (opaque type)
 */
typedef struct ctx_config_s ctx_config_t;


/*
 * Search parameters (opaque type)
 */
typedef struct param_s param_t;


/*
 * Context status code
 */
typedef enum smt_status {
  STATUS_IDLE,
  STATUS_SEARCHING,
  STATUS_UNKNOWN,
  STATUS_SAT,
  STATUS_UNSAT,
  STATUS_INTERRUPTED,
  STATUS_ERROR
} smt_status_t;





/********************************
 *  VECTORS OF TERMS OR TYPES   *
 *******************************/

/*
 * Some functions return a collection of terms or types
 * via a vector. The vector is an array that gets resized
 * by the library as needed.
 *
 * For each vector type, the API provide three functions:
 * - yices_init_xxx_vector(xxx_vector_t *v)
 * - yices_reset_xxx_vector(xxx_vector_t *v)
 * - yices_delete_xxx_vector(xxx_vector_t *v)
 *
 * The first function must be called first to initialize a vector.
 * The reset function can be used to empty vector v. It just resets
 * v->size to zero.
 * The delete function must be called to delete a vector that is no
 * longer needed. This is required to avoid memory leaks.
 */
typedef struct term_vector_s {
  uint32_t capacity;
  uint32_t size;
  term_t *data;
} term_vector_t;

typedef struct type_vector_s {
  uint32_t capacity;
  uint32_t size;
  type_t *data;
} type_vector_t;



/***********************
 *  TERM CONSTRUCTORS  *
 **********************/

/*
 * These codes are part of the term exploration API.
 */
typedef enum term_constructor {
  YICES_CONSTRUCTOR_ERROR = -1, // to report an error

  // atomic terms
  YICES_BOOL_CONSTANT,       // boolean constant
  YICES_ARITH_CONSTANT,      // rational constant
  YICES_BV_CONSTANT,         // bitvector constant
  YICES_SCALAR_CONSTANT,     // constant of uninterpreted/scalar
  YICES_VARIABLE,            // variable in quantifiers
  YICES_UNINTERPRETED_TERM,  // (i.e., global variables, can't be bound)

  // composite terms
  YICES_ITE_TERM,            // if-then-else
  YICES_APP_TERM,            // application of an uninterpreted function
  YICES_UPDATE_TERM,         // function update
  YICES_TUPLE_TERM,          // tuple constructor
  YICES_EQ_TERM,             // equality
  YICES_DISTINCT_TERM,       // distinct t_1 ... t_n
  YICES_FORALL_TERM,         // quantifier
  YICES_LAMBDA_TERM,         // lambda
  YICES_NOT_TERM,            // (not t)
  YICES_OR_TERM,             // n-ary OR
  YICES_XOR_TERM,            // n-ary XOR

  YICES_BV_ARRAY,            // array of boolean terms
  YICES_BV_DIV,              // unsigned division
  YICES_BV_REM,              // unsigned remainder
  YICES_BV_SDIV,             // signed division
  YICES_BV_SREM,             // remainder in signed division (rounding to 0)
  YICES_BV_SMOD,             // remainder in signed division (rounding to -infinity)
  YICES_BV_SHL,              // shift left (padding with 0)
  YICES_BV_LSHR,             // logical shift right (padding with 0)
  YICES_BV_ASHR,             // arithmetic shift right (padding with sign bit)
  YICES_BV_GE_ATOM,          // unsigned comparison: (t1 >= t2)
  YICES_BV_SGE_ATOM,         // signed comparison (t1 >= t2)
  YICES_ARITH_GE_ATOM,       // atom (t1 >= t2) for arithmetic terms: t2 is always 0
  YICES_ARITH_ROOT_ATOM,     // atom (0 <= k <= root_count(p)) && (x r root(p, k)) for r in <, <=, ==, !=, >, >=


  YICES_ABS,                 // absolute value
  YICES_CEIL,                // ceil
  YICES_FLOOR,               // floor
  YICES_RDIV,                // real division (as in x/y)
  YICES_IDIV,                // integer division
  YICES_IMOD,                // modulo
  YICES_IS_INT_ATOM,         // integrality test: (is-int t)
  YICES_DIVIDES_ATOM,        // divisibility test: (divides t1 t2)
  
  // projections
  YICES_SELECT_TERM,         // tuple projection
  YICES_BIT_TERM,            // bit-select: extract the i-th bit of a bitvector

  // sums
  YICES_BV_SUM,              // sum of pairs a * t where a is a bitvector constant (and t is a bitvector term)
  YICES_ARITH_SUM,           // sum of pairs a * t where a is a rational (and t is an arithmetic term)

  // products
  YICES_POWER_PRODUCT        // power products: (t1^d1 * ... * t_n^d_n)
} term_constructor_t;


/**********************
 *  VALUES IN MODELS  *
 *********************/

/*
 * A model maps terms to constant objects that can be
 * atomic values, tuples, or functions. These different
 * objects form a DAG. The API provides functions to
 * explore this DAG. Every node in this DAG is defined
 * by a unique id and a tag that identifies the node type.
 *
 * Atomic nodes have one of the following tags:
 *  YVAL_UNKNOWN    (special marker)
 *  YVAL_BOOL       Boolean constant
 *  YVAL_RATIONAL   Rational constant
 *  YVAL_BV         Bitvector constant
 *  YVAL_SCALAR     Constant of uninterpreted or scalar type
 *
 * Non-leaf nodes:
 *  YVAL_TUPLE      Tuple
 *  YVAL_FUNCTION   Function
 *  YVAL_MAPPING    A pair [tuple -> value].
 *
 * All functions are defined by a finite set of mappings
 * and a default value. For example, if we have 
 *   f(0, 0) = 0
 *   f(0, 1) = 1
 *   f(1, 0) = 1
 *   f(1, 1) = 2
 *   f(x, y) = 2 if x and y  are different from 0 and 1
 *
 * Then f will be represented as follows:
 * - default value = 2
 * - mappings: 
 *     [0, 0 -> 0]
 *     [0, 1 -> 1]
 *     [1, 0 -> 1]
 *
 * In the DAG, there is one node for f, one node for the default value,
 * and three nodes for each of the three  mappings.
 */

// Tags for the node descriptors
typedef enum yval_tag {
  YVAL_UNKNOWN,
  YVAL_BOOL,
  YVAL_RATIONAL,
  YVAL_BV,
  YVAL_SCALAR,
  YVAL_TUPLE,
  YVAL_FUNCTION,
  YVAL_MAPPING
} yval_tag_t;

// Node descriptor
typedef struct yval_s {
  int32_t node_id;
  yval_tag_t node_tag;
} yval_t;

// Vector of node descriptors
typedef struct yval_vector_s {
  uint32_t capacity;
  uint32_t size;
  yval_t *data;
} yval_vector_t;



/*************************
 * MODEL GENERALIZATION  *
 ************************/

/*
 * These codes define a generalization algorithm for functions
 *      yices_generalize_model
 * and  yices_generalize_model_array
 *
 * There are currently two algorithms: generalization by
 * substitution and generalization by projection.
 * The default is to select the algorithm based on variables
 * to eliminate.
 */
typedef enum yices_gen_mode {
  YICES_GEN_DEFAULT,
  YICES_GEN_BY_SUBST,
  YICES_GEN_BY_PROJ
} yices_gen_mode_t;



/*****************
 *  ERROR CODES  *
 ****************/

/*
 * Error reports
 * - the API function return a default value if there's an error
 *   (e.g., term constructors return NULL_TERM, type constructors return NULL_TYPE).
 * - details about the cause of the error are stored in an error_report structure
 *   defined below.
 * - the error report contains an error code and extra information
 *   that depends on the error code.
 */
typedef enum error_code {
  NO_ERROR = 0,

  /*
   * Errors in type or term construction
   */
  INVALID_TYPE,
  INVALID_TERM,
  INVALID_CONSTANT_INDEX,
  INVALID_VAR_INDEX,       // Not used anymore
  INVALID_TUPLE_INDEX,
  INVALID_RATIONAL_FORMAT,
  INVALID_FLOAT_FORMAT,
  INVALID_BVBIN_FORMAT,
  INVALID_BVHEX_FORMAT,
  INVALID_BITSHIFT,
  INVALID_BVEXTRACT,
  INVALID_BITEXTRACT,      // added 2014/02/17
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
  SCALAR_TERM_REQUIRED,
  WRONG_NUMBER_OF_ARGUMENTS,
  TYPE_MISMATCH,
  INCOMPATIBLE_TYPES,
  DUPLICATE_VARIABLE,
  INCOMPATIBLE_BVSIZES,
  EMPTY_BITVECTOR,
  ARITHCONSTANT_REQUIRED,  // added 2013/01/23
  INVALID_MACRO,           // added 2013/03/31
  TOO_MANY_MACRO_PARAMS,   // added 2013/03/31
  TYPE_VAR_REQUIRED,       // added 2013/03/31
  DUPLICATE_TYPE_VAR,      // added 2013/03/31
  BVTYPE_REQUIRED,         // added 2013/05/27
  BAD_TERM_DECREF,         // added 2013/10/03
  BAD_TYPE_DECREF,         // added 2013/10/03
  INVALID_TYPE_OP,         // added 2014/12/03
  INVALID_TERM_OP,         // added 2014/12/04

  /*
   * Parser errors
   */
  INVALID_TOKEN = 100,
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


  /*
   * Errors in assertion processing.
   * These codes mean that the context, as configured,
   * cannot process the assertions.
   */
  CTX_FREE_VAR_IN_FORMULA = 300,
  CTX_LOGIC_NOT_SUPPORTED,
  CTX_UF_NOT_SUPPORTED,
  CTX_ARITH_NOT_SUPPORTED,
  CTX_BV_NOT_SUPPORTED,
  CTX_ARRAYS_NOT_SUPPORTED,
  CTX_QUANTIFIERS_NOT_SUPPORTED,
  CTX_LAMBDAS_NOT_SUPPORTED,
  CTX_NONLINEAR_ARITH_NOT_SUPPORTED,
  CTX_FORMULA_NOT_IDL,
  CTX_FORMULA_NOT_RDL,
  CTX_TOO_MANY_ARITH_VARS,
  CTX_TOO_MANY_ARITH_ATOMS,
  CTX_TOO_MANY_BV_VARS,
  CTX_TOO_MANY_BV_ATOMS,
  CTX_ARITH_SOLVER_EXCEPTION,
  CTX_BV_SOLVER_EXCEPTION,
  CTX_ARRAY_SOLVER_EXCEPTION,
  CTX_SCALAR_NOT_SUPPORTED,   // added 2015/03/26
  CTX_TUPLE_NOT_SUPPORTED,    // added 2015/03/26 
  CTX_UTYPE_NOT_SUPPORTED,    // added 2015/03/26


  /*
   * Error codes for other operations
   */
  CTX_INVALID_OPERATION = 400,
  CTX_OPERATION_NOT_SUPPORTED,


  /*
   * Errors in context configurations and search parameter settings
   */
  CTX_INVALID_CONFIG = 500,
  CTX_UNKNOWN_PARAMETER,
  CTX_INVALID_PARAMETER_VALUE,
  CTX_UNKNOWN_LOGIC,

  /*
   * Error codes for model queries
   */
  EVAL_UNKNOWN_TERM = 600,
  EVAL_FREEVAR_IN_TERM,
  EVAL_QUANTIFIER,
  EVAL_LAMBDA,
  EVAL_OVERFLOW,
  EVAL_FAILED,
  EVAL_CONVERSION_FAILED,
  EVAL_NO_IMPLICANT,

  /*
   * Error codes for model construction
   */
  MDL_UNINT_REQUIRED = 700,
  MDL_CONSTANT_REQUIRED,
  MDL_DUPLICATE_VAR,
  MDL_FTYPE_NOT_ALLOWED,
  MDL_CONSTRUCTION_FAILED,  

  /*
   * Error codes in DAG/node queries
   */
  YVAL_INVALID_OP = 800,
  YVAL_OVERFLOW,

  /*
   * Error codes for model generalization
   */
  MDL_GEN_TYPE_NOT_SUPPORTED = 900,
  MDL_GEN_NONLINEAR,
  MDL_GEN_FAILED,

  /*
   * MCSAT error codes
   */
  MCSAT_ERROR_UNSUPPORTED_THEORY = 1000,

  /*
   * Input/output and system errors
   */
  OUTPUT_ERROR = 9000,

  /*
   * Catch-all code for anything else.
   * This is a symptom that a bug has been found.
   */
  INTERNAL_EXCEPTION = 9999
} error_code_t;



/*
 * Error report = a code + line and column + 1 or 2 terms + 1 or 2 types
 * + an (erroneous) integer value.
 *
 * The yices API returns a negative number and set an error code on
 * error. The fields other than the error code depend on the code.  In
 * addition, the parsing functions (yices_parse_type and
 * yices_parse_term) set the line/column fields on error.
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
 *  INVALID_BITEXTRACT         none
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
 *  SCALAR_TERM_REQUIRED       term1
 *  WRONG_NUMBER_OF_ARGUMENTS  type1, badval
 *  TYPE_MISMATCH              term1, type1
 *  INCOMPATIBLE_TYPES         term1, type1, term2, type2
 *  DUPLICATE_VARIABLE         term1
 *  INCOMPATIBLE_BVSIZES       term1, type1, term2, type2
 *  EMPTY_BITVECTOR            none
 *  ARITHCONSTANT_REQUIRED    term1
 *  INVALID_MACRO              badval
 *  TOO_MANY_MACRO_PARAMS      badval
 *  TYPE_VAR_REQUIRED          type1
 *  DUPLICATE_TYPE_VAR         type1
 *  BVTYPE_REQUIRED            type1
 *  BAD_TERM_DECREF            term1
 *  BAD_TYPE_DECREF            type1
 *
 * The following error codes are used only by the parsing functions.
 * No field other than line/column is set.
 *
 *  INVALID_TOKEN
 *  SYNTAX_ERROR
 *  UNDEFINED_TERM_NAME
 *  UNDEFINED_TYPE_NAME
 *  REDEFINED_TERM_NAME
 *  REDEFINED_TYPE_NAME
 *  DUPLICATE_NAME_IN_SCALAR
 *  DUPLICATE_VAR_NAME
 *  INTEGER_OVERFLOW
 *  INTEGER_REQUIRED
 *  RATIONAL_REQUIRED
 *  SYMBOL_REQUIRED
 *  TYPE_REQUIRED
 *  NON_CONSTANT_DIVISOR
 *  NEGATIVE_BVSIZE
 *  INVALID_BVCONSTANT
 *  TYPE_MISMATCH_IN_DEF
 *  ARITH_ERROR
 *  BVARITH_ERROR
 *
 * The following error codes are triggered by invalid operations
 * on a context. For these errors, no fields of error_report (other
 * than the code) is meaningful.
 *
 *  CTX_FREE_VAR_IN_FORMULA
 *  CTX_LOGIC_NOT_SUPPORTED
 *  CTX_UF_NOT_SUPPORTED
 *  CTX_ARITH_NOT_SUPPORTED
 *  CTX_BV_NOT_SUPPORTED
 *  CTX_ARRAYS_NOT_SUPPORTED
 *  CTX_QUANTIFIERS_NOT_SUPPORTED
 *  CTX_LAMBDAS_NOT_SUPPORTED
 *  CTX_NONLINEAR_ARITH_NOT_SUPPORTED
 *  CTX_FORMULA_NOT_IDL
 *  CTX_FORMULA_NOT_RDL
 *  CTX_TOO_MANY_ARITH_VARS
 *  CTX_TOO_MANY_ARITH_ATOMS
 *  CTX_TOO_MANY_BV_VARS
 *  CTX_TOO_MANY_BV_ATOMS
 *  CTX_ARITH_SOLVER_EXCEPTION
 *  CTX_BV_SOLVER_EXCEPTION
 *  CTX_ARRAY_SOLVER_EXCEPTION
 *  CTX_SCALAR_NOT_SUPPORTED,
 *  CTX_TUPLE_NOT_SUPPORTED,
 *  CTX_UTYPE_NOT_SUPPORTED,
 *
 *  CTX_INVALID_OPERATION
 *  CTX_OPERATION_NOT_SUPPORTED
 *
 *  CTX_INVALID_CONFIG
 *  CTX_UNKNOWN_PARAMETER
 *  CTX_INVALID_PARAMETER_VALUE
 *  CTX_UNKNOWN_LOGIC
 *
 *
 * Errors for functions that operate on a model (i.e., evaluate
 * terms in a model).
 *  EVAL_UNKNOWN_TERM
 *  EVAL_FREEVAR_IN_TERM
 *  EVAL_QUANTIFIER
 *  EVAL_LAMBDA
 *  EVAL_OVERFLOW
 *  EVAL_FAILED
 *  EVAL_CONVERSION_FAILED
 *  EVAL_NO_IMPLICANT
 *
 *
 * Other error codes. No field is meaningful in the error_report,
 * except the error code:
 *
 *  OUTPUT_ERROR
 *  INTERNAL_EXCEPTION
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
