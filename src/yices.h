/*
 * YICES API
 */

#ifndef __YICES_H 
#define __YICES_H


/*
 * On windows/cygwin/mingw:
 *
 *   __YICES_DLLSPEC__ is '__declspec(dllimport) by default
 * 
 * This can be overridden as follows:
 *
 * 1) give -DNOYICES_DLL as a compilation flag (if you want to
 *    link with libyices.a rather than the DLL)
 *
 * 2) define __YICES_DLLSPEC__ to '__declspec(dllexport)' before
 *      #include "yices.h"
 *    when building yices.
 *
 * On any system other than Windows: __YICES_DLLSPEC__ is empty.
 */
#if defined(_WIN32) || defined(__CYGWIN__)
#if defined(NOYICES_DLL)
#undef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__
#else
#if ! defined(__YICES_DLLSPEC__)
#define __YICES_DLLSPEC__ __declspec(dllimport)
#endif
#endif
#else
#define __YICES_DLLSPEC__
#endif


#ifdef __cplusplus
extern "C" {
#endif


/*
 * WARNING: yices requires the header file <stdint.h>
 *
 * It's not available in Microsoft Visual Studio (prior to Visual Studio 2010),
 * and it's possibly missing from other compilers too.
 *
 * If necessary, there are open-source 'stdint.h' that can 
 * be downloaded at
 *      http://code.google.com/p/msinttypes/   (for MS Visual Studio only)
 *   or http://www.azillionmonkeys.com/qed/pstdint.h
 */
#include <stdint.h>
#include <stdio.h>

#include "yices_types.h"
#include "yices_limits.h"



/*********************
 *  VERSION NUMBERS  *
 ********************/

#define __YICES_VERSION            2
#define __YICES_VERSION_MAJOR      0
#define __YICES_VERSION_PATCHLEVEL 0


/*
 * The version as a string "x.y.z"
 */
__YICES_DLLSPEC__ extern const char *yices_version;


/*
 * More details about the release:
 * - build_arch is a string like "x86_64-unknown-linux-gnu"
 * - build_mode is "release" or "debug"
 * - build_date is the compilation date as in "Wed Jun 16 11:11:57 PDT 2010"
 */
__YICES_DLLSPEC__ extern const char *yices_build_arch;
__YICES_DLLSPEC__ extern const char *yices_build_mode;
__YICES_DLLSPEC__ extern const char *yices_build_date;



/***************************************
 *  GLOBAL INITIALIZATION AND CLEANUP  *
 **************************************/

/*
 * This function must be called before anything else to initialize
 * internal data structures.
 */
__YICES_DLLSPEC__ extern void yices_init(void);


/*
 * Delete all internal data structures and objects
 * - this must be called to avoid memory leaks
 */
__YICES_DLLSPEC__ extern void yices_exit(void);


/*
 * Full reset
 * - delete all terms and types and reset the symbol tables
 * - delete all contexts, models, configuration descriptor and 
 *   parameter records.
 */
__YICES_DLLSPEC__ extern void yices_reset(void);




/*********************
 *  ERROR REPORTING  *
 ********************/

/*
 * Get the last error code
 */
__YICES_DLLSPEC__ extern error_code_t yices_error_code(void);


/*
 * Get the last error report
 */
__YICES_DLLSPEC__ extern error_report_t *yices_error_report(void);


/*
 * Clear the error report
 */
__YICES_DLLSPEC__ extern void yices_clear_error(void);


/*
 * Print an error message on stream f.  This converts the current error
 * code + error report structure into an error message.
 * - f must be a non-NULL open stream (writable)
 *
 * Return -1 if there's an error while writing to f (as reported by fprintf).
 * Return 0 otherwise.
 *
 * If there's an error, errno, perror, and friends can be used for diagnostic.
 */
__YICES_DLLSPEC__ extern int32_t yices_print_error(FILE *f);




/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

/*
 * All constructors return NULL_TYPE (-1) if the type definition is wrong.
 */

/*
 * Built-in types bool, int, real.
 */
__YICES_DLLSPEC__ extern type_t yices_bool_type(void);
__YICES_DLLSPEC__ extern type_t yices_int_type(void);
__YICES_DLLSPEC__ extern type_t yices_real_type(void);


/*
 * Bitvectors of given size (number of bits)
 * Requires size > 0
 *
 * If size = 0, error report is set
 *   code = POS_INT_REQUIRED 
 *   badval = size
 * If size > YICES_MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = size
 */
__YICES_DLLSPEC__ extern type_t yices_bv_type(uint32_t size);


/*
 * New scalar type of given cardinality.
 * Requires card > 0
 * 
 * If card = 0, set error report to
 *   code = POS_INT_REQUIRED
 *   badval = size
 */
__YICES_DLLSPEC__ extern type_t yices_new_scalar_type(uint32_t card);


/*
 * New uninterpreted type. No error report.
 */
__YICES_DLLSPEC__ extern type_t yices_new_uninterpreted_type(void);


/*
 * Tuple type tau[0] x ... x tau[n-1].
 * Requires n>0 and tau[0] ... tau[n-1] to be well defined types.
 *
 * Error report 
 * if n == 0, 
 *   code = POS_INT_REQUIRED 
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if tau[i] is not well defined (and tau[0] .. tau[i-1] are)
 *   code = INVALID_TYPE
 *   type1 = tau[i]
 */
__YICES_DLLSPEC__ extern type_t yices_tuple_type(uint32_t n, type_t tau[]);


/*
 * Function type: dom[0] ... dom[n-1] -> range
 * Requires n>0, and dom[0] ... dom[n-1] and range to be well defined
 *
 * Error report
 * if n ==0,
 *   code = POS_INT_REQUIRED
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if range undefined
 *   code = INVALID_TYPE
 *   type1 = range
 * if dom[i] is undefined (and dom[0] ... dom[i-1] are)
 *   code = INVALID_TYPE
 *   type1 = dom[i]
 */
__YICES_DLLSPEC__ extern type_t yices_function_type(uint32_t n, type_t dom[], type_t range);




/***********************
 *  TERM CONSTRUCTORS  *
 **********************/

/*
 * Constructors do type checking and simplification.
 * They return NULL_TERM (< 0) if there's a type error.
 *
 * Type checking rules for function applications:
 * - if f has type [tau_1 ... tau_n -> u]
 *   x_1 has type sigma_1, ..., x_n has type sigma_n
 * - then (f x1 ... xn) is type correct if sigma_i
 *   is a subtype of tau_i for i=1,...,n.
 * Examples: 
 * - x_i has type int and tau_i is real: OK
 * - x_i has type real and tau_i is int: type error
 */

/*
 * Boolean constants: no error report
 */
__YICES_DLLSPEC__ extern term_t yices_true(void);
__YICES_DLLSPEC__ extern term_t yices_false(void);


/*
 * Constant of type tau and id = index
 * - tau must be a scalar type or an uninterpreted type
 * - index must be non-negative, and, if tau is scalar,
 *   index must be less than tau's cardinality.
 *
 * Each constant is identified by its index. Two constants
 * of type tau that have difference indices are distinct.
 *
 * Error report:
 * if tau is undefined
 *   code = INVALID_TYPE
 *   type1 = tau
 * if tau is not scalar or uninterpreted,
 *   code = SCALAR_OR_UTYPE_REQUIRED
 *   type1 = tau
 * if the index is negative or too large
 *   code = INVALID_CONSTANT_INDEX
 *   type1 = tau
 *   badval = index
 */
__YICES_DLLSPEC__ extern term_t yices_constant(type_t tau, int32_t index);


/*
 * Uninterpreted term of type tau
 *
 * An uninterpreted term is like a global variable of type tau. But, we
 * don't call it a variable, because variables have a different meaning
 * in Yices (see next function). 
 *
 * If tau is a function type, then this creates an uninterpreted
 * function (see yices_application).
 *
 *
 * Error report:
 * if tau is undefined
 *   code = INVALID_TYPE
 *   type1 = tau
 */
__YICES_DLLSPEC__ extern term_t yices_new_uninterpreted_term(type_t tau);


/*
 * Variable of type tau. This creates a new variable.
 *
 * Variables are different form uninterpreted terms. They are used
 * in quantifiers and to support substitutions.
 *
 * Error report:
 * if tau is undefined
 *   code = INVALID_TYPE
 *   type1 = tau
 */
__YICES_DLLSPEC__ extern term_t yices_new_variable(type_t tau);


/*
 * Application of an uninterpreted function to n arguments.
 * 
 * Error report:
 * if n == 0,
 *   code = POS_INT_REQUIRED
 *   badval = n
 * if fun or arg[i] is not defined
 *   code = INVALID_TERM
 *   term1 = fun or arg[i]
 * if fun is not a function
 *   code = FUNCTION_REQUIRED
 *   term1 = fun
 * if n != number of arguments required for fun
 *   code = WRONG_NUMBER_OF_ARGUMENTS
 *   type1 = type of fun
 *   badval = n
 * if arg[i] has a wrong type
 *   code = TYPE_MISMATCH
 *   term1 = arg[i]
 *   type1 = expected type
 */
__YICES_DLLSPEC__ extern term_t yices_application(term_t fun, uint32_t n, term_t arg[]);


/*
 * if-then-else
 *
 * Error report:
 * if cond, then_term, or else_term is not a valid term
 *   code = INVALID_TERM
 *   term1 = whichever of cond, then_term, or else_term is invalid
 * if cond is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = cond
 *   type1 = bool (expected type)
 * if then_term and else_term have incompatible types
 *   code = INCOMPATIBLE_TYPES
 *   term1 = then_term
 *   type1 = term1's type
 *   term2 = else_term
 *   type2 = term2's type
 */
__YICES_DLLSPEC__ extern term_t yices_ite(term_t cond, term_t then_term, term_t else_term);


/*
 * Equality (= left right)
 * Disequality (/= left right)
 *
 * Error report:
 * if left or right is not a valid term
 *   code = INVALID_TERM
 *   term1 = left or right
 * if left and right do not have compatible types
 *   code = INCOMPATIBLE_TYPES
 *   term1 = left
 *   type1 = term1's type
 *   term2 = right
 *   type2 = term2's type
 */
__YICES_DLLSPEC__ extern term_t yices_eq(term_t left, term_t right);
__YICES_DLLSPEC__ extern term_t yices_neq(term_t left, term_t right);


/*
 * (not arg)
 *
 * Error report:
 * if arg is invalid
 *    code = INVALID_TERM
 *    term1 = arg
 * if arg is not boolean
 *    code = TYPE_MISMATCH
 *    term1 = arg
 *    type1 = bool (expected type)
 */
__YICES_DLLSPEC__ extern term_t yices_not(term_t arg);


/*
 * (or  arg[0] ... arg[n-1])
 * (and arg[0] ... arg[n-1])
 * (xor arg[0] ... arg[n-1])
 *
 * Note: array arg may be modified.
 *
 * Error report:
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if arg[i] is not a valid term
 *   code = INVALID_TERM
 *   term1 = arg[i]
 * if arg[i] is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = arg[i]
 *   type1 = bool (expected type)
 */
__YICES_DLLSPEC__ extern term_t yices_or(uint32_t n, term_t arg[]);
__YICES_DLLSPEC__ extern term_t yices_and(uint32_t n, term_t arg[]);
__YICES_DLLSPEC__ extern term_t yices_xor(uint32_t n, term_t arg[]);


/*
 * Variants of or/and/xor with 2 or 3 arguments
 */
__YICES_DLLSPEC__ extern term_t yices_or2(term_t t1, term_t t2);
__YICES_DLLSPEC__ extern term_t yices_and2(term_t t1, term_t t2);
__YICES_DLLSPEC__ extern term_t yices_xor2(term_t t1, term_t t2);

__YICES_DLLSPEC__ extern term_t yices_or3(term_t t1, term_t t2, term_t t3);
__YICES_DLLSPEC__ extern term_t yices_and3(term_t t1, term_t t2, term_t t3);
__YICES_DLLSPEC__ extern term_t yices_xor3(term_t t1, term_t t2, term_t t3);


/*
 * (iff left right)
 * (implies left right)
 *
 * Error report:
 * if left or right is invalid
 *    code = INVALID_TERM
 *    term1 = left/right
 * if left or right is not boolean
 *    code = TYPE_MISMATCH
 *    term1 = left/right
 *    type1 = bool (expected type)
 */
__YICES_DLLSPEC__ extern term_t yices_iff(term_t left, term_t right);
__YICES_DLLSPEC__ extern term_t yices_implies(term_t left, term_t right);


/*
 * Tuple constructor
 *
 * Error report:
 * if n == 0
 *   code = POS_INT_REQUIRED
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if one arg[i] is invalid
 *   code = INVALID_TERM
 *   term1 = arg[i]
 */
__YICES_DLLSPEC__ extern term_t yices_tuple(uint32_t n, term_t arg[]);


/*
 * Tuple projection
 *
 * The index must be between 1 and n (where n = number of components in tuple)
 *
 * Error report:
 * if tuple is invalid
 *    code = INVALID_TERM
 *    term1 = tuple
 * if tuple does not have a tuple type
 *    code = TUPLE_REQUIRED
 *    term1 = tuple
 * if index = 0 or index > number of components in tuple
 *    code = INVALID_TUPLE_INDEX
 *    type1 = type of tuple
 *    badval = index
 */
__YICES_DLLSPEC__ extern term_t yices_select(uint32_t index, term_t tuple);


/*
 * Tuple update: replace component i of tuple by new_v
 *
 * The index must be between 1 and n (where n = number of components in tuple)
 *
 * Error report
 * if tuple or new_v is invalid
 *    code = INVALID_TERM
 *    term1 = tuple/new_v
 * if tuple doesn't have a tuple type
 *    code = TUPLE_REQUIRED
 *    term1 = tuple
 * if index = 0 or index > number of components in tuple
 *    code = INVALID_TUPLE_INDEX
 *    type1 = tuple's type
 *    badval = index
 * if new_v has a wrong type
 *    code = TYPE_MISMATCH
 *    term1 = new_v
 *    type1 = expected type (i-th component type in tuple)
 */
__YICES_DLLSPEC__ extern term_t yices_tuple_update(term_t tuple, uint32_t index, term_t new_v);


/*
 * Function update
 *
 * Error report:
 * if n = 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if fun or new_v, or one of arg[i] is invalid
 *    code = INVALID_TERM
 *    term1 = fun, new_v, or arg[i]
 * if fun does not have a function type
 *    code = FUNCTION_REQUIRED
 *    term1 = fun
 * if n != number of arguments for fun
 *    code = WRONG_NUMBER_OF_ARGUMENTS
 *    type1 = type of fun
 *    badval = n
 * if new_v has a wrong type (not a subtype of fun's range)
 *    code = TYPE_MISMATCH
 *    term1 = new_v
 *    type1 = fun's range (expected type)
 * if arg[i] has a wrong type for i-th arg of fun
 *    code = TYPE_MISMATCH
 *    term1 = arg[i]
 *    type1 = expected type
 */
__YICES_DLLSPEC__ extern term_t yices_update(term_t fun, uint32_t n, term_t arg[], term_t new_v);


/*
 * Distinct
 *
 * Note: arg many be modified
 *
 * Error report:
 * if n == 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_ARITY
 *    code = TOO_MANY_ARGUMENTS
 *    badval = n
 * if arg[i] is not a valid term
 *    code = INVALID_TERM
 *    term1 = arg[i]
 * if two terms arg[i] and arg[j] don't have compatible types
 *    code = INCOMPATIBLE_TYPES
 *    term1 = arg[i]
 *    type1 = term1's type
 *    term2 = arg[j]
 *    type2 = term2's type
 */
__YICES_DLLSPEC__ extern term_t yices_distinct(uint32_t n, term_t arg[]);



/*
 * Quantified terms
 *  (forall (var[0] ... var[n-1]) body)
 *  (exists (var[0] ... var[n-1]) body)
 * 
 * Note: array var may be modified
 *
 * Error report:
 * if n == 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_VARS
 *    code = TOO_MANY_VARS
 *    badval = n
 * if body or one of var[i] is invalid
 *    code = INVALID_TERM
 *    term1 = body or var[i]
 * if body is not boolean
 *    code = TYPE_MISMATCH
 *    term1 = body
 *    type1 = bool (expected type)
 * if one of var[i] is not a variable
 *    code = VARIABLE_REQUIRED
 *    term1 = var[i]
 * if one variable occurs twice in var
 *    code = DUPLICATE_VARIABLE
 *    term1 = var[i]
 */
__YICES_DLLSPEC__ extern term_t yices_forall(uint32_t n, term_t var[], term_t body);
__YICES_DLLSPEC__ extern term_t yices_exists(uint32_t n, term_t var[], term_t body);



/*
 * Lambda terms
 *
 * Error report:
 * if n == 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_VARS
 *    code = TOO_MANY_VARS
 *    badval = n
 * if body or one of var[i] is invalid
 *    code = INVALID_TERM
 *    term1 = body or var[i]
 * if one of var[i] is not a variable
 *    code = VARIABLE_REQUIRED
 *    term1 = var[i]
 * if one variable occurs twice in var
 *    code = DUPLICATE_VARIABLE
 *    term1 = var[i]
 *
 */
__YICES_DLLSPEC__ extern term_t yices_lambda(uint32_t n, term_t var[], term_t body);



/**********************************
 *  ARITHMETIC TERM CONSTRUCTORS  *
 *********************************/

/*
 * RATIONAL/INTEGER CONSTANTS
 *
 * Constant terms can be constructed from integers, GMP numbers,
 * or by parsing strings.
 *
 * The constant term constructors return NULL_TERM (-1) if there's
 * an error and set the error report.
 */

/*
 * Zero: no error
 */
__YICES_DLLSPEC__ extern term_t yices_zero(void);


/*
 * Integer constants
 */
__YICES_DLLSPEC__ extern term_t yices_int32(int32_t val);
__YICES_DLLSPEC__ extern term_t yices_int64(int64_t val);


/*
 * Rational constants
 * - den must be non-zero
 * - common factors are removed
 *
 * Error report:
 * if den is zero
 *   code = DIVISION_BY_ZERO
 */
__YICES_DLLSPEC__ extern term_t yices_rational32(int32_t num, uint32_t den);
__YICES_DLLSPEC__ extern term_t yices_rational64(int64_t num, uint64_t den);


/*
 * Constant initialized via GMP integers or rationals.
 * - q must be canonicalized
 */
#ifdef __GMP_H__
__YICES_DLLSPEC__ extern term_t yices_mpz(mpz_t z);
__YICES_DLLSPEC__ extern term_t yices_mpq(mpq_t q);
#endif


/*
 * Convert a string to a rational or integer term. 
 * The string format is
 *     <optional_sign> <numerator>/<denominator>
 *  or <optional_sign> <numerator>
 *
 * where <optional_sign> is + or - or nothing
 * <numerator> and <denominator> are sequences of 
 * decimal digits.
 *
 * Error report:
 *   code = INVALID_RATIONAL_FORMAT if s is not in this format
 *   code = DIVISION_BY_ZERO if the denominator is zero
 */
__YICES_DLLSPEC__ extern term_t yices_parse_rational(const char *s);


/*
 * Convert a string in floating point format to a rational
 * The string must be in one of the following formats:
 *   <optional sign> <integer part> . <fractional part>
 *   <optional sign> <integer part> <exp> <optional sign> <integer>
 *   <optional sign> <integer part> . <fractional part> <exp> <optional sign> <integer>
 * 
 * where <optional sign> is + or - or nothing
 *       <exp> is either 'e' or 'E'
 *
 * Error report:
 * code = INVALID_FLOAT_FORMAT
 */
__YICES_DLLSPEC__ extern term_t yices_parse_float(const char *s);


/*
 * ARITHMETIC OPERATIONS
 */

/*
 * All operations return NULL_TERM if there's an error (NULL_TERM = -1)
 *
 * Error reports:
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not an arithmetic term
 *   code = ARITH_TERM_REQUIRED
 *   term1 = t1 or t2
 *
 * for yices_mul, yices_square, and yices_power,
 * if the result's degree is too large,
 * then the error report is
 *   code = DEGREE_OVERFLOW
 *   badval = product degree
 */
__YICES_DLLSPEC__ extern term_t yices_add(term_t t1, term_t t2);     // t1 + t2
__YICES_DLLSPEC__ extern term_t yices_sub(term_t t1, term_t t2);     // t1 - t2
__YICES_DLLSPEC__ extern term_t yices_neg(term_t t1);                // -t1
__YICES_DLLSPEC__ extern term_t yices_mul(term_t t1, term_t t2);     // t1 * t2
__YICES_DLLSPEC__ extern term_t yices_square(term_t t1);             // t1 * t1
__YICES_DLLSPEC__ extern term_t yices_power(term_t t1, uint32_t d);  // t1 ^ d


/*
 * POLYNOMIALS
 */

/*
 * The functions below construct the term a_0 t_0 + ... + a_{n-1} t_{n-1}
 * given n constant coefficients a_0, ..., a_{n-1} and
 *       n arithmetic terms t_0, ..., t_{n-1}.
 *
 * If there's an error, the functions return NULL_TERM (-1).
 *
 * Error reports:
 * if t[i] is not valid
 *   code = INVALID_TERM
 *   term1 = t[i]
 * if t[i] is not an arithmetic term
 *   code = ARITH_TERM_REQUIRED
 *   term1 = t[i]
 */

/*
 * Polynomial with integer coefficients
 * - a and t must both be arrays of size n
 */
__YICES_DLLSPEC__ extern term_t yices_poly_int32(uint32_t n, int32_t a[], term_t t[]);
__YICES_DLLSPEC__ extern term_t yices_poly_int64(uint32_t n, int64_t a[], term_t t[]);


/*
 * Polynomial with rational coefficients
 * - den, num, and t must be arrays of size n
 * - the coefficient a_i is den[i]/num[i]
 * 
 * Error report:
 * if num[i] is 0
 *   code = DIVISION_BY_ZERO
 */
__YICES_DLLSPEC__ extern term_t yices_poly_rational32(uint32_t n, int32_t num[], uint32_t den[], term_t t[]);
__YICES_DLLSPEC__ extern term_t yices_poly_rational64(uint32_t n, int64_t num[], uint64_t den[], term_t t[]);


/*
 * Coefficients are GMP integers or rationals.
 * - the rationals q[0 ... n-1] must all be canonicalized
 */
#ifdef __GMP_H__
__YICES_DLLSPEC__ extern term_t yices_poly_mpz(uint32_t n, mpz_t z[], term_t t[]);
__YICES_DLLSPEC__ extern term_t yices_poly_mpq(uint32_t n, mpq_t q[], term_t t[]);
#endif



/*
 * ARITHMETIC ATOMS
 */

/*
 * All operations return NULL_TERM if there's an error (NULL_TERM = -1)
 *
 * Error reports
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not an arithmetic term
 *   code = ARITH_TERM_REQUIRED
 *   term1 = t1 or t2
 */
__YICES_DLLSPEC__ extern term_t yices_arith_eq_atom(term_t t1, term_t t2);   // t1 == t2
__YICES_DLLSPEC__ extern term_t yices_arith_neq_atom(term_t t1, term_t t2);  // t1 != t2
__YICES_DLLSPEC__ extern term_t yices_arith_geq_atom(term_t t1, term_t t2);  // t1 >= t2
__YICES_DLLSPEC__ extern term_t yices_arith_leq_atom(term_t t1, term_t t2);  // t1 <= t2
__YICES_DLLSPEC__ extern term_t yices_arith_gt_atom(term_t t1, term_t t2);   // t1 > t2
__YICES_DLLSPEC__ extern term_t yices_arith_lt_atom(term_t t1, term_t t2);   // t1 < t2


/*
 * Comparison with 0:
 *
 * Return NULL_TERM if there's an error.
 *
 * Error report:
 * if t is not valid:
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not an arithmetic term
 *   code = ARITH_TERM_REQUIRES
 *   term1 = t
 */
__YICES_DLLSPEC__ extern term_t yices_arith_eq0_atom(term_t t);   // t == 0
__YICES_DLLSPEC__ extern term_t yices_arith_neq0_atom(term_t t);  // t != 0
__YICES_DLLSPEC__ extern term_t yices_arith_geq0_atom(term_t t);  // t >= 0
__YICES_DLLSPEC__ extern term_t yices_arith_leq0_atom(term_t t);  // t <= 0
__YICES_DLLSPEC__ extern term_t yices_arith_gt0_atom(term_t t);   // t > 0
__YICES_DLLSPEC__ extern term_t yices_arith_lt0_atom(term_t t);   // t < 0




/*********************************
 *  BITVECTOR TERM CONSTRUCTORS  *
 ********************************/

/*
 * BITVECTOR CONSTANTS
 *
 * Constants can be constructed from C integers (32 or 64 bits),
 * from GMP integers, from arrays, or by parsing strings.
 *
 * The constant constructors return NULL_TERM (-1) if there's 
 * an error and set the error report.
 */

/*
 * Conversion of an integer to a bitvector constant.
 * - n = number of bits
 * - x = value
 * The value x is truncated (or 0-padded) to n bits
 *
 * The low-order bit of x is bit 0 of the constant.
 *
 * Error report:
 * if n = 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_BVSIZE
 *    code = MAX_BVSIZE_EXCEEDED
 *    badval = n
 */
__YICES_DLLSPEC__ extern term_t yices_bvconst_uint32(uint32_t n, uint32_t x);
__YICES_DLLSPEC__ extern term_t yices_bvconst_uint64(uint32_t n, uint64_t x);

#ifdef __GMP_H__
__YICES_DLLSPEC__ extern term_t yices_bvconst_mpz(uint32_t n, mpz_t x);
#endif


/*
 * bvconst_zero: set all bits to 0
 * bvconst_one: set low-order bit to 1, all the other bits to 0
 * bvconst_minus_one: set all bits to 1
 *
 * Error report:
 * if n = 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_BVSIZE
 *    code = MAX_BVSIZE_EXCEEDED
 *    badval = n
 */
__YICES_DLLSPEC__ extern term_t yices_bvconst_zero(uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_bvconst_one(uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_bvconst_minus_one(uint32_t n);


/*
 * Construction from an integer array
 * bit i of the constant is 0 if a[i] == 0
 * bit i of the constant is 1 if a[i] != 0
 *
 * Error report:
 * if n = 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_BVSIZE
 *    code = MAX_BVSIZE_EXCEEDED
 *    badval = n
 */
__YICES_DLLSPEC__ extern term_t yices_bvconst_from_array(uint32_t n, int32_t a[]);


/*
 * Parsing from a string of characters '0' and '1'
 * First character = high order bit
 * Last character = low-order bit
 * The constant has n bits if the strings has n characters.
 *
 * Error report:
 * if the format is incorrect:
 *   code = INVALID_BVBIN_FORMAT
 * if the string has more than YICES_MAX_BVSIZE digits
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n
 */
__YICES_DLLSPEC__ extern term_t yices_parse_bvbin(const char *s);


/*
 * Parsing from a hexadecimal string
 * All characters must be '0' to '9' or 'a' to 'f' or 'A' to 'F'
 * - First character = 4 high order bits 
 * - Last character = 4 low-order bits
 * The constant has 4n bits if s has n characters.
 *
 * Error report:
 * if the format is incorrect:
 *   code = INVALID_BVHEX_FORMAT
 * if the result would have more than YICES_MAX_BVSIZE digits
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = 4n
 */
__YICES_DLLSPEC__ extern term_t yices_parse_bvhex(const char *s);




/*
 * BIT-VECTOR ARITHMETIC
 */

/*
 * Binary operations: both arguments must be bitvector terms of the same size.
 * The functions return NULL_TERM (-1) if there's an error.
 *
 * Error reports
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t1 or t2
 * if t1 and t2 do not have the same bitvector type
 *   code = INCOMPATIBLE_TYPES
 *   term1 = t1
 *   type1 = type of t1
 *   term2 = t2
 *   type2 = type of t2
 *
 * For bvmul, bvsquare, or bvpower, if the degree is too large
 *   code = DEGREE_OVERFLOW
 *
 *
 * In case of division by 0, Yices uses the following conventions:
 *   
 *   (bvdiv  x 0b00...0) is the  largest unsigned integer that can be represented using n bits
 *                       (i.e., 0b111....1)
 *
 *   (bvrem  x 0b00...0) is x
 *
 *   (bvsdiv x 0b00...0) is   0b00..01 (i.e., +1) if x's sign bit is 1
 *                       and  0b111111 (i.e., -1) if x's sign bit is 0
 *
 *   (bvsrem x 0b00...0) is x
 *
 *   (bvsmod x 0b00...0) is x
 * 
 */
__YICES_DLLSPEC__ extern term_t yices_bvadd(term_t t1, term_t t2);     // addition (t1 + t2)
__YICES_DLLSPEC__ extern term_t yices_bvsub(term_t t1, term_t t2);     // subtraction (t1 - t2)
__YICES_DLLSPEC__ extern term_t yices_bvneg(term_t t1);                // negation (- t1)
__YICES_DLLSPEC__ extern term_t yices_bvmul(term_t t1, term_t t2);     // multiplication (t1 * t2)
__YICES_DLLSPEC__ extern term_t yices_bvsquare(term_t t1);             // square (t1 * t1)
__YICES_DLLSPEC__ extern term_t yices_bvpower(term_t t1, uint32_t d);  // exponentiation (t1 ^ d)

__YICES_DLLSPEC__ extern term_t yices_bvdiv(term_t t1, term_t t2);   // unsigned div
__YICES_DLLSPEC__ extern term_t yices_bvrem(term_t t1, term_t t2);   // unsigned rem
__YICES_DLLSPEC__ extern term_t yices_bvsdiv(term_t t1, term_t t2);  // signed div
__YICES_DLLSPEC__ extern term_t yices_bvsrem(term_t t1, term_t t2);  // signed rem
__YICES_DLLSPEC__ extern term_t yices_bvsmod(term_t t1, term_t t2);  // signed mod

__YICES_DLLSPEC__ extern term_t yices_bvnot(term_t t1);              // bitwise not
__YICES_DLLSPEC__ extern term_t yices_bvand(term_t t1, term_t t2);   // bitwise and
__YICES_DLLSPEC__ extern term_t yices_bvor(term_t t1, term_t t2);    // bitwise or
__YICES_DLLSPEC__ extern term_t yices_bvxor(term_t t1, term_t t2);   // bitwise exclusive or
__YICES_DLLSPEC__ extern term_t yices_bvnand(term_t t1, term_t t2);  // bitwise not and
__YICES_DLLSPEC__ extern term_t yices_bvnor(term_t t1, term_t t2);   // bitwise not or
__YICES_DLLSPEC__ extern term_t yices_bvxnor(term_t t1, term_t t2);  // bitwise not xor

__YICES_DLLSPEC__ extern term_t yices_bvshl(term_t t1, term_t t2);   // shift t1 left by k bits where k = value of t2
__YICES_DLLSPEC__ extern term_t yices_bvlshr(term_t t1, term_t t2);  // logical shift t1 right by k bits, where k = value of t2
__YICES_DLLSPEC__ extern term_t yices_bvashr(term_t t1, term_t t2);  // arithmetic shift t1 right by k bits, k = value of t2


/*
 * Shift or rotation by an integer constant n
 * - shift_left0 sets the low-order bits to zero
 * - shift_left1 sets the low-order bits to one
 * - shift_right0 sets the high-order bits to zero
 * - shift_right1 sets the high-order bits to one
 * - ashift_right is arithmetic shift, it copies the sign bit
 * - rotate_left: circular rotation
 * - rotate_right: circular rotation 
 *
 * If t is a vector of m bits, then n must satisfy 0 <= n <= m.
 *
 * The functions return NULL_TERM (-1) if there's an error.
 *
 * Error reports:
 * if t is not valid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n > size of t
 *   code = INVALID_BITSHIFT
 *   badval = n
 */
__YICES_DLLSPEC__ extern term_t yices_shift_left0(term_t t, uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_shift_left1(term_t t, uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_shift_right0(term_t t, uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_shift_right1(term_t t, uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_ashift_right(term_t t, uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_rotate_left(term_t t, uint32_t n);
__YICES_DLLSPEC__ extern term_t yices_rotate_right(term_t t, uint32_t n);


/*
 * Extract a subvector of t
 * - t must be a bitvector term of size m
 * - i and j must satisfy i <= j <= m-1
 * The result is the bits i to j of t.
 *
 * Return NULL_TERM (-1) if there's an error.
 *
 * Error reports:
 * if t is not valid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if i <= j <= m-1 does not hold
 *   code = INVALID_BVEXTRACT
 */
__YICES_DLLSPEC__ extern term_t yices_bvextract(term_t t, uint32_t i, uint32_t j);


/*
 * Concatenation
 * - t1 and t2 must be bitvector terms
 *
 * Return NULL_TERM (-1) if there's an error.
 *
 * Error reports
 * if t1 or t2 is not a valid term
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t1 or t2
 */
__YICES_DLLSPEC__ extern term_t yices_bvconcat(term_t t1, term_t t2);


/*
 * Repeated concatenation:
 * - make n copies of t and concatenate them
 * - n must be positive
 *
 * Return NULL_TERM (-1) if there's an error
 *
 * Error report:
 * if t is not valid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n == 0
 *   code = POS_INT_REQUIRED
 *   badval = n
 * if n * size of t > MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n * size of t
 */
__YICES_DLLSPEC__ extern term_t yices_bvrepeat(term_t t, uint32_t n);


/*
 * Sign extension
 * - add n copies of t's sign bit
 *
 * Return NULL_TERM if there's an error.
 *
 * Error reports:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n + size of t > MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n * size of t
 */
__YICES_DLLSPEC__ extern term_t yices_sign_extend(term_t t, uint32_t n);


/*
 * Zero extension
 * - add n zeros to t
 *
 * Return NULL_TERM if there's an error.
 *
 * Error reports:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if n + size of t > MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = n * size of t
 */
__YICES_DLLSPEC__ extern term_t yices_zero_extend(term_t t, uint32_t n);


/*
 * AND-reduction: 
 * if t is b[m-1] ... b[0], then the result is a bit-vector of 1 bit
 * equal to the conjunction of all bits of t (i.e., (and b[0] ... b[m-1])
 *
 * OR-reduction: compute (or b[0] ... b[m-1])
 *
 * Return NULL_TERM if there's an error
 *
 * Error reports:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not a bitvector
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */
__YICES_DLLSPEC__ extern term_t yices_redand(term_t t);
__YICES_DLLSPEC__ extern term_t yices_redor(term_t t); 


/*
 * Bitwise equality comparison: if t1 and t2 are bitvectors of size n,
 * construct (bvredand (bvxnor t1 t2))
 *
 * Return NULL_TERM if there's an error
 *
 * Error reports:
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t1 or t2
 * if t1 and t2 do not have the same bitvector type
 *   code = INCOMPATIBLE_TYPES
 *   term1 = t1
 *   type1 = type of t1
 *   term2 = t2
 *   type2 = type of t2
 */
__YICES_DLLSPEC__ extern term_t yices_redcomp(term_t t1, term_t t2);


/*
 * Convert an array of boolean terms arg[0 ... n-1] into
 * a bitvector term.
 *
 * Error report:
 * if n == 0
 *    code = POS_INT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_BVSIZE
 *    code = MAX_BVSIZE_EXCEEDED
 *    badval = size
 * if arg[i] is invalid
 *    code = INVALID_TERM
 *    term1 = arg[i]
 * if arg[i] is not a boolean
 *    code = TYPE_MISMATCH
 *    term1 = arg[i]
 *    type1 = bool
 */
__YICES_DLLSPEC__ extern term_t yices_bvarray(uint32_t n, term_t arg[]);


/*
 * Extract bit i of vector t (as a boolean)
 *
 * Error report:
 * if t is invalid
 *    code = INVALID_TERM
 *    term1 = t
 * if t is not a bitvector term
 *    code = BITVECTOR_REQUIRES
 *    term1 = t
 * if i >= t's bitsize
 *    code = INVALID_BVEXTRACT
 */
__YICES_DLLSPEC__ extern term_t yices_bitextract(term_t t, uint32_t i);


/*
 * BITVECTOR ATOMS
 */

/*
 * All operations return NULL_TERM (i.e., a negative index) on error
 *
 * Error reports
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 * if t1 or t2 is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t1 or t2
 * if t1 and t2 do not have the same bitvector type
 *   code = INCOMPATIBLE_TYPES
 *   term1 = t1
 *   type1 = type of t1
 *   term2 = t2
 *   type2 = type of t2
 */

/*
 * Equality and disequality
 */
__YICES_DLLSPEC__ extern term_t yices_bveq_atom(term_t t1, term_t t2);
__YICES_DLLSPEC__ extern term_t yices_bvneq_atom(term_t t1, term_t t2);


/*
 * Unsigned inequalities
 */
__YICES_DLLSPEC__ extern term_t yices_bvge_atom(term_t t1, term_t t2);  // t1 >= t2
__YICES_DLLSPEC__ extern term_t yices_bvgt_atom(term_t t1, term_t t2);  // t1 > t2
__YICES_DLLSPEC__ extern term_t yices_bvle_atom(term_t t1, term_t t2);  // t1 <= t2
__YICES_DLLSPEC__ extern term_t yices_bvlt_atom(term_t t1, term_t t2);  // t1 < t2


/*
 * Signed inequalities
 */
__YICES_DLLSPEC__ extern term_t yices_bvsge_atom(term_t t1, term_t t2);  // t1 >= t2
__YICES_DLLSPEC__ extern term_t yices_bvsgt_atom(term_t t1, term_t t2);  // t1 > t2
__YICES_DLLSPEC__ extern term_t yices_bvsle_atom(term_t t1, term_t t2);  // t1 <= t2
__YICES_DLLSPEC__ extern term_t yices_bvslt_atom(term_t t1, term_t t2);  // t1 < t2




/**************
 *  PARSING   *
 *************/

/*
 * Parsing uses the Yices language.
 * - convert an input string s to a type or term.
 * - s must be terminated by '\0'
 *
 * The parsing function return NULL_TYPE or NULL_TERM if there's an
 * error and set the error report. The line and column fields of the
 * error report give information about the error location.
 */
__YICES_DLLSPEC__ extern type_t yices_parse_type(const char *s);
__YICES_DLLSPEC__ extern term_t yices_parse_term(const char *s);



/*******************
 *  SUBSTITUTIONS  *
 ******************/

/*
 * Apply the substitution defined by arrays var and map to a term t
 * - var must be an array of n variables (variables are created using
 *   yices_new_variables).
 * - map must be an array of n terms
 * - the type of map[i] must be a subtype of var[i]'s type
 * - every occurrence of var[i] in t is replaced by map[i]
 * - if a variable occurs several times in v, the last occurrence 
 *   counts. (e.g., if v[i] = x and v[j] = x with i < j, and 
 *   there are no other occurrences of x in v, then x is 
 *   replaced by map[j]).
 * 
 * Return the resulting term or NULL_TERM if there's an error.
 *
 * Error codes:
 * - INVALID_TERM if var[i] or map[i] is not valid
 * - VARIABLE_REQUIRED if var[i] is not a variable
 * - TYPE_MISMATCH if map[i]'s type is not a subtype of var[i]'s type
 * - DEGREE_OVERFLOW if the substitution causes an overflow
 */
__YICES_DLLSPEC__ extern term_t yices_subst_term(uint32_t n, term_t var[], term_t map[], term_t t);


/*
 * Apply a substitution to m terms in parallel
 * - the substitution is defined by arrays var and map:
 *   var must be an array of n variables
 *   map must be an array of n terms
 *   map[i]'s type must be a subtype of var[i]'s type
 * - the substitution is applied to terms t[0] ... t[m-1]
 * - on entry to the function: t[i] must be a valid term 
 *   the function applies the substitution to t[i]
 *   then store the result in place (i.e., t[i] := subst(n, var, map, t[i])).
 *
 * Note: it's more efficient to call this function than to call
 * yices_subst_term m times.
 *
 * Return code: 
 *  0 if all goes well
 * -1 if there's an error
 *
 * Error codes: as above
 */
__YICES_DLLSPEC__ extern int32_t yices_subst_term_array(uint32_t n, term_t var[], term_t map[], uint32_t m, term_t t[]);



/************
 *  NAMES   *
 ***********/

/*
 * It's possible to assign names to terms and types, and later
 * retrieve the term or type from these names.
 *
 * For each term and type, Yices stores a base name, which
 * is used for pretty printing. By default, the base name is NULL.
 * The base name is set on the first call to yices_set_term_name or 
 * yices_set_type_name.
 *
 * In addition, Yices stores two symbol tables that maps names to
 * terms and types, respectively. The name spaces for types and terms
 * are disjoint. The term or type that a name refers to can be changed,
 * and Yices provides a scoping mechanism:
 * - when function  yices_set_term_name(t, name) is called,
 *   then the previous mapping for 'name' (if any) is hidden and now 
 *   'name' refers to term 't'.
 * - if function yices_remove_term_name(name) is called, then the current
 *   mapping for 'name' is removed and the previous mapping (if any)
 *   is restored.
 */

/*
 * The following functions attach a name to a type or a term
 * - name  must be a '\0'-terminated string
 * - if tau or t does not have a base name yet, then name is stored 
 *   as base name for tau or t.
 * - if name referred to another term or another type, then this 
 *   previous mapping is hidden
 *
 * The functions return -1 and set the error report if the term or
 * type is invalid . Otherwise they return 0.
 *
 * A copy of string name is made internally.
 */
__YICES_DLLSPEC__ extern int32_t yices_set_type_name(type_t tau, const char *name);
__YICES_DLLSPEC__ extern int32_t yices_set_term_name(term_t t, const char *name);


/*
 * Remove the current mapping of name
 * - no effect if name is not assigned to a term or type
 * - if name is assigned to some term t or type tau, then this current
 *   mapping is removed. If name was previously mapped to another term
 *   or type, then the previous mapping is restored.
 */
__YICES_DLLSPEC__ extern void yices_remove_type_name(const char *name);
__YICES_DLLSPEC__ extern void yices_remove_term_name(const char *name);


/*
 * Get type or term of the given name
 * - return NULL_TYPE or NULL_TERM if there's no type or term with that name
 */
__YICES_DLLSPEC__ extern type_t yices_get_type_by_name(const char *name);
__YICES_DLLSPEC__ extern term_t yices_get_term_by_name(const char *name);


/*
 * Remove the base name of a type tau or of a term t.
 *
 * The functions return -1 and set the error report if the 
 * type or term is invalid. Otherwise, they return 0.
 *
 * If tau or t doesn't have a name, the functions do nothing
 * and return 0.
 */
__YICES_DLLSPEC__ extern int32_t yices_clear_type_name(type_t tau);
__YICES_DLLSPEC__ extern int32_t yices_clear_term_name(term_t t);
  



/**********************
 *  PRETTY PRINTING   *
 *********************/

/*
 * Pretty printing uses a rectangular display area, characterized
 * by its width, height, and offset as follows.
 * 
 *                  <----------- width ------------->
 *                   _______________________________ 
 * <---- offset --->|                               |   ^
 *                  |                               |   |
 *                  |                               | Height
 *                  |                               |   |
 *                  |                               |   v
 *                   ------------------------------- 
 *
 */

/*
 * Pretty print type tau or term t on file f
 * - width, height, offset define the print area
 * - f = output file to use. 
 *   f must be open and writable.
 *
 * - return -1 on error
 * - return 0 otherwise.
 *
 * - possible error report for yices_pp_type
 *    code = INVALID_TYPE
 *    type1 = tau
 *
 * - possible error report for yices_pp_term
 *    code = INVALID_TERM
 *    term1 = t
 *
 * - other errors (for both)
 *    code = OUTPUT_ERROR if writing to file f failed.
 *    in this case, errno, perror, etc. can be used for diagnostic.
 */
__YICES_DLLSPEC__ extern int32_t yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset);
__YICES_DLLSPEC__ extern int32_t yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset);




/**************************
 *  SOME CHECKS ON TERMS  *
 *************************/

/*
 * Get the type of term t
 * return NULL_TYPE if t is not a valid term
 * and set the error report:
 *   code = INVALID_TERM
 *   term1 = t
 */
__YICES_DLLSPEC__ extern type_t yices_type_of_term(term_t t);


/*
 * Check the type of a term t:
 * - return 0 for false, 1 for true
 *
 * - term_is_arithmetic check whether t's type is either int or real
 * - term_is_real check whether t's type is real
 * - term_is_int check whether t's type is int 
 * - term_is_scalar check whether t has a scalar or uninterpreted type
 *
 * If t is not a valid term, the check functions return false
 * and set the error report as above.
 */
__YICES_DLLSPEC__ extern int32_t yices_term_is_bool(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_int(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_real(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_arithmetic(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_bitvector(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_tuple(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_function(term_t t);
__YICES_DLLSPEC__ extern int32_t yices_term_is_scalar(term_t t);


/*
 * Size of a bitvector term (i.e., number of bits)
 * - return 0 if there's an error
 *
 * Error report:
 * if t is not a valid term
 *    code = INVALID_TERM
 *    term1 = t
 * if t is not a bitvector term
 *    code = BITVECTOR_REQUIRED
 *    term1 = t
 */
__YICES_DLLSPEC__ extern uint32_t yices_term_bitsize(term_t t);





/****************************
 *  CONTEXT CONFIGURATION   *
 ***************************/

/*
 * When a context is created, it is possible to configure it to use a
 * specific solver or a specific combination of solvers.  It is also
 * possible to specify whether or not the context should support
 * features such as push and pop.
 * 
 * The following theory solvers are currently available:
 * - egraph (solver for uninterpreted functions)
 * - bitvector solver
 * - array solver
 * - solver for linear arithmetic based on simplex
 * - solver for integer difference logic (based on Floyd-Warshall)
 * - solver for real difference logic (also based on Floyd-Warshall)
 *
 * The following combinations of theory solvers can be used:
 * - no solvers at all
 * - egraph alone
 * - bitvector solver alone
 * - simplex solver alone
 * - integer Floyd-Warshall solver alone
 * - real Floyd-Warshall solver alone
 * - egraph + bitvector solver
 * - egraph + simplex solver
 * - egraph + array solver
 * - egraph + bitvector + array solver
 * - egraph + simplex + array solver
 * - egraph + simplex + bitvector + array solver
 *
 * If no solvers are used, the context can deal only with Boolean
 * formulas.
 *
 * When the simplex solver is used, it's also possible to
 * specify which arithmetic fragment is intended, namely:
 * - integer difference logic              (IDL)
 * - real difference logic                 (RDL)
 * - real linear arithmetic                (LRA)
 * - integer linear arithmetic             (LIA)
 * - mixed integer/real linear arithmetic  (LIRA)
 *
 * In addition to the solver combination, a context can be configured
 * for different usage:
 * - one-shot mode: check satisfiability of one set of formulas
 * - multiple checks: repeated calls to assert/check are allowed
 * - push/pop: push and pop are supported (implies multiple checks)
 * - clean interrupts are supported (implies push/pop)
 * Currently, the Floyd-Warshall solvers can only be used in one-shot mode.
 *
 * By default, a new solver is configured as follows:
 * - solvers: egraph + simplex + bitvector + array solver
 * - usage: push/pop supported
 *
 * To specify another configuration, one must pass a configuration
 * descriptor to function yices_new_context. A configuration descriptor
 * is an opaque structure that includes the following fields: 
 * - arith-fragment: either IDL, RDL, LRA, LIA, or LIRA
 * - uf-solver: either NONE, DEFAULT
 * - bv-solver: either NONE, DEFAULT
 * - array-solver: either NONE, DEFAULT
 * - arith-solver: either NONE, DEFAULT, IFW, RFW, SIMPLEX
 * - mode: either ONE-SHOT, MULTI-CHECKS, PUSH-POP, INTERACTIVE
 *
 * This is done as follows:
 * 1) allocate a configuration descriptor via yices_new_config
 * 2) set the configuration parameters by repeated calls to yices_set_config
 *    or using yices_default_config_for_logic
 * 3) create one or more context with this configuration by passing the 
 *    descriptor to yices_new_context
 * 4) free the configuration descriptor when it's no longer needed
 */

/*
 * Allocate a configuration descriptor:
 * - the descriptor is set to the default configuration
 */
__YICES_DLLSPEC__ extern ctx_config_t *yices_new_config(void);


/*
 * Deletion
 */
__YICES_DLLSPEC__ extern void yices_free_config(ctx_config_t *config);


/*
 * Set a configuration parameter:
 * - name = the parameter name
 * - value = the value
 *
 * The following table specifies the parameters and allowed values for each parameter name:
 *
 *            name    |    value            |      meaning
 *   ----------------------------------------------------------------------------------------
 *            "mode"  | "one-shot"          |  only one call to check is supported
 *                    |                     |
 *                    | "multi-checks"      |  several calls to assert and check are 
 *                    |                     |  possible
 *                    |                     | 
 *                    | "push-pop"          |  like multi-check and with support for
 *                    |                     |  retracting assertions (via push/pop)
 *                    |                     |
 *                    | "interactive"       |  like push-pop, but with automatic context clean
 *                    |                     |  up when search is interrupted.
 *   ----------------------------------------------------------------------------------------
 *    "uf-solver"     | "default"           |  the uf-solver is included
 *                    | "none"              |  no uf-solver
 *   ----------------------------------------------------------------------------------------
 *    "bv-solver"     | "default"           |  the bitvector solver is included
 *                    | "none"              |  no bitvector solver
 *   ----------------------------------------------------------------------------------------
 *    "array-solver"  | "default"           |  the array solver is included
 *                    | "none"              |  no array solver
 *   ----------------------------------------------------------------------------------------
 *    "arith-solver"  | "ifw"               |  solver for IDL, based on the Floyd-Warshall 
 *                    |                     |  algorithm
 *                    |                     |
 *                    | "rfw"               |  solver for RDL, based on Floyd-Warshall
 *                    |                     |
 *                    | "simplex"           |  solver for linear arithmetic, based on Simplex
 *                    |                     |
 *                    | "default"           |  same as "simplex"
 *                    |                     |
 *                    | "none"              |  no arithmetic solver
 *   ----------------------------------------------------------------------------------------
 *   "arith-fragment" | IDL                 |  integer difference logic
 *                    | RDL                 |  real difference logic
 *                    | LIA                 |  linear integer arithmetic
 *                    | LRA                 |  linear real arithmetic
 *                    | LIRA                |  mixed linear arithmetic (real + integer variables)
 *
 * 
 *
 * The function returns -1 if there's an error, 0 otherwise.
 *
 * Error codes:
 *  CTX_UNKNOWN_PARAMETER if name is not a known parameter name
 *  CTX_INVALID_PARAMETER_VALUE if name is known but value does not match the parameter type
 */
__YICES_DLLSPEC__ extern int32_t yices_set_config(ctx_config_t *config, const char *name, const char *value);


/*
 * Set config to a default solver combination for the given logic
 * - return -1 if there's an error
 * - return 0 otherwise
 *
 * The logic must be given as a string, using the SMT-LIB conventions.
 * Currently, Yices recognizes and supports the following logics:
 *
 *   QF_ABV:    arrays and bitvectors
 *   QF_AUFBV:  arrays, bitvectors, uninterpreted functions
 *   QF_AUFLIA: arrays, uninterpreted functions, and linear integer arithmetic
 *   QF_AX:     arrays with extensionality
 *   QF_BV:     bitvectors
 *   QF_IDL:    integer difference logic
 *   QF_LIA:    linear integer arithmetic
 *   QF_LRA:    linear real arithmetic
 *   QF_RDL:    real difference logic
 *   QF_UF:     uninterpreted functions
 *   QF_UFBV:   uninterpreted functions + bitvectors
 *   QF_UFIDL:  uninterpreted functions + integer difference logic
 *   QF_UFLIA:  uninterpreted functions + linear integer arithmetic
 *   QF_UFLRA:  uninterpreted functions + linear real arithmetic
 *
 * In all these logics, QF means quantifier-free.
 *
 * For future extensions, Yices also recognizes the following names
 * for logics that Yices does not support yet. (They require solvers
 * that can deal with quantifiers or non-linear arithmetic).
 *
 *   AUFLIA
 *   AUFLIRA
 *   AUFNIRA
 *   LRA
 *   QF_NIA
 *   QF_NRA
 *   UFLRA
 *   UFNIA
 *
 * 
 * Error codes:
 *  CTX_UNKNOWN_LOGIC if logic is not a valid name
 *  CTX_LOGIC_NOT_SUPPORTED if logic is known but not supported
 */
__YICES_DLLSPEC__ extern int32_t yices_default_config_for_logic(ctx_config_t *config, const char *logic);





/***************
 *  CONTEXTS   *
 **************/

/*
 * A context is a stack of assertions.
 *
 * The intended use is:
 * 1) create a context (empty)
 * 2) assert one or more formulas in the context.
 *    (it's allowed to call assert several times before check).
 * 3) check satisfiability
 * 4) if the context is satisfiable, optionally build a model
 * 5) reset the context or call push or pop, then go back to 2
 * 6) delete the context
 *
 *
 * A context can be in one of the following states:
 * 1) IDLE: this is the initial state.
 *    In this state, it's possible to assert formulas.
 *    After assertions, the status may change to UNSAT (if
 *    the assertions are trivially unsatisfiable). Otherwise
 *    the state remains IDLE.
 * 
 * 2) SEARCHING: this is the context status during search.
 *    The context moves into that state after a call to 'check'
 *    and remains in that state until the solver completes
 *    or the search is interrupted.
 *
 * 3) SAT/UNSAT/UNKNOWN: status returned after a search
 *    - UNSAT means the assertions are not satisfiable.
 *    - SAT means they are satisfiable.
 *    - UNKNOWN means that the solver could not determine whether
 *      the assertions are SAT or UNSAT. This may happen if 
 *      Yices is not complete for the specific logic used (e.g.,
 *      if the formula includes quantifiers).
 *
 * 4) INTERRUPTED: if the context is in the SEARCHING state,
 *    then it can be interrupted via a call to stop_search.
 *    The status INTERRUPTED indicates that.
 *
 * For fine tuning: there are options that determine which internal
 * simplifications are applied when formulas are asserted, and
 * other options to control heuristics used by the solver.
 */

/*
 * Create a new context:
 * - config is an optional argument that defines the context configuration
 * - the configuration specifies which components the context should
 *   include (e.g., egraph, bv_solver, simplex_solver, etc),
 *   and which features should be supported (e.g., whether push/pop are
 *   needed).
 *
 * If config is NULL, the default configuration is used:
 *   push/pop are enabled
 *   the solvers are: egraph + array solver + bv solver + simplex
 *   mixed real/integer arithmetic is supported
 *
 * Otherwise the context is configured as specified by config, provided
 * that configuration is valid.
 *
 * If there's an error (i.e., the configuration is not supported), the
 * function returns NULL and set an error code: CTX_INVALID_CONFIG.
 */
__YICES_DLLSPEC__ extern context_t *yices_new_context(const ctx_config_t *config);


/*
 * Deletion
 */
__YICES_DLLSPEC__ extern void yices_free_context(context_t *ctx);


/*
 * Get status: return the context's status flag
 * - return one of the codes defined in yices_types.h, 
 *   namely one of the constants
 *
 *    STATUS_IDLE 
 *    STATUS_SEARCHING
 *    STATUS_UNKNOWN
 *    STATUS_SAT
 *    STATUS_UNSAT
 *    STATUS_INTERRUPTED
 *
 */
__YICES_DLLSPEC__ extern smt_status_t yices_context_status(context_t *ctx);


/*
 * Reset: remove all assertions and restore ctx's 
 * status to IDLE.
 */
__YICES_DLLSPEC__ extern void yices_reset_context(context_t *ctx);


/*
 * Push: mark a backtrack point
 * - return 0 if this operation is supported by the context
 *         -1 otherwise
 *
 * Error report:
 * - if the context is not configured to support push/pop
 *   code = CTX_OPERATION_NOT_SUPPORTED
 * - if the context status is UNSAT or SEARCHING or INTERRUPTED
 *   code = CTX_INVALID_OPERATION
 */
__YICES_DLLSPEC__ extern int32_t yices_push(context_t *ctx);


/*
 * Pop: backtrack to the previous backtrack point (i.e., the matching
 * call to yices_push).
 * - return 0 if the operation succeeds, -1 otherwise.
 *
 * Error report:
 * - if the context is not configured to support push/pop
 *   code = CTX_OPERATION_NOT_SUPPORTED
 * - if there's no matching push (i.e., the context stack is empty)
 *   or if the context's status is SEARCHING or INTERRUPTED
 *   code = CTX_INVALID_OPERATION
 */
__YICES_DLLSPEC__ extern int32_t yices_pop(context_t *ctx);


/*
 * Several options determine how much simplification is performed
 * when formulas are asserted. It's best to leave them untouched
 * unless you really know what you're doing.
 *
 * The following functions selectively enable/disable a preprocessing
 * option. Current options include:
 *   var-elim: whether to eliminate variables by substitution
 *   arith-elim: more variable elimination for arithmetic (Gaussian elimination)
 *   flatten: whether to flatten nested (or ...)
 *     (e.g., turn (or (or a b) (or c d) ) to (or a b c d))
 *   learn_eq: enable/disable heuristics to learn implied equalities
 *   keep_ite: whether to eliminate term if-then-else or keep them as terms
 *
 * The following functions can be used to enable or disable one of these options.
 * - return code: -1 if there's an error, 0 otherwise.
 *
 * Error codes:
 *  CTX_UNKNOWN_PARAMETER if the option name is not one of the above.
 */
__YICES_DLLSPEC__ extern int32_t yices_context_enable_option(context_t *ctx, const char *option);
__YICES_DLLSPEC__ extern int32_t yices_context_disable_option(context_t *ctx, const char *option);
 


/*
 * Assert formula t in ctx
 * - ctx status must be IDLE or UNSAT or SAT or UNKNOWN
 * - t must be a boolean term
 *
 * If ctx's status is UNSAT, nothing is done.
 * 
 * If ctx's status is IDLE, SAT, or UNKNOWN, then the formula is
 * simplified and asserted in the context. The context status is
 * changed to UNSAT if the formula is simplified to 'false' or
 * to IDLE otherwise.
 * 
 * This returns 0 if there's no error or -1 if there's an error.
 * 
 * Error report:
 * if t is invalid
 *   code = INVALID_TERM
 *   term1 = t
 * if t is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = t
 *   type1 = bool (expected type)
 * if ctx's status is not IDLE or UNSAT or SAT or UNKNOWN
 *   code = CTX_INVALID_OPERATION
 * if ctx's status is neither IDLE nor UNSAT, and the context is 
 * not configured for multiple checks
 *   code = CTX_OPERATION_NOT_SUPPORTED
 *
 * Other error codes are defined in yices_types.h to report that t is
 * outside the logic supported by ctx.
 */
__YICES_DLLSPEC__ extern int32_t yices_assert_formula(context_t *ctx, term_t t);


/*
 * Assert an array of n formulas t[0 ... n-1]
 * - ctx's status must be IDLE or UNSAT or SAT or UNKNOWN
 * - all t[i]'s must be valid boolean terms.
 *
 * The function returns -1 on error, 0 otherwise.
 *
 * The error report is set as in the previous function.
 */
__YICES_DLLSPEC__ extern int32_t yices_assert_formulas(context_t *ctx, uint32_t n, term_t t[]);


/*
 * Check satisfiability: check whether the assertions stored in ctx
 * are satisfiable.  
 * - params is an optional structure that stores heuristic parameters.
 * - if params is NULL, default parameter settings are used.
 *
 * It's better to keep params=NULL unless you encounter performance
 * problems.  Then you may want to play with the heuristics to see if
 * performance improves.
 *
 * The behavior and returned value depend on ctx's current status:
 *
 * 1) If ctx's status is SAT, UNSAT, or UNKNOWN, the function 
 *    does nothing and just returns the status.
 *
 * 2) If ctx's status is IDLE, then the solver searches for a
 *    satisfying assignment. If param != NULL, the search parameters
 *    defined by params are used.
 * 
 *    The function returns one of the following codes:
 *    - SAT: the context is satisfiable
 *    - UNSAT: the context is not satisfiable
 *    - UNKNOWN: satisfiability can't be proved or disproved 
 *    - INTERRUPTED: the search was interrupted
 *
 *    The returned status is also stored as the new ctx's status flag,
 *    with the following exception. If the context was built with 
 *    mode = INTERACTIVE and the search was interrupted, then the
 *    function returns INTERRUPTED but the ctx's state is restored to
 *    what it was before the call to 'yices_check_context' and the
 *    status flag is reset to IDLE.
 *
 * 3) Otherwise, the function does nothing and returns 'STATUS_ERROR', 
 *    it also sets the yices error report (code = CTX_INVALID_OPERATION).
 */
__YICES_DLLSPEC__ extern smt_status_t yices_check_context(context_t *ctx, const param_t *params);


/*
 * Add a blocking clause: this is intended to help enumerate different models
 * for a set of assertions.
 * - if ctx's status is SAT or UNKNOWN, then a new clause is added to ctx
 *   to remove the current truth assignment from the search space. After this
 *   clause is added, the next call to yices_check_context will either produce 
 *   a different truth assignment (hence a different model) or return UNSAT.
 *
 * - ctx's status flag is updated to IDLE (if the new clause is not empty) or 
 *   to UNSAT (if the new clause is the empty clause).
 *
 * Return code: 0 if there's no error, -1 if there's an error.
 *
 * Error report:
 * if ctx's status is different from SAT or UNKNOWN
 *    code = CTX_INVALID_OPERATION
 * if ctx is not configured to support multiple checks
 *    code = CTX_OPERATION_NOT_SUPPORTED
 */
__YICES_DLLSPEC__ extern int32_t yices_assert_blocking_clause(context_t *ctx);


/*
 * Interrupt the search:
 * - this can be called from a signal handler to stop the search,
 *   after a call to yices_check_context to interrupt the solver.
 *
 * If ctx's status is SEARCHING, then the current search is
 * interrupted. Otherwise, the function does nothing.
 */
__YICES_DLLSPEC__ extern void yices_stop_search(context_t *ctx);




/*
 * SEARCH PARAMETERS
 */

/*
 * A parameter record is an opaque object that stores various
 * search parameters and options that control the heuristics used by
 * the solver. 
 *
 * A parameter structure is created by calling 
 * - yices_new_param_structure(void)
 * This returns a parameter structure initialized with default
 * settings.
 *
 * Then individual parameters can be set using function
 * - yices_set_param(s, name, value) where both name and value are 
 *   character strings.
 * - an unknown/unsupported parameter name is ignored
 *
 * Then the param object can be passed on as argument to yices_check_context.
 *
 * When it's no longer needed, the object must be deleted by 
 * calling yices_free_param_structure(param).
 */

/*
 * Return a parameter record initialized with default settings.
 */
__YICES_DLLSPEC__ extern param_t *yices_new_param_record(void);


/*
 * Set a parameter in record p
 * - pname = parameter name
 * - value = setting
 *
 * TBD: describe the parameters and the range of values for each.
 *
 * Return -1 if there's an error, 0 otherwise
 */
__YICES_DLLSPEC__ extern int32_t yices_set_param(param_t *p, const char *pname, const char *value);


/*
 * Delete the record param
 */
__YICES_DLLSPEC__ extern void yices_free_param_record(param_t *param);





/**************
 *   MODELS   *
 *************/

/*
 * Build a model from ctx 
 * - keep_subst indicates whether the model should include
 *   the eliminated variables: 
 *   keep_subst = 0 means don't keep substitutions,
 *   keep_subst != 0 means keep them
 * - ctx status must be SAT or UNKNOWN
 *
 * The function returns NULL if the status isn't SAT or UNKNOWN 
 * and sets an error report (code = CTX_INVALID_OPERATION).
 *
 * When assertions are added to the context, the simplifications may
 * eliminate variables (cf. simplification options above).  The flag
 * 'keep_subst' indicates whether the model should keep track of these
 * eliminated variables and include their value.
 *
 * Example: after the following assertions 
 *
 *    (= x (bv-add y z))
 *    (bv-gt y 0b000)
 *    (bg-gt z 0b000)
 *
 * variable 'x' gets eliminated. Then a call to 'check_context' will
 * return SAT and we can ask for a model 'M'
 * - if 'keep_subst' is false then the value of 'x' in 'M' is unavailable.
 * - if 'keep_subst' is true then the value of 'x' in 'M' is computed,
 *   based on the value of 'y' and 'z' in 'M'.
 *
 * It's always better to set 'keep_subst' true. The only exceptions
 * are some of the large SMT_LIB benchmarks where millions of variables
 * are eliminated.  In such cases, it saves memory to set 'keep_subst'
 * false, and model construction is faster too.
 */
__YICES_DLLSPEC__ extern model_t *yices_get_model(context_t *ctx, int32_t keep_subst);


/*
 * Delete model mdl
 */
__YICES_DLLSPEC__ extern void yices_free_model(model_t *mdl);


/*
 * Print model mdl on FILE f
 * - f must be open/writable
 */
__YICES_DLLSPEC__ extern void yices_print_model(FILE *f, model_t *mdl);


/*
 * Pretty printing:
 * - f = output file to use
 * - witdh, height, offset define the print area
 * 
 * return -1 on error, 0 otherwise
 *
 * On error:
 *   code = OUTPUT_ERROR (means that writing to f failed)
 *   in this case, errno, perror, etc. can be used for diagnostic.
 */
__YICES_DLLSPEC__ extern int32_t yices_pp_model(FILE *f, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset);
 

/*
 * Evaluation functions. Once a model is constructed, it's possible
 * to query for the value of a term t in that model. The following
 * functions do that for different term types.
 * 
 * The evaluation functions return -1 if the value of t is unknown
 * or can't be computed in the model. Otherwise, they return 0.
 *
 * Possible error codes:
 * If t is not valid:
 *   code = INVALID_TERM
 *   term1 = t
 * If t contains a subterm whose value is not known
 *   code = EVAL_UNKNOWN_TERM
 * If t contains a free variable
 *   code = EVAL_FREEVAR_IN_TERM
 * If t contains quantifier(s)
 *   code = EVAL_QUANTIFIER
 * If t contains lamnda terms
 *   code = EVAL_LAMBDA
 * If the evaluation fails for other reasons:
 *   code = EVAL_FAILED
 *
 * Other codes are possible depending on the specific evaluation function.
 */

/*
 * Value of boolean term t: returned as an integer val
 * - val = 0 means t is false in mdl
 * - val = 1 means t is true in mdl
 *
 * Error codes:
 * If t is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = t
 *   type1 = bool (expected type)
 * + the other evaluation error codes above.
 */
__YICES_DLLSPEC__ extern int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val);


/*
 * Value of arithmetic term t: it can be returned as an integer, a
 * rational (pair num/den), converted to a double, or using the GMP
 * mpz_t and mpq_t representations.
 *
 * Error codes:
 * If t is not an arithmetic term:
 *   code = ARITH_TERM_REQUIRED
 *   term1 = t
 * If t's value does not fit in the *val object
 *   code = EVAL_OVERFLOW
 */
__YICES_DLLSPEC__ extern int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val);
__YICES_DLLSPEC__ extern int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val);
__YICES_DLLSPEC__ extern int32_t yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den);
__YICES_DLLSPEC__ extern int32_t yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den);
__YICES_DLLSPEC__ extern int32_t yices_get_double_value(model_t *mdl, term_t t, double *val);

#ifdef __GMP_H
__YICES_DLLSPEC__ extern int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val);
__YICES_DLLSPEC__ extern int32_t yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val);
#endif


/*
 * Value of bitvector term t in mdl
 * - the value is returned in array val
 * - val must be an integer array of sufficient size to store all bits of t
 * - bit i of t is stored in val[i] (val[i] is either 0 or 1)
 * - the value is returned using small-endian convention:
 *    val[0] is the low-order bit
 *    ...
 *    val[n-1] is the high-order bit 
 *
 * If t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */
__YICES_DLLSPEC__ extern int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]);


/*
 * Value of term t of uninterpreted or scalar type
 * - the value is returned as a constant index in *val 
 *   (with the same meaning as in function yices_constant):
 * - if t has type tau and tau is a scalar type of size n then 
 *   the function returns an index k between 0 and n-1
 * - if tau is an uninterpreted type, then the function returns an
 *   integer index k
 * 
 * The index k is a unique identifier: if two terms t1 and t2 are not
 * equal in the model mdl, then their values will be distinct indices k.
 *
 * Error codes:
 * - if t does not have a scalar or uninterpreted type:
 *   code = SCALAR_TERM_REQUIRED
 *   term1 = t
 */
__YICES_DLLSPEC__ extern int32_t yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val);


#ifdef __cplusplus
} /* close extern "C" { */
#endif


#endif /* __YICES_H */
