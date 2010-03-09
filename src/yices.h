/*
 * Yices API for constructing terms and types
 */

#ifndef __YICES_H
#define __YICES_H

#ifdef __cplusplus
extern "C" {
#endif


#include <stdint.h>

#include "yices_types.h"
#include "yices_limits.h"



/***************************************
 *  GLOBAL INITIALIZATION AND CLEANUP  *
 **************************************/

/*
 * Must be called before anything else to initialize 
 * internal data structures.
 */
extern void yices_init(void);

/*
 * Free all allocated memory.
 */
extern void yices_cleanup(void);




/*********************
 *  ERROR REPORTING  *
 ********************/

/*
 * Get the last error report
 */
extern error_report_t *yices_get_error_report(void);

/*
 * Clear the error report
 */
extern void yices_clear_error(void);




/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

/*
 * All constructors return NULL_TYPE (-1) if the type definition is wrong.
 */

/*
 * Built-in types bool, int, real.
 */
extern type_t yices_bool_type(void);
extern type_t yices_int_type(void);
extern type_t yices_real_type(void);

/*
 * Bitvectors of given size (number of bits)
 * Requires size > 0
 *
 * If size <= 0, error report is set
 *   code = POS_INT_REQUIRED 
 *   badval = size
 * If size > YICES_MAX_BVSIZE
 *   code = MAX_BVSIZE_EXCEEDED
 *   badval = size
 */
extern type_t yices_bv_type(int32_t size);

/*
 * New scalar type of given cardinality.
 * Requires card > 0
 * 
 * If card <= 0, set error report to
 *   code = POS_INT_REQUIRED
 *   badval = size
 */
extern type_t yices_new_scalar_type(int32_t card);

/*
 * New uninterpreted type. No error report.
 */
extern type_t yices_new_uninterpreted_type(void);

/*
 * Typle type tau[0] x ... x tau[n-1].
 * Requires n>0 and tau[0] ... tau[n-1] to be well defined types.
 *
 * Error report 
 * if n<=0, 
 *   code = POSINT_REQUIRED 
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if tau[i] is not well defined (and tau[0] .. tau[i-1] are)
 *   code = INVALID_TYPE
 *   type1 = tau[i]
 *   index = i
 */
extern type_t yices_tuple_type(int32_t n, type_t tau[]);

/*
 * Function type: dom[0] ... dom[n-1] -> range
 * Requires n>0, and dom[0] ... dom[n-1] and range to be well defined
 *
 * Error report
 * if n<=0,
 *   code = POSINT_REQUIRED
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if range undefined
 *   code = INVALID_TYPE
 *   type1 = range
 *   index = -1
 * if dom[i] is undefined (and dom[0] ... dom[i-1] are)
 *   code = INVALID_TYPE
 *   type1 = dom[i]
 *   index = i
 */
extern type_t yices_function_type(int32_t n, type_t dom[], type_t range);




/***********************
 *  TERM CONSTRUCTORS  *
 **********************/

/*
 * Constructors do type checking and some simplifications.
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
extern term_t yices_true(void);
extern term_t yices_false(void);

/*
 * Constant of type tau and id = index
 * - tau must be a scalar type or an uninterpreted type
 * - index must be non-negative, and if tau is scalar,
 *   index must be less than tau's cardinality.
 *
 * Error report:
 * if tau is undefined
 *   code = INVALID_TYPE
 *   type1 = tau
 *   index = -1
 * if tau is not scalar or uninterpreted,
 *   code = SCALAR_OR_UTYPE_REQUIRED
 *   type1 = tau
 * if the index is negative or too large
 *   code = INVALID_CONSTANT_INDEX
 *   type1 = tau
 *   badval = index
 */
extern term_t yices_constant(type_t tau, int32_t index);

/*
 * Uninterpreted term of type tau
 *
 * Error report:
 * if tau is undefined
 *   code = INVALID_TYPE
 *   type1 = tau
 *   index = -1
 */
extern term_t yices_new_uninterpreted_term(type_t tau);

/*
 * Variable of type tau and id = index (to be used in quantified expressions)
 *
 * Error report:
 * if index is negative
 *   code = NONNEG_INT_REQUIRED
 *   badval = index
 * if tau is undefined
 *   code = INVALID_TYPE
 *   type1 = tau
 *   index = -1
 */
extern term_t yices_variable(type_t tau, int32_t index);

/*
 * Application of an uninterpreted function
 * 
 * Error report:
 * if n <= 0,
 *   code = POSINT_REQUIRED
 *   badval = index
 * if fun or arg[i] is not defined
 *   code = INVALID_TERM
 *   term1 = fun or arg[i]
 *   index = -1 or i
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
 *   index = i
 */
extern term_t yices_application(term_t fun, int32_t n, term_t arg[]);

/*
 * if-then-else
 *
 * Error report:
 * if cond, then_term, or else_term is not a valid term
 *   code = INVALID_TERM
 *   term1 = whichever of cond, then_term, or else_term is invalid
 *   index = -1
 * if cond is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = cond
 *   type1 = bool (expected type)
 *   index = -1
 * if then_term and else_term have incompatible types
 *   code = INCOMPATIBLE_TYPES
 *   term1 = then_term
 *   type1 = term1's type
 *   term2 = else_term
 *   type2 = term2's type
 */
extern term_t yices_ite(term_t cond, term_t then_term, term_t else_term);

/*
 * Equality (= left right)
 * Disequality (/= left right)
 *
 * Error report:
 * if left or right is not a valid term
 *   code = INVALID_TERM
 *   term1 = left or right
 *   index = -1
 * if left and right do not have compatible types
 *   code = INCOMPATIBLE_TYPES
 *   term1 = left
 *   type1 = term1's type
 *   term2 = right
 *   type2 = term2's type
 */
extern term_t yices_eq(term_t left, term_t right);
extern term_t yices_neq(term_t left, term_t right);

/*
 * (or arg[0] ... arg[n-1])
 * (and arg[0] ... arg[n-1])
 *
 * Error report:
 * if n < 0
 *   code = NONNEG_INT_REQUIRED
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if arg[i] is not a valid term
 *   code = INVALID_TERM
 *   term1 = arg[i]
 *   index = i
 * if arg[i] is not boolean
 *   code = TYPE_MISMATCH
 *   term1 = arg[i]
 *   type1 = bool (expected type)
 *   index = i
 */
extern term_t yices_or(int32_t n, term_t arg[]);
extern term_t yices_and(int32_t n, term_t arg[]);

/*
 * (not arg)
 *
 * Error report:
 * if arg is invalid
 *    code = INVALID_TERM
 *    term1 = arg
 *    index = -1
 * if arg is not boolean
 *    code = TYPE_MISMATCH
 *    term1 = arg
 *    type1 = bool (expected type)
 *    index = -1
 */
extern term_t yices_not(term_t arg);

/*
 * (xor left right)
 * (iff left right)
 * (implies left right)
 *
 * Error report:
 * if left or right is invalid
 *    code = INVALID_TERM
 *    term1 = left/right
 *    index = -1
 * if left or right is not boolean
 *    code = TYPE_MIMATCH
 *    term1 = left/right
 *    index = -1
 */
extern term_t yices_xor(term_t left, term_t right);
extern term_t yices_iff(term_t left, term_t right);
extern term_t yices_implies(term_t left, term_t right);


/*
 * Tuple constructor
 *
 * Error report:
 * if n <= 0 
 *   code = POSINT_REQUIRED
 *   badval = n
 * if n > YICES_MAX_ARITY
 *   code = TOO_MANY_ARGUMENTS
 *   badval = n
 * if one arg[i] is invalid
 *   code = INVALID_TERM
 *   term1 = arg[i]
 *   index = i
 */
extern term_t yices_tuple(int32_t n, term_t arg[]);

/*
 * Tuple projection
 *
 * Error report:
 * if index < 0
 *    code = NONNEG_REQUIRED
 *    badval = index
 * if tuple is invalid
 *    code = INVALID_TERM
 *    term1 = tuple
 *    index = -1
 * if tuple does not have a tuple type
 *    code = TUPLE_REQUIRED
 *    term1 = tuple
 * if index >= number of components in tuple
 *    code = INVALID_TUPLE_INDEX
 *    type1 = type of tuple
 *    badval = index
 */
extern term_t yices_select(int32_t index, term_t tuple);

/*
 * Function update
 *
 * Error report:
 * if n <= 0
 *    code = POSINT_REQUIRED
 *    badval = n
 * if fun or new_v, or one of arg[i] is invalid
 *    code = INVALID_TERM
 *    term1 = fun, new_v, or arg[i]
 *    index = -1, or i
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
 *    index = -1
 * if arg[i] has a wrong type for i-th arg of fun
 *    code = TYPE_MISMATCH
 *    term1 = arg[i]
 *    type1 = expected type
 *    index = i
 */
extern term_t yices_update(term_t fun, int32_t n, term_t arg[], term_t new_v);


/*
 * Distinct
 *
 * Error report:
 * if n <= 0
 *    code = POSINT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_ARITY
 *    code = TOO_MANY_ARGUMENTS
 *    badval = n
 * if arg[i] is not a valid term
 *    code = INVALID_TERM
 *    term1 = arg[i]
 *    index = i
 * if two terms arg[i] and arg[j] don't have compatible types
 *    code = INCOMPATIBLE_TYPES
 *    term1 = arg[i]
 *    type1 = term1's type
 *    term2 = arg[j]
 *    type2 = term2's type
 */
extern term_t yices_distinct(int32_t n, term_t arg[]);


/*
 * Tuple update: replace component i of tuple by new_v
 *
 * Error report
 * if i < 0
 *    code = NONNEG_INT_REQUIRED
 *    badval = i
 * if tuple or new_v is invalid
 *    code = INVALID_TERM
 *    term1 = tuple/new_v
 *    index = -1
 * if tuple doesn't have a tuple type
 *    code = TUPLE_REQUIRED
 *    term1 = tuple
 * if i >= number of components in tuple
 *    code = INVALID_TUPLE_INDEX
 *    type1 = tuple's type
 *    badval = i
 * if new_v has a wrong type
 *    code = TYPE_MISMATCH
 *    term1 = new_v
 *    type1 = expected type (i-th component type in tuple)
 *    index = -1
 */
extern term_t yices_tuple_update(term_t tuple, int32_t index, term_t new_v);


/*
 * Quantified terms
 *  (forall (var[0] ... var[n-1]) body)
 *  (exists (var[0] ... var[n-1]) body)
 * 
 * Error report:
 * if n <= 0
 *    code = POSINT_REQUIRED
 *    badval = n
 * if n > YICES_MAX_VARS
 *    code = TOO_MANY_VARS
 *    badval = n
 * if body or one of var[i] is invalid
 *    code = INVALID_TERM
 *    term1 = body or var[i]
 *    index = -1 or i
 * if body is not boolean
 *    code = TYPE_MISMATCH
 *    term1 = body
 *    type1 = bool (expected type)
 *    index = -1
 * if one of var[i] is not a variable
 *    code = VARIABLE_REQUIRED
 *    term1 = var[i]
 *    index = i
 * if one variable occurs twice in var
 *    code = DUPLICATE_VARIABLE
 *    term1 = var[i]
 *    index = i
 */
extern term_t yices_forall(int32_t n, term_t var[], term_t body);
extern term_t yices_exists(int32_t n, term_t var[], term_t body);






/**********************************
 *  ARITHMETIC TERM CONSTRUCTORS  *
 *********************************/

/*
 * RATIONAL CONSTANTS
 * - the functions below return a pointer to an internal buffer
 *   that stores a rational constant. 
 * - they return NULL if an error occurs.
 *
 * WARNING: there is only one internal rational buffer. 
 * It's reused on every call to one of these functions.
 *
 * The constant can be converted to a term using function
 * yices_arith_constant.
 */

/*
 * Integer constants
 */
extern rational_t *yices_int32(int32_t val);
extern rational_t *yices_int64(int64_t val);

/*
 * Rational constants
 * - den must be non-zero
 * - common factors are removed
 * If den=0, the result is NULL.
 */
extern rational_t *yices_rat32(int32_t num, uint32_t den);
extern rational_t *yices_rat64(int64_t num, uint64_t den);

/*
 * Convert a string to a rational. The string format is
 *     <optional_sign> <numerator>/<denominator>
 *  or <optional_sign> <numerator>
 *
 * where <optional_sign> is + or - or nothing
 * <numerator> and <denominator> are sequences of 
 * decimal digits.
 *
 * If the format is wrong, the result is NULL.
 */
extern rational_t *yices_string_rational(char *s);

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
 * If the format is wrong, the result is NULL.
 */
extern rational_t *yices_string_float(char *s);

/*
 * Constant initialized via GMP integers or rationals.
 * - q must be canonicalized
 */
#ifdef __GMP_H__
extern rational_t *yices_mpz(mpz_t z);
extern rational_t *yices_mpq(mpq_t q);
#endif




/*
 * ARITHMETIC CONSTANTS
 */

/*
 * Convert rational_t a to a term.
 * - a must be the pointer returned by one of the functions above
 * - a must be non-null
 */
extern term_t yices_arith_constant(rational_t *a);



/*
 * POLYNOMIALS
 */

/*
 * All operations return NULL_TERM if there's an error (NULL_TERM = -1)
 *
 * Error reports:
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 *   index = -1
 * if t1 or t2 is not an arithmetic term
 *   code = ARITHTERM_REQUIRED
 *   term1 = t1 or t2
 *   index = -1
 *
 * for yices_mul and yices_square, if the result's degree
 * is too large, then the error report is
 *   code = DEGREE_OVERFLOW
 */
extern term_t yices_add(term_t t1, term_t t2);     // t1 + t2
extern term_t yices_sub(term_t t1, term_t t2);     // t1 - t2
extern term_t yices_neg(term_t t1);                // -t1
extern term_t yices_mul(term_t t1, term_t t2);     // t1 * t2
extern term_t yices_square(term_t t1);             // t1 * t1



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
 *   index = -1
 * if t1 or t2 is not an arithmetic term
 *   code = ARITHTERM_REQUIRED
 *   term1 = t1 or t2
 *   index = -1
 */
extern term_t yices_aritheq_atom(term_t t1, term_t t2);  // t1 == t2
extern term_t yices_arithneq_atom(term_t t1, term_t t2); // t1 != t2

extern term_t yices_arithgeq_atom(term_t t1, term_t t2);  // t1 >= t2
extern term_t yices_arithleq_atom(term_t t1, term_t t2);  // t1 <= t2
extern term_t yices_arithgt_atom(term_t t1, term_t t2);   // t1 > t2
extern term_t yices_arithlt_atom(term_t t1, term_t t2);   // t1 < t2






/*********************************
 *  BITVECTOR TERM CONSTRUCTORS  *
 ********************************/

/*
 * BITVECTOR CONSTANTS
 *
 * The functions below return a pointer to an internal buffer that
 * stores a bitvector constant (or they return NULL if there's an error).
 * The bitvector constant can be converted to a term using
 * yices_bvconstant.
 */

/*
 * Conversion of an integer to a bitvector constant.
 * - n = number of bits
 * - x = value
 * The value x is truncated (or 0-padded) to n bits
 * The low-order bit of x is bit 0 of the constant.
 * n must be positive, otherwise the functions return NULL.
 */
extern bvconstant_t *yices_bvconst_uint32(int32_t n, uint32_t x);
extern bvconstant_t *yices_bvconst_uint64(int32_t n, uint64_t x);

#ifdef __GMP_H__
extern bvconstant_t *yices_bvconst_mpz(int32_t n, mpz_t x);
#endif


/*
 * Parsing from a string of characters '0' and '1'
 * First character = high order bit
 * Last character = low-order bit
 * The constant has n bits if the strings has n characters.
 *
 * Return NULL if the string does not have the right format
 * (including if the string is empty).
 */
extern bvconstant_t *yices_bvconst_from_string(char *s);

/*
 * Parsing from a hexadecimal string
 * - First character = 4 high order bits 
 * - Last character = 4 low-order bits
 * The constant has 4n bits if s has n characters.
 *
 * Return NULL if the string does not have the right format
 * (including if the string is empty).
 */
extern bvconstant_t *yices_bvconst_form_hexa_string(char *s);

/*
 * Construction from an integer array
 * bit i of the constant is 0 if a[i] == 0
 * bit i of the constant is 1 if a[i] != 0
 *
 * Return NULL if n <= 0
 */
extern bvconstant_t *yices_bvconst_from_array(int32_t n, int32_t a[]);

/*
 * bvconst_zero: set all bits to 0
 * bvconst_one: set low-order bit to 1, all the others to 0
 * bvconst_minus_one: set all bits to 1
 *
 * Return NULL if n <= 0
 */
extern bvconstant_t *yices_bvconst_zero(int32_t n);
extern bvconstant_t *yices_bvconst_one(int32_t n);
extern bvconstant_t *yices_bvconst_minus_one(int32_t n);



/*
 * Convert bvconstant_t a to a term
 * - a must be the pointer returned by one of the functions above
 * - a must be non-null
 */
extern term_t yices_bvconstant(bvconstant_t *a);




/*
 * BIT-VECTOR TERMS
 */

/*
 * Binary operations: both arguments must be bitvector terms of the same size.
 * The functions return NULL_TERM (-1) if there's an error.
 *
 * Error reports
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 *   index = -1
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
 * for bvmul or bvsquare, if the degree is too large
 *   code = DEGREE_OVERFLOW
 */
extern term_t yices_bvadd(term_t t1, term_t t2);   // addition (t1 + t2
extern term_t yices_bvsub(term_t t1, term_t t2);   // subtraction (t1 - t2)
extern term_t yices_bvneg(term_t t1);              // negation (- t1)
extern term_t yices_bvmul(term_t t1, term_t t2);   // multiplication (t1 * t2)
extern term_t yices_bvsquare(term_t t1);           // square (t1 * t1)

extern term_t yices_bvdiv(term_t t1, term_t t2);   // unsigned div
extern term_t yices_bvrem(term_t t1, term_t t2);   // unsigned rem
extern term_t yices_bvsdiv(term_t t1, term_t t2);  // signed div
extern term_t yices_bvsrem(term_t t1, term_t t2);  // signed rem
extern term_t yices_bvsmod(term_t t1, term_t t2);  // signed mod

extern term_t yices_bvnot(term_t t1);              // bitwise not
extern term_t yices_bvand(term_t t1, term_t t2);   // bitwise and
extern term_t yices_bvor(term_t t1, term_t t2);    // bitwise or
extern term_t yices_bvxor(term_t t1, term_t t2);   // bitwise exclusive or
extern term_t yices_bvnand(term_t t1, term_t t2);  // bitwise not and
extern term_t yices_bvnor(term_t t1, term_t t2);   // bitwise not or
extern term_t yices_bvxnor(term_t t1, term_t t2);  // bitwise not xor

extern term_t yices_bvshl(term_t t1, term_t t2);   // shift t1 left by k bits where k = value of t2
extern term_t yices_bvlshr(term_t t1, term_t t2);  // logical shift t1 right by k bits, where k = value of t2
extern term_t yices_bvashr(term_t t1, term_t t2);  // arithmetic shift t1 right by k bits, k = value of t2



/*
 * Shift or rotation by an integer constant n
 * - shift_left0 sets the low-order bits to zero
 * - shift_left1 sets the low-order bits to one
 * - shift_rigth0 sets the high-order bits to zero
 * - shift_right1 sets the high-order bits to one
 * - ashift_right is arithmetic shift, it copies the sign bit &
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
 * if n < 0
 *   code = NONNEG_INT_REQUIRED
 *   badval = n
 * if n > size of t
 *   code = INVALID_BITSHIFT
 *   badval = n
 */
extern term_t yices_shift_left0(term_t t, int32_t n);
extern term_t yices_shift_left1(term_t t, int32_t n);
extern term_t yices_shift_right0(term_t t, int32_t n);
extern term_t yices_shift_right1(term_t t, int32_t n);
extern term_t yices_ashift_right(term_t t, int32_t n);
extern term_t yices_rotate_left(term_t t, int32_t n);
extern term_t yices_rotate_right(term_t t, int32_t n);


/*
 * Extract a subvector of t
 * - t must be a bitvector term of size m
 * - i and j must satisfy 0 <= i <= j <= m-1
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
 * if 0 <= i <= j <= m-1 does not hold
 *   code = INVALID_BVEXTRACT
 */
extern term_t yices_bvextract(term_t t, int32_t i, int32_t j);


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
extern term_t yices_bvconcat(term_t t1, term_t t2);


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
 * if n <= 0
 *   code = POSINT_REQUIRED
 *   badval = n
 */
extern term_t yices_bvrepeat(term_t t, int32_t n);


/*
 * Sign extension
 * - add n copies of t's sign bit
 * - n must be non-negative
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
 * if n < 0,
 *   code = NONNEG_INT_REQUIRED
 *   badval = n
 */
extern term_t yices_sign_extend(term_t t, int32_t n);


/*
 * Zero extension
 * - add n zeros to t
 * - n must be non-negative
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
 * if n < 0,
 *   code = NONNEG_INT_REQUIRED
 *   badval = n
 */
extern term_t yices_zero_extend(term_t t, int32_t n);



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
 *   code = BITVECOTR_REQUIRED
 *   term1 = t
 */
extern term_t yices_redand(term_t t);
extern term_t yices_redor(term_t t); 


/*
 * Bitwise equality comparison: if t1 and t2 are bitvectors of size n,
 * construct (bvand (bvxnor t1 t2))
 *
 * Return NULL_TERM if there's an error
 *
 * Error reports:
 * if t1 or t2 is not valid
 *   code = INVALID_TERM
 *   term1 = t1 or t2
 *   index = -1
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
extern term_t yices_redcomp(term_t t1, term_t t2);




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
 *   index = -1
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
extern term_t yices_bveq_atom(term_t t1, term_t t2);
extern term_t yices_bvneq_atom(term_t t1, term_t t2);

/*
 * Unsigned inequalities
 */
extern term_t yices_bvge_atom(term_t t1, term_t t2);  // t1 >= t2
extern term_t yices_bvgt_atom(term_t t1, term_t t2);  // t1 > t2
extern term_t yices_bvle_atom(term_t t1, term_t t2);  // t1 <= t2
extern term_t yices_bvlt_atom(term_t t1, term_t t2);  // t1 < t2


/*
 * Signed inequalities
 */
extern term_t yices_bvsge_atom(term_t t1, term_t t2);  // t1 >= t2
extern term_t yices_bvsgt_atom(term_t t1, term_t t2);  // t1 > t2
extern term_t yices_bvsle_atom(term_t t1, term_t t2);  // t1 <= t2
extern term_t yices_bvslt_atom(term_t t1, term_t t2);  // t1 < t2




/**************************
 *  SOME CHECKS ON TERMS  *
 *************************/

/*
 * Get the type of term t
 * return NULL_TYPE if t is not a valid term
 * and set the error report:
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 */
extern type_t yices_type_of_term(term_t t);


/*
 * Check the type of a term t:
 * - term_is_arithmetic check whether t's type is either int or real
 * - term_is_real check whether t's type is real (return false if t's type is int)
 * - term_is_int check whether t's type is int 
 * If t is not a valid term, the check functions return false
 * and set the error report as above.
 */
extern bool yices_term_is_bool(term_t t);
extern bool yices_term_is_int(term_t t);
extern bool yices_term_is_real(term_t t);
extern bool yices_term_is_arithmetic(term_t t);
extern bool yices_term_is_bitvector(term_t t);
extern bool yices_term_is_tuple(term_t t);
extern bool yices_term_is_function(term_t t);


/*
 * Size of a bitvector term (i.e., number of bits)
 * - return -1 if there's an error
 *
 * Error report:
 * if t is not a valid term
 *    code = INVALID_TERM
 *    term1 = t
 *    index = -1
 * if t is not a bitvector term
 *    code = BITVECTOR_REQUIRED
 *    term1 = t
 */
extern int32_t yices_term_bitsize(term_t t);




/************
 *  NAMES   *
 ***********/

/*
 * The following functions attach a name to a type or a term
 * The name spaces for types and terms are disjoint.
 * names must be '\0' terminated strings.
 *
 * The functions return -1 and set the error report if the term or
 * type is invalid . Otherwise they return 0.
 *
 * A copy of string name is made internally.
 */
extern int32_t yices_set_type_name(type_t tau, char *name);
extern int32_t yices_set_term_name(term_t t, char *name);

/*
 * Remove mapping from name to type or term
 * - no effect if name is not assigned to a term or type
 */
extern void yices_remove_type_name(char *name);
extern void yices_remove_term_name(char *name);

/*
 * Get type or term of the given name
 * - return NULL_TYPE or NULL_TERM if there's no type or term with that name
 */
extern type_t yices_get_type_by_name(char *name);
extern term_t yices_get_term_by_name(char *name);







/***************
 *  CONTEXTS   *
 **************/

/*
 * A context is defined by a set of solvers (which determines
 * the logic supported by the context). This is where formulas
 * are asserted.
 */







/************************
 *  ARITHMETIC BUFFERS  *
 ***********************/

/*
 * An arith_buffer object is an auxiliary structure for building
 * polynomials (or linear arithmetic expressions). Using buffers may
 * be more efficient than direct term constructions as it avoids
 * creating unnecessary intermediate terms.
 *
 * The construction is as follows:
 * 1) allocate a new buffer by calling yices_new_arith_buffer
 * 2) apply buffer operations to construct a polynomial expression
 *    inside the buffer
 * 3) when done, convert the buffer to a term or an atom via the 
 *    functions
 *     yices_arith_term
 *     yices_arith_eq0_atom
 *     yices_arith_geq0_atom, etc.
 * 4) free the buffer or reset it and go back to step 2
 *
 */


/*
 * BUFFER ALLOCATION
 */

/*
 * Allocate an arithmetic buffer.
 * The buffer is initialized to the zero polynomial.
 */
extern arith_buffer_t *yices_new_arith_buffer(void);

/*
 * Free an allocated buffer
 */
extern void yices_free_arith_buffer(arith_buffer_t *b);

/*
 * Reset: set buffer to zero.
 */
extern void yices_arith_reset(arith_buffer_t *b);




/*
 * POLYNOMIAL CONSTRUCTION
 */

/*
 * Linear operations
 */
extern void yices_arith_negate(arith_buffer_t *b);
extern void yices_arith_add_const(arith_buffer_t *b, rational_t *a);
extern void yices_arith_sub_const(arith_buffer_t *b, rational_t *a);
extern void yices_arith_mul_const(arith_buffer_t *b, rational_t *a);
extern void yices_arith_add_buffer(arith_buffer_t *b, arith_buffer_t *b1);
extern void yices_arith_sub_buffer(arith_buffer_t *b, arith_buffer_t *b1);
extern void yices_arith_add_const_times_buffer(arith_buffer_t *b, rational_t *a, arith_buffer_t *b1);
extern void yices_arith_sub_const_times_buffer(arith_buffer_t *b, rational_t *a, arith_buffer_t *b1);


/*
 * Linear operations involving terms:
 * - return -1 if the term is not well defined or if it does not have
 *   integer or real type.
 * - return 0 if the operation succeeds
 *
 * Error report
 * if t is not well defined
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 * if t has a bad type
 *   code = ARITHTERM_REQUIRED
 *   term1 = t
 */
extern int32_t yices_arith_add_term(arith_buffer_t *b, term_t t);
extern int32_t yices_arith_sub_term(arith_buffer_t *b, term_t t);
extern int32_t yices_arith_add_const_times_term(arith_buffer_t *b, rational_t *a, term_t t);
extern int32_t yices_arith_sub_const_times_term(arith_buffer_t *b, rational_t *a, term_t t);


/*
 * Non-linear operations:
 * - return -1 if the operation failed (either because the terms are incorrect)
 *   or because there's an overflow in the polynomial degree.
 * - return 0 otherwise
 */
extern int32_t yices_arith_mul_buffer(arith_buffer_t *b, arith_buffer_t *b1);
extern int32_t yices_arith_mul_term(arith_buffer_t *b, term_t t);
extern int32_t yices_arith_square(arith_buffer_t *b);



/*
 * CONVERSION TO ARITHMETIC TERMS AND ATOMS
 */

/*
 * All these operations construct a term from arithmetic buffer b.
 * - the content of b is invalid after these operations
 * - so b must be reset before it's used again
 */
extern term_t yices_arith_term(arith_buffer_t *b);

extern term_t yices_arith_eq0_atom(arith_buffer_t *b);    // b == 0
extern term_t yices_arith_neq0_atom(arith_buffer_t *b);   // b != 0
extern term_t yices_arith_geq0_atom(arith_buffer_t *b);   // b >= 0
extern term_t yices_arith_leq0_atom(arith_buffer_t *b);   // b <= 0
extern term_t yices_arith_gt0_atom(arith_buffer_t *b);    // b > 0
extern term_t yices_arith_lt0_atom(arith_buffer_t *b);    // b < 0







/********************************** 
 *  BITVECTOR ARITHMETIC BUFFERS  *
 *********************************/

/*
 * A bvarith_buffer object is an auxiliary data structure for 
 * building bit-vector polynomials.
 *
 * Usage:
 * 1) allocate a buffer
 * 2) apply buffer operations to construct a polynomial
 * 3) convert the buffer to a term
 * 4) free the buffer, or reset it and go back to 2
 */

/*
 * Allocate a bvarith_buffer: it's initially set to the bitvector 
 * constant 0b0000....0 of n bits.
 * return NULL if n <= 0.
 */
extern bvarith_buffer_t *yices_new_bvarith_buffer(int32_t n);

/*
 * Free an allocated buffer
 */
extern void yices_free_bvarith_buffer(bvarith_buffer_t *b);

/*
 * Reset: reset buffer's value to 0b000...0 with n bits
 * No effect if n <= 0.
 */
extern void yices_bvarith_reset(bvarith_buffer_t *b, int32_t n);



/*
 * ASSIGNMENTS
 */

/*
 * Assignment: copy a constant into b.
 * - set b's bitsize to that of c
 */
extern void yices_bvarith_set_const(bvarith_buffer_t *b, bvconstant_t *c);

/*
 * Copy another buffer into b: b's size is adjusted.
 * no effect if b1 == b
 */
extern void yices_bvarith_set_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);

/*
 * Assignment: copy term t into b.
 * Return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if t is invalid
 *    code = INVALID_TERM
 *    term1 = t
 *    index = -1
 * if t does not have bitvector type
 *    code = BITVECTOR_REQUIRED
 *    term1 = t
 */
extern int32_t yices_bvarith_set_term(bvarith_buffer_t *b, term_t t);


/*
 * POLYNOMIAL CONSTRUCTION
 */

/*
 * Arithmetic operations:
 * - return -1 if there's an error, 0 otherwise.
 *
 * Error report:
 * if buffer and arguments do not have the same size
 *   code = INCOMPATIBLE_BVSIZES
 *   badval = size of argument
 * if term t is not well defined
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 * if degree is too large (in mul operations)
 *   code = DEGREE_OVERFLOW
 */
extern int32_t yices_bvarith_add_const(bvarith_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvarith_sub_const(bvarith_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvarith_mul_const(bvarith_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvarith_add_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);
extern int32_t yices_bvarith_sub_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);
extern int32_t yices_bvarith_mul_buffer(bvarith_buffer_t *b, bvarith_buffer_t *b1);
extern int32_t yices_bvarith_add_term(bvarith_buffer_t *b, term_t t);
extern int32_t yices_bvarith_sub_term(bvarith_buffer_t *b, term_t t);
extern int32_t yices_bvarith_mul_term(bvarith_buffer_t *b, term_t t);
extern int32_t yices_bvarith_square(bvarith_buffer_t *b);

extern void yices_bvarith_negate(bvarith_buffer_t *b); // no error 


/*
 * Convert bvarith buffer b to a term
 */
extern term_t yices_bvarith_term(bvarith_buffer_t *b);




/*****************************
 *  BITVECTOR LOGIC BUFFERS  *
 ****************************/

/*
 * A bvlogic_buffer is a auxiliary data structure for building
 * "logical" bitvector expression. This can be any expression
 * built using bitwise and, or, etc. and the structural operations
 * concat, extract, shift, etc.
 *
 * Usage:
 * 1) allocate a buffer
 * 2) apply operation to construct a bitvector expression
 * 3) convert the biffer to a term
 * 4) free the buffer or reset it and go back to step 2
 */

/*
 * Allocate a bvlogic_buffer. It's initally set to the empty bitvector
 */
extern bvlogic_buffer_t *yices_new_bvlogic_buffer(void);

/*
 * Free an allocated logic buffer
 */
extern void yices_free_bvlogic_buffer(bvlogic_buffer_t *b);

/*
 * Reset to the empty vector
 */
extern void yices_bvlogic_reset(bvlogic_buffer_t *b);



/*
 * ASSIGNMENTS
 */

/*
 * Assignment: copy a constant into b
 */
extern void yices_bvlogic_set_const(bvlogic_buffer_t *b, bvconstant_t *c);

/*
 * Assignment: copy another buffer into b
 * (no effect if b1 == b)
 */
extern void yices_bvlogic_set_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);

/*
 * Assignment: copy term t into b.
 * Return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if t is invalid
 *    code = INVALID_TERM
 *    term1 = t
 *    index = -1
 * if t does not have bitvector type
 *    code = BITVECTOR_REQUIRED
 *    term1 = t
 */
extern int32_t yices_bvlogic_set_term(bvlogic_buffer_t *b, term_t t);


/*
 * OPERATIONS
 */

/*
 * Bitwise not 
 */
extern void yices_bvlogic_not(bvlogic_buffer_t *b);


/*
 * Bitwise operations between a buffer and a constant.
 * return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if c does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    badval = c's bitsize
 */
extern int32_t yices_bvlogic_and_const(bvlogic_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvlogic_or_const(bvlogic_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvlogic_xor_const(bvlogic_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvlogic_nand_const(bvlogic_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvlogic_nor_const(bvlogic_buffer_t *b, bvconstant_t *c);
extern int32_t yices_bvlogic_xnor_const(bvlogic_buffer_t *b, bvconstant_t *c);


/*
 * Bitwise operation with another buffer.
 * Return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if b1 does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    badval = b1's bitsize
 */
extern int32_t yices_bvlogic_and_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);
extern int32_t yices_bvlogic_or_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);
extern int32_t yices_bvlogic_xor_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);
extern int32_t yices_bvlogic_nand_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);
extern int32_t yices_bvlogic_nor_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);
extern int32_t yices_bvlogic_xnor_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);


/*
 * Bitwise operations with a term t.
 * Return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if t is invalid
 *    code = INVALID_TERM
 *    term1 = t
 *    index = -1
 * if t does not have bitvector type
 *    code = BITVECTOR_REQUIRED
 *    term1 = t
 * if t does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    badval = t's bitsize
 */
extern int32_t yices_bvlogic_and_term(bvlogic_buffer_t *b, term_t t);
extern int32_t yices_bvlogic_or_term(bvlogic_buffer_t *b, term_t t);
extern int32_t yices_bvlogic_xor_term(bvlogic_buffer_t *b, term_t t);
extern int32_t yices_bvlogic_nand_term(bvlogic_buffer_t *b, term_t t);
extern int32_t yices_bvlogic_nor_term(bvlogic_buffer_t *b, term_t t);
extern int32_t yices_bvlogic_xnor_term(bvlogic_buffer_t *b, term_t t);


/*
 * Bitwise operations with n terms arg[0...n-1]
 * Return -1 if there's an errror, 0 otherwise.
 *
 * Error report:
 * if arg[i] is invalid
 *    code = INVALID_TERM
 *    term1 = arg[i]
 *    index = i
 * if arg[i] does not have bitvector type
 *    code = BITVECTOR_REQUIRED
 *    term1 = arg[i]
 *    index = i
 * if arg[i] does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    term1 = arg[i]
 *    index = i
 *    badval = arg[i]'s bitsize
 */
extern int32_t yices_bvlogic_and_terms(bvlogic_buffer_t *b, int32_t n, term_t arg[]);
extern int32_t yices_bvlogic_or_terms(bvlogic_buffer_t *b, int32_t n, term_t arg[]);
extern int32_t yices_bvlogic_xor_terms(bvlogic_buffer_t *b, int32_t n, term_t arg[]);
extern int32_t yices_bvlogic_nand_terms(bvlogic_buffer_t *b, int32_t n, term_t arg[]);
extern int32_t yices_bvlogic_nor_terms(bvlogic_buffer_t *b, int32_t n, term_t arg[]);
extern int32_t yices_bvlogic_xnor_terms(bvlogic_buffer_t *b, int32_t n, term_t arg[]);



/*
 * Shift by n bits:
 * - shift_left0 sets the low-order bits to zero
 * - shift_left1 sets the low-order bits to one
 * - shift_rigth0 sets the high-order bits to zero
 * - shift_right1 sets the high-order bits to one
 * - ashift_right is arithmetic shift, it copies the sign bit
 *
 * If b is a vector of m bits, then n must satisfy 0 <= n <= m.
 * Return -1 if n is negative or larger than m, 0 otherwise.
 *
 * Error reports:
 * if n < 0
 *   code = NONNEG_INT_REQUIRED
 *   badval = n
 * if n > m
 *   code = INVALID_BITSHIFT
 *   badval = n
 */
extern int32_t yices_bvlogic_shift_left0(bvlogic_buffer_t *b, int32_t n);
extern int32_t yices_bvlogic_shift_left1(bvlogic_buffer_t *b, int32_t n);
extern int32_t yices_bvlogic_shift_right0(bvlogic_buffer_t *b, int32_t n);
extern int32_t yices_bvlogic_shift_right1(bvlogic_buffer_t *b, int32_t n);
extern int32_t yices_bvlogic_ashift_right(bvlogic_buffer_t *b, int32_t n);


/*
 * Rotation by n bits: 
 * left/right refer to b written in big-endian form, 
 * as m bits b[m-1] ... b[0]
 * - rotate_left gives   b[m-n-1] ... b[0] b[m-1] ... b[m-n]
 * - rotate_right gives   b[n-1] ...b[0] b[m-1] ... b[n]
 *
 * n must satisfy 0 <= n <= m
 * Return -1 if n is negative or larger than m, 0 otherwise.
 * 
 * Same error reports as shift operations.
 */
extern int32_t yices_bvlogic_rotate_left(bvlogic_buffer_t *b, int32_t n);
extern int32_t yices_bvlogic_rotate_right(bvlogic_buffer_t *b, int32_t n);



/*
 * Extract subvector b[j] ... b[i] of b[m-1] ... b[0]
 * - i and j must satisfy 0 <= i <= j <= m-1
 *
 * Error report:
 * if 0 <= i <= j <= m-1 does not hold
 *    code = INVALID_BVEXTRACT
 */
extern int32_t yices_bvlogic_extract(bvlogic_buffer_t *b, int32_t i, int32_t j);


/*
 * Concatenation: if b is b[m-1] ... b[0] then 
 * - concat_left adds bits to the left of b[m-1]: low-order bits of the result
 * are from b, high-order bits are from the argument c, b1, or t.
 * - concat_right adds bits to the right of b[0]: high-order bits of the result
 * are from b, low-order bits are from the argument c, b1, or t.
 *
 * For concatenation with a term t:
 * Return -1 on error, 0 otherwise.
 *
 * Error report:
 * if t is not a valid term
 *   code = INVALID_TERM
 *   term1 = t
 *   index = -1
 * if t is not a bitvector term
 *   code = BITVECTOR_REQUIRED
 *   term1 = t
 */
extern void yices_bvlogic_concat_left_const(bvlogic_buffer_t *b, bvconstant_t *c); 
extern void yices_bvlogic_concat_right_const(bvlogic_buffer_t *b, bvconstant_t *c); 
extern void yices_bvlogic_concat_left_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);
extern void yices_bvlogic_concat_right_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);

extern int32_t yices_bvlogic_concat_left_term(bvlogic_buffer_t *b, term_t t);
extern int32_t yices_bvlogic_concat_right_term(bvlogic_buffer_t *b, term_t t);


/*
 * Repeat: make n copies of b
 * n must be positive
 *
 * Return -1 if n is not positive, 0 otherwise
 * Error report
 *   code = POSINT_REQUIRED
 *   badval = n
 */
extern int32_t yices_bvlogic_repeat(bvlogic_buffer_t *b, int32_t n);


/*
 * Sign-extension:
 * if b is b[m-1] ... b[0] then copy the sign bit b[m-1] n times to the left of b[m-1] 
 * returns -1 if m == 0 or n < 0, returns 0 otherwise
 *
 * Error report:
 *   code = INVALID_BVSIGNEXTEND
 */
extern int32_t yices_bvlogic_sign_extend(bvlogic_buffer_t *b, int32_t n);

/*
 * Zero-extension
 * if b is b[m-1] ... b[0] then copy bit 0 n  times to the left of b[m-1] 
 * returns -1 if m == 0 or n < 0, returns 0 otherwise
 *
 * Error report:
 *   code = INVALID_BVZEROEXTEND
 */
extern int32_t yices_bvlogic_zero_extend(bvlogic_buffer_t *b, int32_t n);



/*
 * And-reduction:
 * - if b is b[m-1] ... b[0] then compute (and b[0] ... b[m-1]) and store that in b[0]
 * - return -1 if m == 0, return 0 otherwise
 *
 * Error report:
 *   code = EMPTY_BITVECTOR if m == 0
 */
extern int32_t yices_bvlogic_redand(bvlogic_buffer_t *b);


/*
 * Or-reduction
 * - if b is b[m-1] ... b[0] then compute (and b[0] ... b[m-1]) and store that in b[0]
 * - return -1 if m == 0, return 0 otherwise
 *
 * Error report:
 *   code = EMPTY_BITVECTOR if m == 0
 */
extern int32_t yices_bvlogic_redor(bvlogic_buffer_t *b);



/*
 * BITWISE COMPARISON
 */

/*
 * Bitwise comparison with a constant.
 * Store (and (eq b[0] c[0]) ... (eq b[m-1] c[m-1])) into b[0]
 * - return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if c does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    badval = c's bitsize
 */
extern int32_t yices_bvlogic_comp_const(bvlogic_buffer_t *b, bvconstant_t *c);


/*
 * Bitwise comparison with another buffer
 * Return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if b1 does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    badval = b1's bitsize
 */
extern int32_t yices_bvlogic_comp_buffer(bvlogic_buffer_t *b, bvlogic_buffer_t *b1);


/*
 * Bitwise comparison with a bitvector term t
 * Return -1 if there's an error, 0 otherwise
 *
 * Error report:
 * if t is invalid
 *    code = INVALID_TERM
 *    term1 = t
 *    index = -1
 * if t does not have bitvector type
 *    code = BITVECTOR_REQUIRED
 *    term1 = t
 * if t does not have the same bitsize as b
 *    code = INCOMPATIBLE_BVSIZES
 *    badval = t's bitsize
 */
extern int32_t yices_bvlogic_comp_term(bvlogic_buffer_t *b, term_t t);



/*
 * Convert buffer to a term
 * Return NULL_TERM if b is empty
 * 
 * Error report
 *   code = EMPTY_BITVECTOR
 */
extern term_t yices_bvlogic_term(bvlogic_buffer_t *b);




#ifdef __cplusplus
} /* close extern "C" { */
#endif


#endif /* __YICES_H */
