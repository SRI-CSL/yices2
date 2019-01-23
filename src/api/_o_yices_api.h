/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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
 *
 * Lock free versions of the delicate yices_api.c calls, (implemented in yices_api.c)
 * The prefix _o_ is intended to mean that the global lock must be OWNED by the caller.
 */

#ifndef ___O_YICES_API_H
#define ___O_YICES_API_H

#include <stdio.h>

/*
 * LOCK FREE VERSIONS OF YICES_API CALLS
 */


/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

static type_t _o_yices_bool_type(void);

static type_t _o_yices_int_type(void);

static type_t _o_yices_real_type(void);

static type_t _o_yices_bv_type(uint32_t size);

static type_t _o_yices_new_uninterpreted_type(void);

static type_t _o_yices_new_scalar_type(uint32_t card);

static type_t _o_yices_tuple_type(uint32_t n, const type_t elem[]);

static type_t _o_yices_function_type(uint32_t n, const type_t dom[], type_t range);


/***********************
 *  TERM CONSTRUCTORS  *
 **********************/


static term_t _o_yices_constant(type_t tau, int32_t index);

static term_t _o_yices_new_uninterpreted_term(type_t tau);

static term_t _o_yices_new_variable(type_t tau);

static term_t _o_yices_application(term_t fun, uint32_t n, const term_t arg[]);

static term_t _o_yices_ite(term_t cond, term_t then_term, term_t else_term);

static term_t _o_yices_eq(term_t left, term_t right);

static term_t _o_yices_neq(term_t left, term_t right);

static term_t _o_yices_not(term_t arg);

static term_t _o_yices_or(uint32_t n, term_t arg[]);

static term_t _o_yices_and(uint32_t n, term_t arg[]);

static term_t _o_yices_xor(uint32_t n, term_t arg[]);

static term_t _o_yices_or2(term_t left, term_t right);

static term_t _o_yices_and2(term_t left, term_t right);

static term_t _o_yices_xor2(term_t left, term_t right);

static term_t _o_yices_iff(term_t left, term_t right);

static term_t _o_yices_implies(term_t left, term_t right);

static term_t _o_yices_tuple(uint32_t n, const term_t arg[]);

static term_t _o_yices_select(uint32_t index, term_t tuple);

static term_t _o_yices_update(term_t fun, uint32_t n, const term_t arg[], term_t new_v);
  
static term_t _o_yices_distinct(uint32_t n, term_t arg[]);

static term_t _o_yices_tuple_update(term_t tuple, uint32_t index, term_t new_v);

static term_t _o_yices_forall(uint32_t n, term_t var[], term_t body);

static term_t _o_yices_exists(uint32_t n, term_t var[], term_t body);

static term_t _o_yices_lambda(uint32_t n, const term_t var[], term_t body);

/*************************
 *  RATIONAL CONSTANTS   *
 ************************/

static term_t _o_yices_int32(int32_t val);

static term_t _o_yices_int64(int64_t val);

static term_t _o_yices_rational32(int32_t num, uint32_t den);

static term_t _o_yices_rational64(int64_t num, uint64_t den);

static term_t _o_yices_mpz(const mpz_t z);

static term_t _o_yices_mpq(const mpq_t q);

static term_t _o_yices_parse_rational(const char *s);

static term_t _o_yices_parse_float(const char *s);

/***************************
 *  ARITHMETIC OPERATIONS  *
 **************************/

static term_t _o_yices_add(term_t t1, term_t t2);

static term_t _o_yices_sub(term_t t1, term_t t2);

static term_t _o_yices_neg(term_t t1);

static term_t _o_yices_mul(term_t t1, term_t t2);

static term_t _o_yices_square(term_t t1);

static term_t _o_yices_power(term_t t1, uint32_t d);

static term_t _o_yices_sum(uint32_t n, const term_t t[]);

static term_t _o_yices_product(uint32_t n, const term_t t[]);

static term_t _o_yices_division(term_t t1, term_t t2);

/***************************
 *  DIV/MOD AND RELATIVES  *
 **************************/

static term_t _o_yices_idiv(term_t t1, term_t t2);

static term_t _o_yices_imod(term_t t1, term_t t2);

static term_t _o_yices_divides_atom(term_t t1, term_t t2);

static term_t _o_yices_is_int_atom(term_t t);

static term_t _o_yices_abs(term_t t);

static term_t _o_yices_floor(term_t t);

static term_t _o_yices_ceil(term_t t);


/*******************
 *   POLYNOMIALS   *
 ******************/

static term_t _o_yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[]);

static term_t _o_yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[]);

static term_t _o_yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[]);

static term_t _o_yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[]);

static term_t _o_yices_poly_mpz(uint32_t n, const mpz_t z[], const term_t t[]);

static term_t _o_yices_poly_mpq(uint32_t n, const mpq_t q[], const term_t t[]);


/**********************
 *  ARITHMETIC ATOMS  *
 *********************/

static term_t _o_yices_arith_eq_atom(term_t t1, term_t t2);

static term_t _o_yices_arith_neq_atom(term_t t1, term_t t2);

static term_t _o_yices_arith_geq_atom(term_t t1, term_t t2);

static term_t _o_yices_arith_lt_atom(term_t t1, term_t t2);

static term_t _o_yices_arith_gt_atom(term_t t1, term_t t2);

static term_t _o_yices_arith_leq_atom(term_t t1, term_t t2);

static term_t _o_yices_arith_eq0_atom(term_t t);

static term_t _o_yices_arith_neq0_atom(term_t t);
  
static term_t _o_yices_arith_geq0_atom(term_t t);

static term_t _o_yices_arith_leq0_atom(term_t t);

static term_t _o_yices_arith_gt0_atom(term_t t);

static term_t _o_yices_arith_lt0_atom(term_t t);


/**************************
 *  BITVECTOR CONSTANTS   *
 *************************/

static term_t _o_yices_bvconst_uint32(uint32_t n, uint32_t x);

static term_t _o_yices_bvconst_uint64(uint32_t n, uint64_t x);

static term_t _o_yices_bvconst_int32(uint32_t n, int32_t x);

static term_t _o_yices_bvconst_int64(uint32_t n, int64_t x);

static term_t _o_yices_bvconst_mpz(uint32_t n, const mpz_t x);

static term_t _o_yices_bvconst_zero(uint32_t n);

static term_t _o_yices_bvconst_one(uint32_t n);

static term_t _o_yices_bvconst_minus_one(uint32_t n);

static term_t _o_yices_bvconst_from_array(uint32_t n, const int32_t a[]);

static term_t _o_yices_parse_bvbin(const char *s);

static term_t _o_yices_parse_bvhex(const char *s);
  

/***************************
 *  BIT-VECTOR ARITHMETIC  *
 ***************************/

static term_t _o_yices_bvadd(term_t t1, term_t t2);

static term_t _o_yices_bvsub(term_t t1, term_t t2);

static term_t _o_yices_bvneg(term_t t1);

static term_t _o_yices_bvmul(term_t t1, term_t t2);

static term_t _o_yices_bvsquare(term_t t1);

static term_t _o_yices_bvpower(term_t t1, uint32_t d);

/************************************
 *  N-ARY BIT-VECTOR SUMS/PRODUCTS  *
 ***********************************/

static term_t _o_yices_bvsum(uint32_t n, const term_t t[]);

static term_t _o_yices_bvproduct(uint32_t n, const term_t t[]);

/***********************************
 *  BITWISE BIT-VECTOR OPERATIONS  *
 **********************************/

static term_t _o_yices_bvnot(term_t t1);

static term_t _o_yices_bvnand(term_t t1, term_t t2);

static term_t _o_yices_bvnor(term_t t1, term_t t2);

static term_t _o_yices_bvxnor(term_t t1, term_t t2);


/************************************
 *  ASSOCIATIVE BITWISE OPERATIONS  *
 ***********************************/

static term_t _o_yices_bvand(uint32_t n, const term_t t[]);

static term_t _o_yices_bvor(uint32_t n, const term_t t[]);

static term_t _o_yices_bvxor(uint32_t n, const term_t t[]);

static term_t _o_yices_bvand2(term_t t1, term_t t2);

static term_t _o_yices_bvor2(term_t t1, term_t t2);

static term_t _o_yices_bvxor2(term_t t1, term_t t2);
 
/*********************************************
 *   BITVECTOR SHIFT/ROTATION BY A CONSTANT  *
 ********************************************/

static term_t _o_yices_shift_left0(term_t t, uint32_t n);

static term_t _o_yices_shift_left1(term_t t, uint32_t n);

static term_t _o_yices_shift_right0(term_t t, uint32_t n);

static term_t _o_yices_shift_right1(term_t t, uint32_t n);

static term_t _o_yices_ashift_right(term_t t, uint32_t n);

static term_t _o_yices_rotate_left(term_t t, uint32_t n);

static term_t _o_yices_rotate_right(term_t t, uint32_t n);

/****************************************
 *  BITVECTOR EXTRACTION/CONCATENATION  *
 ***************************************/

static term_t _o_yices_bvextract(term_t t, uint32_t i, uint32_t j);

static term_t _o_yices_bvconcat2(term_t t1, term_t t2);

static term_t _o_yices_bvconcat(uint32_t n, const term_t t[]);

static term_t _o_yices_bvrepeat(term_t t, uint32_t n);

static term_t _o_yices_sign_extend(term_t t, uint32_t n);

static term_t _o_yices_zero_extend(term_t t, uint32_t n);

static term_t _o_yices_redand(term_t t);

static term_t _o_yices_redor(term_t t);

static term_t _o_yices_redcomp(term_t t1, term_t t2);

/*******************************
 *  GENERIC BIT-VECTOR SHIFTS  *
 *****************************/

static term_t _o_yices_bvshl(term_t t1, term_t t2);

static term_t _o_yices_bvlshr(term_t t1, term_t t2);

static term_t _o_yices_bvashr(term_t t1, term_t t2);

/**********************************
 *  BITVECTOR DIVISION OPERATORS  *
 *********************************/

static term_t _o_yices_bvdiv(term_t t1, term_t t2);

static term_t _o_yices_bvrem(term_t t1, term_t t2);

static term_t _o_yices_bvsdiv(term_t t1, term_t t2);

static term_t _o_yices_bvsrem(term_t t1, term_t t2);

static term_t _o_yices_bvsmod(term_t t1, term_t t2);

static term_t _o_yices_bvarray(uint32_t n, const term_t arg[]);

static term_t _o_yices_bitextract(term_t t, uint32_t i);

/*********************
 *  BITVECTOR ATOMS  *
 ********************/

static term_t _o_yices_bveq_atom(term_t t1, term_t t2);

static term_t _o_yices_bvneq_atom(term_t t1, term_t t2);

static term_t _o_yices_bvge_atom(term_t t1, term_t t2);

static term_t _o_yices_bvgt_atom(term_t t1, term_t t2);

static term_t _o_yices_bvle_atom(term_t t1, term_t t2);

static term_t _o_yices_bvlt_atom(term_t t1, term_t t2);

static term_t _o_yices_bvsge_atom(term_t t1, term_t t2);

static term_t _o_yices_bvsgt_atom(term_t t1, term_t t2);

static term_t _o_yices_bvsle_atom(term_t t1, term_t t2);

static term_t _o_yices_bvslt_atom(term_t t1, term_t t2);

  
/*********************
 *  PRETTY PRINTING  *
 ********************/

static int32_t _o_yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset);

static int32_t _o_yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset);

static int32_t _o_yices_pp_term_array(FILE *f, uint32_t n, const term_t a[], uint32_t width, uint32_t height, uint32_t offset, int32_t horiz);

static char *_o_yices_type_to_string(type_t tau, uint32_t width, uint32_t height, uint32_t offset);

static char *_o_yices_term_to_string(term_t t, uint32_t width, uint32_t height, uint32_t offset);

/*********************
 *  CHECKS ON TYPES  *
 ********************/

static int32_t _o_yices_type_is_bool(type_t tau);

static int32_t _o_yices_type_is_int(type_t tau);

static int32_t _o_yices_type_is_real(type_t tau);

static int32_t _o_yices_type_is_arithmetic(type_t tau);

static int32_t _o_yices_type_is_bitvector(type_t tau);

static int32_t _o_yices_type_is_tuple(type_t tau);

static int32_t _o_yices_type_is_function(type_t tau);

static int32_t _o_yices_type_is_scalar(type_t tau);

static int32_t _o_yices_type_is_uninterpreted(type_t tau);

static int32_t _o_yices_test_subtype(type_t tau, type_t sigma);

static int32_t _o_yices_compatible_types(type_t tau, type_t sigma);

static uint32_t _o_yices_bvtype_size(type_t tau);

static uint32_t _o_yices_scalar_type_card(type_t tau);

static int32_t _o_yices_type_num_children(type_t tau);

static type_t _o_yices_type_child(type_t tau, int32_t i);

static int32_t _o_yices_type_children(type_t tau, type_vector_t *v);

/***********************
 *  TERM EXPLORATION   *
 **********************/

static type_t _o_yices_type_of_term(term_t t);

static int32_t _o_yices_term_is_bool(term_t t);

static int32_t _o_yices_term_is_int(term_t t);

static int32_t _o_yices_term_is_real(term_t t);

static int32_t _o_yices_term_is_arithmetic(term_t t);

static int32_t _o_yices_term_is_bitvector(term_t t);

static int32_t _o_yices_term_is_tuple(term_t t);

static int32_t _o_yices_term_is_function(term_t t);

static int32_t _o_yices_term_is_scalar(term_t t);

static uint32_t _o_yices_term_bitsize(term_t t);

static int32_t _o_yices_term_is_ground(term_t t);

static int32_t _o_yices_term_is_atomic(term_t t);

static int32_t _o_yices_term_is_composite(term_t t);

static int32_t _o_yices_term_is_projection(term_t t);

static int32_t _o_yices_term_is_sum(term_t t);

static int32_t _o_yices_term_is_bvsum(term_t t);

static int32_t _o_yices_term_is_product(term_t t);

static term_constructor_t _o_yices_term_constructor(term_t t);

static int32_t _o_yices_term_num_children(term_t t);

static term_t _o_yices_term_child(term_t t, int32_t i);

static int32_t _o_yices_proj_index(term_t t);

static term_t _o_yices_proj_arg(term_t t);

static int32_t _o_yices_bool_const_value(term_t t, int32_t *val);

static int32_t _o_yices_bv_const_value(term_t t, int32_t val[]);

static int32_t _o_yices_scalar_const_value(term_t t, int32_t *val);

static int32_t _o_yices_rational_const_value(term_t t, mpq_t q);

static int32_t _o_yices_sum_component(term_t t, int32_t i, mpq_t coeff, term_t *term);

static int32_t _o_yices_bvsum_component(term_t t, int32_t i, int32_t val[], term_t *term);

static int32_t _o_yices_product_component(term_t t, int32_t i, term_t *term, uint32_t *exp);

/*******************************************
 *  EXTENSIONS: SUPPORT FOR TYPE CHECKING  *
 ******************************************/

//FIXME: IAM: these are not exported but should probably be thread safe. How?

/************************
 *  TERM SUBSTITUTION   *
 ***********************/

static term_t _o_yices_subst_term(uint32_t n, const term_t var[], const term_t map[], term_t t);

static int32_t _o_yices_subst_term_array(uint32_t n, const term_t var[], const term_t map[], uint32_t m, term_t t[]);

  
/**************
 *  PARSING   *
 *************/

static type_t _o_yices_parse_type(const char *s);

static term_t _o_yices_parse_term(const char *s);

/************
 *  NAMES   *
 ***********/

static int32_t _o_yices_set_type_name(type_t tau, const char *name);

static int32_t _o_yices_set_term_name(term_t t, const char *name);

static const char *_o_yices_get_type_name(type_t tau);

static const char *_o_yices_get_term_name(term_t t);

static void _o_yices_remove_type_name(const char *name);

static void _o_yices_remove_term_name(const char *name);

static type_t _o_yices_get_type_by_name(const char *name);

static term_t _o_yices_get_term_by_name(const char *name);

static int32_t _o_yices_clear_type_name(type_t tau);

static int32_t _o_yices_clear_term_name(term_t t);


/****************************
 *  CONTEXT CONFIGURATIONS  *
 ***************************/

/*******************************************
 *  SIMPLIFICATION/PREPROCESSING OPTIONS   *
 ******************************************/

/*************************************
 *  SEARCH PARAMETER CONFIGURATIONS  *
 ************************************/

/****************
 *  UNSAT CORE  *
 ***************/

/************
 *  MODELS  *
 ***********/

/************************
 *  VALUES IN A MODEL   *
 ***********************/


/*************************
 *  GARBAGE COLLECTION   *
 ************************/



#endif /* ___O_YICES_API_H */
