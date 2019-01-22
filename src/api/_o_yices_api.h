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

/**************************
 *  BITVECTOR CONSTANTS   *
 *************************/

/***************************
 *  BIT-VECTOR ARITHMETIC  *
 ***************************/

/************************************
 *  N-ARY BIT-VECTOR SUMS/PRODUCTS  *
 ***********************************/

/***********************************
 *  BITWISE BIT-VECTOR OPERATIONS  *
 **********************************/

/************************************
 *  ASSOCIATIVE BITWISE OPERATIONS  *
 ***********************************/

/*********************************************
 *   BITVECTOR SHIFT/ROTATION BY A CONSTANT  *
 ********************************************/

/****************************************
 *  BITVECTOR EXTRACTION/CONCATENATION  *
 ***************************************/

/*******************************
 *  GENERIC BIT-VECTOR SHIFTS  *
 *****************************/

/**********************************
 *  BITVECTOR DIVISION OPERATORS  *
 *********************************/

/*********************
 *  BITVECTOR ATOMS  *
 ********************/

/*********************
 *  PRETTY PRINTING  *
 ********************/

/*********************
 *  CHECKS ON TYPES  *
 ********************/

/***********************
 *  TERM EXPLORATION   *
 **********************/


/************************
 *  TERM SUBSTITUTION   *
 ***********************/


/**************
 *  PARSING   *
 *************/


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

/*
 * VALUES AS CONSTANT TERMS
 */

/*
 * MODEL GENERALIZATION
 */

/*************************
 *  GARBAGE COLLECTION   *
 ************************/



#endif /* ___O_YICES_API_H */
