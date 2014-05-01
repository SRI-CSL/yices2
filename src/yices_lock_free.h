/*
 * 
 * Lock free versions of yices_api.c (implemented in yices_api.c)
 */

#ifndef __YICES_LOCK_FREE_H
#define __YICES_LOCK_FREE_H

#include <stdio.h>

/*
 * LOCK FREE VERSIONS OF YICES_API CALLS
 */


/***********************
 *  TYPE CONSTRUCTORS  *
 **********************/

extern type_t _o_yices_bool_type(void);

extern type_t _o_yices_bv_type(uint32_t size);


/***********************
 *  TERM CONSTRUCTORS  *
 **********************/

extern term_t _o_yices_new_uninterpreted_term(type_t tau);

extern term_t _o_yices_ite(term_t cond, term_t then_term, term_t else_term);

extern term_t _o_yices_eq(term_t left, term_t right);

extern term_t _o_yices_neq(term_t left, term_t right);

/*
 * BOOLEAN NEGATION
 */

extern term_t _o_yices_not(term_t arg);

/*
 * OR, AND, and XOR may modify arg
 */

extern term_t _o_yices_or(uint32_t n, term_t arg[]);

extern term_t _o_yices_and(uint32_t n, term_t arg[]);

extern term_t _o_yices_xor(uint32_t n, term_t arg[]);


/*
 * BINARY VERSIONS OF OR/AND/XOR
 */

extern term_t _o_yices_or2(term_t left, term_t right);

extern term_t _o_yices_and2(term_t left, term_t right);

extern term_t _o_yices_xor2(term_t left, term_t right);

extern term_t _o_yices_iff(term_t left, term_t right);

extern term_t _o_yices_implies(term_t left, term_t right);

extern term_t _o_yices_distinct(uint32_t n, term_t arg[]);

/**************************
 *  BITVECTOR CONSTANTS   *
 *************************/

extern term_t _o_yices_bvconst_uint32(uint32_t n, uint32_t x);

extern term_t _o_yices_bvconst_uint64(uint32_t n, uint64_t x);

extern term_t _o_yices_bvconst_mpz(uint32_t n, mpz_t x);

extern term_t _o_yices_bvconst_zero(uint32_t n);

extern term_t _o_yices_bvconst_one(uint32_t n);

extern term_t _o_yices_bvconst_minus_one(uint32_t n);

extern term_t _o_yices_bvconst_from_array(uint32_t n, int32_t a[]);

extern term_t _o_yices_parse_bvbin(const char *s);

extern term_t _o_yices_parse_bvhex(const char *s);

/***************************
 *  BIT-VECTOR ARITHMETIC  *
 ***************************/

extern term_t _o_yices_bvadd(term_t t1, term_t t2);

extern term_t _o_yices_bvsub(term_t t1, term_t t2);

extern term_t _o_yices_bvneg(term_t t1);

extern term_t _o_yices_bvmul(term_t t1, term_t t2);

extern term_t _o_yices_bvsquare(term_t t1);

extern term_t _o_yices_bvpower(term_t t1, uint32_t d);

/***********************************
 *  BITWISE BIT-VECTOR OPERATIONS  *
 **********************************/

extern term_t _o_yices_bvnot(term_t t1);

extern term_t _o_yices_bvand(term_t t1, term_t t2);

extern term_t _o_yices_bvor(term_t t1, term_t t2);

extern term_t _o_yices_bvxor(term_t t1, term_t t2);

extern term_t _o_yices_bvnand(term_t t1, term_t t2);

extern term_t _o_yices_bvnor(term_t t1, term_t t2);

extern term_t _o_yices_bvxnor(term_t t1, term_t t2);

/*********************************************
 *   BITVECTOR SHIFT/ROTATION BY A CONSTANT  *
 ********************************************/

extern term_t _o_yices_shift_left0(term_t t, uint32_t n);

extern term_t _o_yices_shift_left1(term_t t, uint32_t n);

extern term_t _o_yices_shift_right0(term_t t, uint32_t n);

extern term_t _o_yices_shift_right1(term_t t, uint32_t n);

extern term_t _o_yices_ashift_right(term_t t, uint32_t n);

extern term_t _o_yices_rotate_left(term_t t, uint32_t n);

extern term_t _o_yices_rotate_right(term_t t, uint32_t n);

/****************************************
 *  BITVECTOR EXTRACTION/CONCATENATION  *
 ***************************************/

extern term_t _o_yices_bvextract(term_t t, uint32_t i, uint32_t j);

extern term_t _o_yices_bvconcat(term_t t1, term_t t2);

extern term_t _o_yices_bvrepeat(term_t t, uint32_t n);

extern term_t _o_yices_sign_extend(term_t t, uint32_t n);

extern term_t _o_yices_zero_extend(term_t t, uint32_t n);

extern term_t _o_yices_redand(term_t t);

extern term_t _o_yices_redor(term_t t);

extern term_t _o_yices_redcomp(term_t t1, term_t t2);

/*******************************
 *  GENERIC BIT-VECTOR SHIFTS  *
 *****************************/

extern term_t _o_yices_bvshl(term_t t1, term_t t2);

extern term_t _o_yices_bvlshr(term_t t1, term_t t2);

extern term_t _o_yices_bvashr(term_t t1, term_t t2);

/**********************************
 *  BITVECTOR DIVISION OPERATORS  *
 *********************************/

extern term_t _o_yices_bvdiv(term_t t1, term_t t2);

extern term_t _o_yices_bvrem(term_t t1, term_t t2);

extern term_t _o_yices_bvsdiv(term_t t1, term_t t2);

extern term_t _o_yices_bvsrem(term_t t1, term_t t2);

extern term_t _o_yices_bvsmod(term_t t1, term_t t2);

extern term_t _o_yices_bvarray(uint32_t n, term_t arg[]);

extern term_t _o_yices_bitextract(term_t t, uint32_t i);

/*********************
 *  BITVECTOR ATOMS  *
 ********************/

extern term_t _o_yices_bveq_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvneq_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvge_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvgt_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvle_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvlt_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvsge_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvsgt_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvsle_atom(term_t t1, term_t t2);

extern term_t _o_yices_bvslt_atom(term_t t1, term_t t2);


/*********************
 *  PRETTY PRINTING  *
 ********************/

extern int32_t _o_yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset);

extern int32_t _o_yices_pp_term(FILE *f, term_t t, uint32_t width, uint32_t height, uint32_t offset);


/*********************
 *  CHECKS ON TYPES  *
 ********************/

extern int32_t _o_yices_type_is_bool(type_t tau);

extern int32_t _o_yices_type_is_bitvector(type_t tau);

extern int32_t _o_yices_test_subtype(type_t tau, type_t sigma);

extern uint32_t _o_yices_bvtype_size(type_t tau);

/**************************
 *  SOME CHECKS ON TERMS  *
 *************************/

extern type_t _o_yices_type_of_term(term_t t);

extern int32_t _o_yices_term_is_bool(term_t t);

extern int32_t _o_yices_term_is_bitvector(term_t t);

extern uint32_t _o_yices_term_bitsize(term_t t);


/************************
 *  TERM SUBSTITUTION   *
 ***********************/

extern term_t _o_yices_subst_term(uint32_t n, term_t var[], term_t map[], term_t t);

extern int32_t _o_yices_subst_term_array(uint32_t n, term_t var[], term_t map[], uint32_t m, term_t t[]);


/**************
 *  PARSING   *
 *************/

extern type_t _o_yices_parse_type(const char *s);

extern term_t _o_yices_parse_term(const char *s);


/************
 *  NAMES   *
 ***********/

extern int32_t _o_yices_set_type_name(type_t tau, const char *name);

extern int32_t _o_yices_set_term_name(term_t t, const char *name);

extern const char *_o_yices_get_type_name(type_t tau);

extern const char *_o_yices_get_term_name(term_t t);

extern void _o_yices_remove_type_name(const char *name);

extern void _o_yices_remove_term_name(const char *name);

extern type_t _o_yices_get_type_by_name(const char *name);

extern term_t _o_yices_get_term_by_name(const char *name);

extern int32_t _o_yices_clear_type_name(type_t tau);

extern int32_t _o_yices_clear_term_name(term_t t);

/*************************
 *  CONTEXT OPERATIONS   *
 ************************/

extern int32_t _o_yices_assert_formula(context_t *ctx, term_t t);

extern int32_t _o_yices_assert_formulas(context_t *ctx, uint32_t n, term_t t[]);

extern int32_t _o_yices_assert_blocking_clause(context_t *ctx);

extern smt_status_t _o_yices_check_context(context_t *ctx, const param_t *params);

extern void _o_yices_set_default_params(context_t *ctx, param_t *params);


/*******************************************
 *  SIMPLIFICATION/PREPROCESSING OPTIONS   *
 ******************************************/

extern int32_t _o_yices_context_enable_option(context_t *ctx, const char *option);


/*************************
 *  CONTEXT OPERATIONS   *
 ************************/

extern smt_status_t _o_yices_context_status(context_t *ctx);

extern uint32_t _o_yices_push_level(context_t *ctx);

extern void _o_yices_reset_context(context_t *ctx);

extern int32_t _o_yices_push(context_t *ctx);

extern int32_t _o_yices_pop(context_t *ctx);






/************
 *  MODELS  *
 ***********/

extern void _o_yices_print_model(FILE *f, model_t *mdl);

extern model_t *_o_yices_get_model(context_t *ctx, int32_t keep_subst);

extern int32_t _o_yices_pp_model(FILE *f, model_t *mdl, uint32_t width, uint32_t height, uint32_t offset);

extern int32_t _o_yices_pp_value_in_model(FILE *f, model_t *mdl, term_t t, uint32_t width, uint32_t height, uint32_t offset);

extern int32_t _o_yices_get_bool_value(model_t *mdl, term_t t, int32_t *val);

extern int32_t _o_yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]);


/*************************
 *  GARBAGE COLLECTION   *
 ************************/

extern int32_t _o_yices_incref_term(term_t t);

extern int32_t _o_yices_incref_type(type_t tau);

extern int32_t _o_yices_decref_term(term_t t);

extern int32_t _o_yices_decref_type(type_t tau);

extern uint32_t _o_yices_num_terms(void);

extern uint32_t _o_yices_num_types(void);

extern uint32_t _o_yices_num_posref_terms(void);

extern uint32_t _o_yices_num_posref_types(void);

extern void _o_yices_garbage_collect(term_t *t, uint32_t nt,
                                     type_t *tau, uint32_t ntau,
                                     int32_t keep_named);



#endif /* __YICES_LOCK_FREE_H */
