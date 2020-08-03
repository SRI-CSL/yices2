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

#pragma once

#include <stdio.h>
#include <cudd.h>

#include "terms/terms.h"
#include "utils/pointer_vectors.h"

typedef DdNode BDD;

#define BDDS_RESERVE_MAX 2

typedef struct {
  DdManager* cudd;
  int* tmp_inputs;
  char* tmp_model;
  size_t tmp_alloc_size;
  pvector_t reserve[BDDS_RESERVE_MAX];
  uint32_t reserve_i;
} CUDD;

/** Construct and allocate cudd */
CUDD* bdds_new();

/** Destruct and delete cudd */
void bdds_delete(CUDD* cudd);

/**
 * Given the term and BDDs of all the children compute the BDDs into
 * the output. The out_bdds should be initialized to NULL.
 */
void bdds_compute_bdds(CUDD* cudd, term_table_t* terms, term_t t,
    const pvector_t* children_bdds, BDD** out_bdds);

/** Initialize: set all to NULL. */
void bdds_init(BDD** a, uint32_t n);

/** Dereference all non-NULL bdds in a and set them to NUL.L */
void bdds_clear(CUDD* cudd, BDD** a, uint32_t n);

/** Attach extra reference all bdds in a. */
void bdds_attach(BDD** a, uint32_t n);

/** Copy BDDs from a to out and attach. */
void bdds_copy(BDD** out, BDD** a, uint32_t n);

/** Compare the two BDD vectors. */
bool bdds_eq(BDD** a, BDD** b, uint32_t n);

/** Print the BDDs to out. */
void bdds_print(CUDD* cudd, BDD** a, uint32_t n, FILE* out);

/** Check if the BDD is a point of given size (only one solution). */
bool bdds_is_point(CUDD* cudd, BDD* a, uint32_t size);

/**
 * Check if the constant satisfies the constraint C(x). The variables in x
 * should be the same size as x_value.
 */
bool bdds_is_model(CUDD* cudd, BDD** x, BDD* C_x, const bvconstant_t* x_value);

/** Get a constant that satisfies the constraint C(x). */
void bdds_get_model(CUDD* cudd, BDD** x, BDD* C_x, bvconstant_t* out);

/** Make a new variable. */
void bdds_mk_variable(CUDD* cudd, BDD** out, uint32_t n);

/** Make a repeat b...b BDD. */
void bdds_mk_repeat(CUDD* cudd, BDD** out, BDD* b, uint32_t n);

/** Make a constant 0...0 BDD. */
void bdds_mk_zero(CUDD* cudd, BDD** out, uint32_t n);

  /** Make a constant 0...01 BDD. */
void bdds_mk_one(CUDD* cudd, BDD** out, uint32_t n);

/** Make a constant BDD. */
void bdds_mk_constant(CUDD* cudd, BDD** out, uint32_t n, const bvconstant_t* c);

/** Check if a BDD is constant */
bool bdds_is_constant(CUDD* cudd, BDD** a, uint32_t n);

/** Check if a BDD is constant 0...0 */
bool bdds_is_constant_zero(CUDD* cudd, BDD** a, uint32_t n);

/** Check if a BDD is constant 0...01 */
bool bdds_is_constant_one(CUDD* cudd, BDD** a, uint32_t n);

/** Check if a BDD is constant 1...1 */
bool bdds_is_constant_neg_one(CUDD* cudd, BDD** a, uint32_t n);

/** Check if a BDD is a power of 2. Returns power, or -1 if not */
int32_t bdds_is_constant_pow2(CUDD* cudd, BDD** a, uint32_t n);

/** Negate the BDDs a. */
void bdds_mk_not(CUDD* cudd, BDD** out, BDD** a, uint32_t n);

/** Boolean and of the BDDs in a and b. */
void bdds_mk_and(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n);

/** Boolean or of the BDDs in a and b. */
void bdds_mk_or(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n);

/** Two's complement (negation) of the BDDs in a. */
void bdds_mk_2s_complement(CUDD* cudd, BDD** out, BDD** a, uint32_t n);

/** Addition of the BDDs in a and b. */
void bdds_mk_plus(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n);

/** Multiplication of the BDDs in a and b. */
void bdds_mk_mult(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n);

/** Division of the BDDs in a and b. */
void bdds_mk_div(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Remainder of the BDDs in a and b. */
void bdds_mk_rem(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Signed division of BDDs in a and b. */
void bdds_mk_sdiv(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Signed remainder of BDDs in a and b (rounding to 0). */
void bdds_mk_srem(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Signed remainder of BDDs in a and b. (rounding to -infinity). */
void bdds_mk_smod(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Left shift of BDDs in a and b (padding 0). */
void bdds_mk_shl(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Left shift of BDDs in a */
void bdds_mk_shl_const(CUDD* cudd, BDD** out_bdds, BDD** a, uint32_t shift, uint32_t n);

/** Logical shift right of BDDs in a and b (padding with 0). */
void bdds_mk_lshr(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Arithmetic shift right (padding with sign bit). */
void bdds_mk_ashr(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Equality circuit of BDDs in a and b, out is of n 1. */
void bdds_mk_eq(CUDD* cudd, BDD** out, BDD** a, BDD** b, uint32_t n);

/** Unsigned comparison circuit of BDDs in a and b, out is of n 1. */
void bdds_mk_ge(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);

/** Signed comparison circuit of BDDs in a and b, out is of n 1. */
void bdds_mk_sge(CUDD* cudd, BDD** out_bdds, BDD** a, BDD** b, uint32_t n);
