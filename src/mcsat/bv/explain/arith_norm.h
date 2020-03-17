/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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

#include "utils/int_hash_map2.h"
#include "utils/pair_hash_map.h"
#include "terms/term_manager.h"
#include "terms/term_utils.h"
#include "mcsat/bv/bv_evaluator.h"
#include "arith_utils.h"

/**
   Extracting bits and coefficients from terms.
**/

// The following structure is produced by function analyse below,
// which analyses a term t of bitwidth w.
// Those w bits split into 3 sections: prefix . central_section . suffix
// The bits of t in prefix and suffix are all evaluable in the current context,
// while the first and last bits of the central section aren't.
// In case all bits are evaluable, the central section has length 0 and,
// by convention, the w bits form the suffix (while the prefix also has length 0).

typedef struct arith_analyse_s {

  // Length of the suffix section.
  // i.e. norm[suffix] is the lowest bit of norm that isn't evaluable.
  // suffix is w if all bits below w are evaluable
  uint32_t suffix;
  
  // Length of the central section.
  // norm[suffix+length-1] is the highest bit of norm that isn't evaluable.
  // length is 0 if all bits below w are evaluable
  uint32_t length;

  // Term eval has bitwidth w and contains the prefix, the suffix, while all bits of the central section are set to 0.
  // More precisely:
  // - the suffix bits eval[0] ... eval[suffix-1] are the bits norm[0] ... norm[suffix-1]
  // - the length bits eval[suffix] ... eval[suffix+length-1] are 0 ... 0
  // - the remaining bits eval[suffix+length] ... eval[w-1] are the bits norm[suffix+length] ... norm[w-1]
  term_t eval;
  // Term var is the complement of term eval, so that bvand(eval,var) = 0...0 and bvor(eval,var) = norm
  // - the suffix bits var[0] ... var[suffix-1] are the bits 0 ... 0
  // - the length bits var[suffix] ... var[suffix+length-1] are norm[suffix] ... norm[suffix+length-1]
  // - the remaining bits var[suffix+length] ... var[w-1] are the bits 0 ... 0
  term_t var;
  term_t garbage;
  
  // Term base has bitwidth at least length
  // Bits base[start] ... base[start+length-1] are norm[suffix] ... norm[suffix+length-1]
  term_t base;  
  uint32_t start;

  bool intros;  // whether new constructs have been introduced because negated bits or sign-extensions were found in the original t's central section

} arith_analyse_t;

// In what follows, there's a notion of normalisation via which
// t<w> propagates the lower bit extraction down to variables if t is not evaluable

typedef struct arith_norm_s {

  bv_csttrail_t csttrail; // Where we keep some cached values

  // Cache of analyses (function analyse below): for a pair of keys (t,var),
  // the value is the arith_analyse_t resulting from analysing t when the conflict variable term is var
  pmap_t var_cache;
  // Cache of term normalisations (function extract below): for a pair of keys (t,w), the value is the normal form of t<w>
  int_hmap2_t norm_cache;

} arith_norm_t;

void arith_norm_freeval(arith_norm_t* norm);
arith_analyse_t* arith_analyse(arith_norm_t* norm, term_t t);
term_t arith_normalise_upto(arith_norm_t* norm, term_t t, uint32_t w);

static inline
term_t arith_normalise(arith_norm_t* norm, term_t t){
  term_table_t* terms = norm->csttrail.ctx->terms;
  uint32_t w = bv_term_bitsize(terms, t);
  return arith_normalise_upto(norm, t, w);;
}

static inline
void init_arith_norm(arith_norm_t* norm){
  init_pmap(&norm->var_cache, 0);
  init_int_hmap2(&norm->norm_cache, 0);
}

static inline
void delete_arith_norm(arith_norm_t* norm){
  delete_pmap(&norm->var_cache);
  delete_int_hmap2(&norm->norm_cache);
}

static inline
void reset_arith_norm(arith_norm_t* norm){
  reset_int_hmap2(&norm->norm_cache); // no need to reset the cache of analyses between each conflict
}

/**
   Making atoms. Assumption for these functions:
   the atom to be built evaluates to true according to the trail.
**/

// This function returns (left == right), normalising left and right and simplifying the result
static inline
term_t arith_eq_norm(arith_norm_t* norm, term_t left, term_t right){
  term_manager_t* tm = norm->csttrail.ctx->tm;
  term_t l = arith_normalise(norm, left);
  term_t r = arith_normalise(norm, right);
  term_t t = arith_sub(tm, r, l);
  t = arith_normalise(norm, t);
  return arith_eq0(tm, t);
}

// This function returns (left < right), normalising left and right and simplifying the result
static inline
term_t arith_lt_norm(arith_norm_t* norm, term_t left, term_t right){
  term_manager_t* tm = norm->csttrail.ctx->tm;
  term_t leftn  = arith_normalise(norm, left);
  term_t rightn = arith_normalise(norm, right);
  return arith_lt(tm, leftn, rightn);
}

// This function returns (left < right), normalising left and right and simplifying the result
static inline
term_t arith_le_norm(arith_norm_t* norm, term_t left, term_t right){
  term_manager_t* tm = norm->csttrail.ctx->tm;
  term_t leftn  = arith_normalise(norm, left);
  term_t rightn = arith_normalise(norm, right);
  return arith_le(tm, leftn, rightn);
}

