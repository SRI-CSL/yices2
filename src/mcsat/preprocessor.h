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

#include "terms/terms.h"
#include "terms/term_manager.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"
#include "io/tracer.h"

#include <setjmp.h>

#ifndef MCSAT_PREPROCESSOR_H_
#define MCSAT_PREPROCESSOR_H_

typedef struct {

  /** Term table */
  term_table_t* terms;

  /** Term manager */
  term_manager_t tm;

  /** Map from terms to their preprocessed version */
  int_hmap_t preprocess_map;

  /** Purification map, term to its variable */
  int_hmap_t purification_map;

  /** Tracer */
  tracer_t* tracer;

  /** Exception handler */
  jmp_buf* exception;

} preprocessor_t;

/** Construct the preprocessor */
void preprocessor_construct(preprocessor_t* pre, term_table_t* terms, jmp_buf* handler);

/** Destruct the preprocessor */
void preprocessor_destruct(preprocessor_t* pre);

/** Preprocess the term, add any additional assertions to output vector. */
term_t preprocessor_apply(preprocessor_t* pre, term_t t, ivector_t* out);

/** Set tracer */
void preprocessor_set_tracer(preprocessor_t* pre, tracer_t* tracer);

/** Set the exception handler */
void preprocessor_set_exception_handler(preprocessor_t* pre, jmp_buf* handler);

#endif
