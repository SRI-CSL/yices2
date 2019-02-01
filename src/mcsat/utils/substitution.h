/*
 * substitution.h
 *
 *  Created on: Jan 31, 2019
 *      Author: dejan
 */

#pragma once

#include "terms/terms.h"
#include "terms/term_manager.h"
#include "io/tracer.h"
#include "utils/int_hash_map.h"

#include <stdbool.h>

/** Substitution that alows arbitrary terms to be substituted */
typedef struct {

  /** Map from terms to terms to substitute */
  int_hmap_t substitution_fwd;

  /** Map from terms back to original terms */
  int_hmap_t substitution_bck;

  /** Tracer */
  tracer_t* tracer;

  /** Term manager */
  term_manager_t* tm;

} substitution_t;

/** Construct the substitution */
void substitution_construct(substitution_t* subst, term_manager_t* tm, tracer_t* tracer);

/** Destruct the data in the substitution */
void substitution_destruct(substitution_t* subst);

/**
 * Run the forward substitution and return the result.
 *
 * Frontier takes precedence to substitution, i.e., if a *strict* subterm is
 * in the frontier the substitution returns the subterm without modifications.
 *
 * NOTE: intermediate results are cached, which affects later uses
 */
term_t substitution_run_fwd(substitution_t* subst, term_t t, const int_hmap_t* frontier);

/**
 * Run the forward substitution and return the result.
 *
 * Frontier takes precedence to substitution, i.e., if a *strict* subterm is
 * in the frontier the substitution returns the subterm without modifications.
 *
 * NOTE: intermediate results are cached, which affects later uses
 */
term_t substitution_run_bck(substitution_t* subst, term_t t, const int_hmap_t* frontier);

/** Check if the substitution has the given term */
bool substitution_has_term(const substitution_t* subst, term_t term);

/** Add another pair to the substitution */
void substitution_add(substitution_t* subst, term_t t, term_t t_subst);

