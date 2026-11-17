/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "terms/terms.h"

#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"

typedef struct equality_sensitivity_s {
  /** Input types. */
  type_table_t* types;

  /** Input terms. */
  term_table_t* terms;

  /** Deterministic active-obligation roots for equality-sensitivity scanning. */
  ivector_t obligation_roots;

  /** Per-check assumption roots; reset after solving with assumptions. */
  ivector_t assumption_roots;

  /** Frozen equality-sensitive type ids. */
  int_hset_t types_sensitive;

  /** Worklist for equality-sensitive type closure. */
  ivector_t type_worklist;

  /** Worklist for active-obligation DAG scanning. */
  ivector_t term_worklist;

  /** Term ids already scanned for the current equality-sensitive generation. */
  int_hset_t scanned_terms;

  /** Temporary vector for term children during equality-sensitivity scanning. */
  ivector_t term_children;

  /** Generation for invalidating future sensitivity-dependent caches. */
  uint32_t generation;

  /** True after the pre-search equality-sensitivity freeze hook has run. */
  bool frozen;

  /** True if obligation roots changed since the last freeze. */
  bool dirty;

  /** Whether term registration currently records active-obligation roots. */
  bool record_registration_roots;

  /** Whether currently recorded registration roots are per-check assumptions. */
  bool registration_roots_are_assumptions;
} equality_sensitivity_t;

extern void equality_sensitivity_construct(equality_sensitivity_t* eqsens,
                                           type_table_t* types,
                                           term_table_t* terms);

extern void equality_sensitivity_destruct(equality_sensitivity_t* eqsens);

extern void equality_sensitivity_note_obligation_root(equality_sensitivity_t* eqsens,
                                                      term_t t);

extern void equality_sensitivity_note_assumption_root(equality_sensitivity_t* eqsens,
                                                      term_t t);

extern void equality_sensitivity_note_registered_term(equality_sensitivity_t* eqsens,
                                                      term_t t);

extern uint32_t equality_sensitivity_obligation_root_count(const equality_sensitivity_t* eqsens);

extern term_t equality_sensitivity_obligation_root(const equality_sensitivity_t* eqsens,
                                                   uint32_t i);

extern uint32_t equality_sensitivity_assumption_root_count(const equality_sensitivity_t* eqsens);

extern term_t equality_sensitivity_assumption_root(const equality_sensitivity_t* eqsens,
                                                   uint32_t i);

extern void equality_sensitivity_restore_obligation_roots(equality_sensitivity_t* eqsens,
                                                          uint32_t n);

extern void equality_sensitivity_clear_assumption_roots(equality_sensitivity_t* eqsens);

extern void equality_sensitivity_unfreeze(equality_sensitivity_t* eqsens);

extern void equality_sensitivity_freeze(equality_sensitivity_t* eqsens);

extern bool equality_sensitivity_type_is_sensitive(equality_sensitivity_t* eqsens,
                                                   type_t tau);

extern uint32_t equality_sensitivity_generation(const equality_sensitivity_t* eqsens);

extern bool equality_sensitivity_is_frozen(const equality_sensitivity_t* eqsens);

extern bool equality_sensitivity_set_registration_roots_are_assumptions(equality_sensitivity_t* eqsens,
                                                                        bool value);

extern bool equality_sensitivity_set_record_registration_roots(equality_sensitivity_t* eqsens,
                                                               bool value);

#ifndef NDEBUG
extern void equality_sensitivity_assert_generated_equality_is_sensitive(equality_sensitivity_t* eqsens,
                                                                        term_t t);
#endif
