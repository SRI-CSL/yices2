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

/*
 * Bitset-based assumption cache for the CDCL(T) plugin.
 *
 * Each atom is assigned a compact uint32_t index.  A set of atoms is
 * represented as a bitset stored as an array of uint64_t words.
 *
 * The cache stores two classes of entries:
 *   SAT   - assumption sets known to be satisfiable
 *   UNSAT - assumption sets (cores) known to be unsatisfiable
 *
 * Lookup semantics:
 *   A query Q is SAT  if some cached SAT entry S ⊇ Q  (superset → also SAT).
 *   A query Q is UNSAT if some cached UNSAT entry U ⊆ Q (subset → also UNSAT).
 */

#ifndef CDCLT_SAT_CACHE_H
#define CDCLT_SAT_CACHE_H

#include <stdint.h>
#include <stdbool.h>

#include "terms/terms.h"
#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"

typedef struct {
  int_hmap_t atom_index;   /* term_t -> uint32_t compact index           */
  term_t    *atoms;        /* reverse map: index -> term_t               */
  uint32_t   n_atoms;
  uint32_t   atoms_cap;

  uint32_t   n_words;      /* ceil(n_atoms / 64), current bitset width   */

  uint64_t  *sat_bits;     /* flat row-major [sat_count * n_words]       */
  uint32_t   sat_count;
  uint32_t   sat_cap;

  uint64_t  *unsat_bits;   /* flat row-major [unsat_count * n_words]     */
  uint32_t   unsat_count;
  uint32_t   unsat_cap;

  uint64_t  *scratch;      /* n_words words for building the current query */
  uint32_t   scratch_cap;
} cdclt_sat_cache_t;


void cdclt_sat_cache_init(cdclt_sat_cache_t *c);
void cdclt_sat_cache_destroy(cdclt_sat_cache_t *c);

/*
 * Register atom t; return its compact index.  Idempotent.
 * Triggers in-place buffer resize when n_atoms crosses a 64-boundary.
 */
uint32_t cdclt_sat_cache_register_atom(cdclt_sat_cache_t *c, term_t t);

/*
 * Build scratch bitset from assump.
 * Returns false if any literal is unregistered.
 */
bool cdclt_sat_cache_build(cdclt_sat_cache_t *c, const ivector_t *assump);

/*
 * Like build but writes into dst instead of scratch.
 */
bool cdclt_sat_cache_build_into(cdclt_sat_cache_t *c, const ivector_t *assump,
                                uint64_t *dst);

/*
 * Returns true if any cached SAT entry S ⊇ Q (so Q is also SAT).
 */
bool cdclt_sat_cache_lookup_sat(const cdclt_sat_cache_t *c, const uint64_t *Q);

/*
 * Returns true if any cached UNSAT entry U ⊆ Q (so Q is also UNSAT).
 * On hit, appends conflict literals (term_t) into conflict.
 */
bool cdclt_sat_cache_lookup_unsat(const cdclt_sat_cache_t *c, const uint64_t *Q,
                                  ivector_t *conflict);

void cdclt_sat_cache_record_sat(cdclt_sat_cache_t *c, const uint64_t *Q_bits);
void cdclt_sat_cache_record_unsat(cdclt_sat_cache_t *c, const uint64_t *core_bits);

#endif /* CDCLT_SAT_CACHE_H */
