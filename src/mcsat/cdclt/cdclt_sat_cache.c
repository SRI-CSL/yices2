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
 * See cdclt_sat_cache.h for the design overview.
 */

#include <string.h>
#include <assert.h>

#include "mcsat/cdclt/cdclt_sat_cache.h"
#include "utils/bit_tricks.h"
#include "utils/memalloc.h"

/* -----------------------------------------------------------------------
 * Internal helpers
 * --------------------------------------------------------------------- */

/*
 * Initial capacities.
 */
#define INIT_ATOMS_CAP   16
#define INIT_ENTRIES_CAP 16

/*
 * Expand a flat row-major buffer from old_w words/row to new_w words/row.
 * count rows are live.  The buffer already has capacity for count*new_w words.
 * We process rows backwards so each row can be moved right in place.
 * New word columns (indices old_w .. new_w-1) are zeroed.
 */
static void expand_flat_buffer(uint64_t *buf, uint32_t count,
                               uint32_t old_w, uint32_t new_w) {
  assert(new_w > old_w);

  if (count == 0) return;

  /* Move rows from highest to lowest to avoid overwriting unread data. */
  for (uint32_t i = count; i-- > 0; ) {
    /* Source row i starts at buf[i * old_w].
     * Destination row i starts at buf[i * new_w]. */
    uint64_t *src = buf + (size_t)i * old_w;
    uint64_t *dst = buf + (size_t)i * new_w;
    /* memmove handles potential overlap (dst > src when i > 0). */
    memmove(dst, src, (size_t)old_w * sizeof(uint64_t));
    /* Zero the new columns. */
    memset(dst + old_w, 0, (size_t)(new_w - old_w) * sizeof(uint64_t));
  }
}

/*
 * Ensure flat buffer *buf_ptr has capacity for at least new_cap rows,
 * each of n_words width.  *cap_ptr is updated.
 */
static void ensure_flat_cap(uint64_t **buf_ptr, uint32_t *cap_ptr,
                             uint32_t count, uint32_t n_words) {
  assert(n_words > 0);
  uint32_t cap = *cap_ptr;

  if (count < cap) return;

  /* Double capacity, starting from INIT_ENTRIES_CAP. */
  if (cap == 0) {
    cap = INIT_ENTRIES_CAP;
  } else {
    cap = cap * 2;
  }

  *buf_ptr = (uint64_t *)safe_realloc(*buf_ptr,
                                      (size_t)cap * n_words * sizeof(uint64_t));
  *cap_ptr = cap;
}

/* -----------------------------------------------------------------------
 * Public API
 * --------------------------------------------------------------------- */

void cdclt_sat_cache_init(cdclt_sat_cache_t *c) {
  init_int_hmap(&c->atom_index, 0);
  c->atoms     = NULL;
  c->n_atoms   = 0;
  c->atoms_cap = 0;
  c->n_words   = 1; /* at least 1 word even when empty */

  c->sat_bits  = NULL;
  c->sat_count = 0;
  c->sat_cap   = 0;

  c->unsat_bits  = NULL;
  c->unsat_count = 0;
  c->unsat_cap   = 0;

  c->scratch     = NULL;
  c->scratch_cap = 0;
}

void cdclt_sat_cache_destroy(cdclt_sat_cache_t *c) {
  delete_int_hmap(&c->atom_index);
  safe_free(c->atoms);
  safe_free(c->sat_bits);
  safe_free(c->unsat_bits);
  safe_free(c->scratch);

  c->atoms       = NULL;
  c->sat_bits    = NULL;
  c->unsat_bits  = NULL;
  c->scratch     = NULL;
}

/*
 * Ensure scratch has at least n_words capacity.
 */
static void ensure_scratch(cdclt_sat_cache_t *c) {
  if (c->n_words > c->scratch_cap) {
    c->scratch     = (uint64_t *)safe_realloc(c->scratch,
                       (size_t)c->n_words * sizeof(uint64_t));
    c->scratch_cap = c->n_words;
  }
}

uint32_t cdclt_sat_cache_register_atom(cdclt_sat_cache_t *c, term_t t) {
  int_hmap_pair_t *p = int_hmap_get(&c->atom_index, (int32_t)t);

  if (p->val >= 0) {
    /* Already registered. */
    return (uint32_t)p->val;
  }

  /* Assign next compact index. */
  uint32_t idx = c->n_atoms;
  p->val = (int32_t)idx;

  /* Grow atoms array if needed. */
  if (idx >= c->atoms_cap) {
    uint32_t new_cap = (c->atoms_cap == 0) ? INIT_ATOMS_CAP : c->atoms_cap * 2;
    c->atoms     = (term_t *)safe_realloc(c->atoms,
                                          new_cap * sizeof(term_t));
    c->atoms_cap = new_cap;
  }
  c->atoms[idx] = t;
  c->n_atoms    = idx + 1;

  /* Check whether we crossed a 64-boundary and need to widen bitsets. */
  uint32_t new_words = (c->n_atoms + 63) / 64;
  assert(new_words >= 1);

  if (new_words > c->n_words) {
    uint32_t old_words = c->n_words;

    /* Widen sat_bits buffer (even if count=0, keep stride consistent). */
    if (c->sat_cap > 0) {
      c->sat_bits = (uint64_t *)safe_realloc(c->sat_bits,
                      (size_t)c->sat_cap * new_words * sizeof(uint64_t));
      expand_flat_buffer(c->sat_bits, c->sat_count, old_words, new_words);
    }

    /* Widen unsat_bits buffer. */
    if (c->unsat_cap > 0) {
      c->unsat_bits = (uint64_t *)safe_realloc(c->unsat_bits,
                        (size_t)c->unsat_cap * new_words * sizeof(uint64_t));
      expand_flat_buffer(c->unsat_bits, c->unsat_count, old_words, new_words);
    }

    /* Widen scratch. */
    c->scratch     = (uint64_t *)safe_realloc(c->scratch,
                       new_words * sizeof(uint64_t));
    c->scratch_cap = new_words;

    c->n_words = new_words;
  }

  return idx;
}

bool cdclt_sat_cache_build_into(cdclt_sat_cache_t *c, const ivector_t *assump,
                                uint64_t *dst) {
  uint32_t w = c->n_words;
  memset(dst, 0, (size_t)w * sizeof(uint64_t));

  for (uint32_t i = 0; i < assump->size; i++) {
    term_t lit = (term_t)assump->data[i];
    int_hmap_pair_t *p = int_hmap_find(&c->atom_index, (int32_t)lit);
    if (p == NULL) return false;
    uint32_t idx  = (uint32_t)p->val;
    dst[idx / 64] |= (UINT64_C(1) << (idx % 64));
  }
  return true;
}

bool cdclt_sat_cache_build(cdclt_sat_cache_t *c, const ivector_t *assump) {
  ensure_scratch(c);
  return cdclt_sat_cache_build_into(c, assump, c->scratch);
}

bool cdclt_sat_cache_lookup_sat(const cdclt_sat_cache_t *c, const uint64_t *Q) {
  uint32_t w = c->n_words;
  for (uint32_t i = 0; i < c->sat_count; i++) {
    const uint64_t *S = c->sat_bits + (size_t)i * w;
    bool match = true;
    for (uint32_t k = 0; k < w; k++) {
      /* Q ⊆ S  iff  (Q[k] & ~S[k]) == 0 */
      if ((Q[k] & ~S[k]) != 0) {
        match = false;
        break;
      }
    }
    if (match) return true;
  }
  return false;
}

bool cdclt_sat_cache_lookup_unsat(const cdclt_sat_cache_t *c, const uint64_t *Q,
                                  ivector_t *conflict) {
  uint32_t w = c->n_words;
  for (uint32_t i = 0; i < c->unsat_count; i++) {
    const uint64_t *U = c->unsat_bits + (size_t)i * w;
    bool match = true;
    for (uint32_t k = 0; k < w; k++) {
      /* U ⊆ Q  iff  (U[k] & ~Q[k]) == 0 */
      if ((U[k] & ~Q[k]) != 0) {
        match = false;
        break;
      }
    }
    if (match) {
      /* Reconstruct conflict: iterate set bits of U. */
      for (uint32_t k = 0; k < w; k++) {
        uint64_t word = U[k];
        while (word != 0) {
          uint32_t bit = ctz64(word);
          uint32_t atom_idx = k * 64 + bit;
          assert(atom_idx < c->n_atoms);
          ivector_push(conflict, (int32_t)c->atoms[atom_idx]);
          word &= word - 1; /* clear lowest set bit */
        }
      }
      return true;
    }
  }
  return false;
}

void cdclt_sat_cache_record_sat(cdclt_sat_cache_t *c, const uint64_t *Q_bits) {
  uint32_t w = c->n_words;
  ensure_flat_cap(&c->sat_bits, &c->sat_cap, c->sat_count, w);
  uint64_t *row = c->sat_bits + (size_t)c->sat_count * w;
  memcpy(row, Q_bits, (size_t)w * sizeof(uint64_t));
  c->sat_count++;
}

void cdclt_sat_cache_record_unsat(cdclt_sat_cache_t *c, const uint64_t *core_bits) {
  uint32_t w = c->n_words;
  ensure_flat_cap(&c->unsat_bits, &c->unsat_cap, c->unsat_count, w);
  uint64_t *row = c->unsat_bits + (size_t)c->unsat_count * w;
  memcpy(row, core_bits, (size_t)w * sizeof(uint64_t));
  c->unsat_count++;
}
