/*
 * We combine 32indices with a polarity bit to represent positive 
 * and negative occurrences of a term t. This is used for encoding
 * boolean negation efficiently. If t is a boolean term, then
 * pos_occ(t) means t
 * neg_occ(t) means (not t).
 *
 * We encode the polarity bit as the low-order bit of 32bit signed 
 * integers. Negative numbers are error indicators. This encoding
 * is used in several places. Utility function to manipulate term
 * indices and term occurrences are defined here.
 */

#ifndef __TERM_OCCURRENCES_H
#define __TERM_OCCURRENCES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>


/*
 * Conversion between terms and occurrences:
 * - the polarity bit is the low-order bit of
 *   0 means positive polarity
 *   1 means negative polarity
 */
static inline int32_t pos_occ(int32_t t) {
  return (t << 1);
}

static inline int32_t neg_occ(int32_t t) {
  return (t << 1) | 1;
}

// polarity 0 --> pos_occ(t), polarity 1 --> neg_occ(t)
static inline int32_t mk_occ(int32_t t, uint32_t polarity) {
  assert((polarity & ~1) == 0);
  return (t << 1) | polarity;
}

/*
 * Extract term and polarity bit
 */
static inline int32_t term_of(int32_t x) {
  return x>>1;
}

static inline uint32_t polarity_of(int32_t x) {
  return ((uint32_t) x) & 1;
} 


/*
 * Check polarity
 */
static inline bool is_pos_occ(int32_t x) {
  return polarity_of(x) == 0;
}

static inline bool is_neg_occ(int32_t x) {
  return polarity_of(x) != 0;
}


/*
 * Complement of x = same term, opposite polarity
 */
static inline int32_t opposite_occ(int32_t x) {
  return x ^ 1;
}


#endif /* __TERM_OCCURRENCES_H */
