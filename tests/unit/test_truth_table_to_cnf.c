/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONVERSION OF A THREE-VARIABLE TRUTH TABLE TO CNF
 */

#include <inttypes.h>
#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#include "utils/bit_tricks.h"


/*
 * Truth table: defined by an 8bit array b[7 ... 0]
 *
 * The input variables are denoted by y, z, t.
 * The output is denoted by x. The table is as follows:
 *
 *  y   z   t    x
 * -----------------
 *  0   0   0    b0
 *  0   0   1    b1
 *  0   1   0    b2
 *  0   1   1    b3
 *  1   0   0    b4
 *  1   0   1    b5
 *  1   1   0    b6
 *  1   1   1    b7
 *
 * Each row can be converted to a clause. For example,
 * the first row is:
 *    (not y) and (not z) and (not t) => x = b0
 * that is,
 *    (y or z or t or x=b0)
 *
 * But we want to minimize the number of clauses.
 * This is what this test is about.
 */


/*
 * Show the table defined by array b
 */
static void show_table(int32_t b[8]) {
  uint32_t i;
  int32_t vy, vz, vt;

  printf("Truth table:\n");
  printf(" y  z  t | x\n");
  printf("-------------\n");
  for (i=0; i<8; i++) {
    vy = (i & 4) >> 2;
    vz = (i & 2) >> 1;
    vt = (i & 1);
    printf(" %"PRId32"  %"PRId32"  %"PRId32" | %"PRId32"\n", vy, vz, vt, b[i]);
  }
  printf("-------------\n\n");
}


/*
 * CNF encoding: each clause is defined by
 * - an index i between 0 and 7
 * - the value b[i] for x
 * - a bit-mask m[i] of four bits
 *
 * i is formed of three bits i2 i1 i0, which define three literals
 * (i.e., a row in the table as above)
 * - if i2 is 1, the first  literal is (not y), otherwise, it's y (literal l2)
 * - if i1 is 1, the second literal is (not z), otherwise, it's z (literal l1)
 * - if i0 is 1, the third  literal is (not t), otherwise, it's t (literal l0)
 *
 * so before simplification, clause i is
 *   (l2 \/ l1 \/ l0 \/ (x == b[i]))
 *
 * the bit-mask m[i] determines how much simplification was done:
 * - if m[i] is 0, then clause i was removed (subsumed)
 * - otherwise m[i] is of the form m3 m2 m1 m0 with m3 equal to 1:
 *   if m2 is 1, l2 is kept (otherwise, it's removed)
 *   if m1 is 1, l1 is kept (otherwise, it's removed)
 *   if m0 is 1, l0 is kept (otherwise, it's removed)
 *
 * We use the following bit-tricks:
 * - the common variables of two clauses i and j is defined
 *   by the '1' bits in m[i] & m[j]
 * - the variables that have opposite polarities in i and j
 *   are defined  by (i ^ j) & m[i] & m[j]
 */

static void show_literal(const char *var, uint32_t sign) {
  assert(sign == 0 || sign == 1);
  if (sign == 1) {
    printf(" ~%s", var);
  } else {
    printf("  %s", var);
  }
}

static void show_clauses(int32_t b[8], uint32_t m[8]) {
  uint32_t i;

  for (i=0; i<8; i++) {
    if (m[i] != 0) {
      if (m[i] & 7) {
	printf("(or");
      }
      if (m[i] & 4) {
	show_literal("y", (i>>2) & 1);
      }
      if (m[i] & 2) {
	show_literal("z", (i>>1) & 1);
      }
      if (m[i] & 1) {
	show_literal("t", i & 1);
      }
      show_literal("x", b[i] ^ 1);
      if (m[i] & 7) {
	printf(")");
      }
      printf("\n");
    }
  }
}


// convert m to a 32bit unsigned integer then print that
static void show_compact_mask(uint32_t m[8]) {
  uint32_t i, compact;

  compact = 0;
  i = 8;
  while (i > 0) {
    i --;
    assert(0 == m[i] || (8 <= m[i] && m[i] < 16));
    compact = (compact << 4) | m[i];
  }

  printf("CNF compilation code: %"PRIu32" 0x%08x\n", compact, compact);
}



/*
 * Simplify the set of clauses using clause i
 * - the clauses are given by m and b
 * - return true if a clause is reduced
 */
static bool reduce_by_clause(uint32_t m[8], int32_t b[8], uint32_t i) {
  uint32_t j, delta;
  bool changed;

  changed = false;

  for (j=0; j<8; j++) {
    if (i != j && b[i] == b[j] && m[j] != 0 && (m[i] & m[j]) == m[i]) {
      delta = (i ^ j) & m[i];
      switch (delta) {
      case 0:
	changed = true;
	m[j] = 0; // i subsumes j
	break;

      case 1:
      case 2:
      case 4:
	/*
	 * i is of the form a \/ B
	 * j is of the form (not a) \/ B or C
	 * with C possibly empty.
	 * resolving gives: B \/ C which subsumes j
	 */
	changed = true;
	m[j] ^= delta; // replace j by i
	break;

      default:
	// keep j as is
	break;
      }
    }
  }

  return changed;
}


/*
 * The triple (k, msk, v) defines a clause
 * - k = index between 0 and 7 (variables are y, z, t)
 * - msk = bit mask
 * - v = value of x
 * This function checks whether one clause in the set
 * is subsumed by (k, msk, v) and if so it removes it.
 * - return true if some clause is removed
 */
static bool check_subsumption(uint32_t m[8], int32_t b[8], uint32_t k, uint32_t msk, int32_t v) {
  uint32_t i;
  bool changed;

  changed = false;

  for (i=0; i<8; i++) {
    if (m[i] != 0 && b[i] == v && (msk & m[i]) == msk) {
      if (((i ^ k) & msk) == 0) {
	// clause i is subsumed
	m[i] = 0;
	changed = true;
      }
    }
  }

  return changed;
}


/*
 * Go through all pairs of clauses i, j:
 * - if i and j can be resolved, build the resulting clause (k, msk, v)
 *   then check whether (k, msk, v) subsumes anything
 * - return true if anything changes
 */
static bool remove_redundant_clauses(uint32_t m[8], int32_t b[8]) {
  uint32_t i, j, delta;
  uint32_t k, msk;
  bool changed;

  changed = false;

  for (i=0; i<7; i++) {
    if (m[i] != 0) {
      for (j=i+1; j<8; j++) {
	if (m[j] != 0 && b[i] == b[j]) {
	  delta = (i ^ j) & m[i] & m[j];
	  if (popcount32(delta) == 1) {
	    // i and j can be resolved
	    msk = (m[i] | m[j]) ^ delta;
	    k = ((i & m[i]) | (j & m[j])) ^ delta;
	    changed |= check_subsumption(m, b, k, msk, b[i]);
	  }
	}
      }
    }
  }

  return changed;
}



/*
 * Check consistency
 */
static bool check_cnf(int32_t b[8], uint32_t m[8]) {
  uint32_t i, j;

  for (i=0; i<8; i++) {
    // i == truth assignment for y, z, t
    for (j=0; j<8; j++) {
      if (m[j] != 0 && ((i^j) & m[j]) == 0) {
	if (b[j] != b[i]) return false;
      }
    }
  }

  return true;
}



static void make_cnf(int32_t b[8], uint32_t m[8]) {
  uint32_t i, changed;

  for (i=0; i<8; i++) {
    m[i] = 0x0f;
  }

  printf("Initial clauses:\n");
  show_clauses(b, m);
  printf("\n");

  /*
   * simplification using subsumption/resolution
   */
  do {
    changed = false;
    for (i=0; i<8; i++) {
      if (m[i] != 0) {
	changed |= reduce_by_clause(m, b, i);
      }
    }
  } while (changed);

  printf("Simplified clauses:\n");
  show_clauses(b, m);
  show_compact_mask(m);
  printf("\n");

  if (! check_cnf(b, m)) {
    printf("BUG: invalid CNF conversion\n");
    fflush(stdout);
    exit(1);
  }

  /*
   * Full reduction
   */
  while (remove_redundant_clauses(m, b));

  printf("Reduced clause set:\n");
  show_clauses(b, m);
  show_compact_mask(m);
  printf("\n");

  if (! check_cnf(b, m)) {
    printf("BUG: invalid CNF conversion\n");
    fflush(stdout);
    exit(1);
  }
}

int main(void) {
  int32_t b[8];
  uint32_t m[8];
  uint32_t i, j;

  for (i=0; i<256; i++) {
    printf("Function %"PRIu32"\n\n", i);
    for (j=0; j<8; j++) {
      b[j] = (i >> j) & 1;
    }
    show_table(b);
    make_cnf(b, m);
    printf("\n");
  }

  return 0;
}
