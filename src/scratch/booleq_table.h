/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXPERIMENTAL: TABLE OF BOOLEAN EQUALITIES
 */

/*
 * This is used to keep track of assertions of the form
 *   l := (xor a b) or  l := (eq a b)
 * where l, a, and b are literals.
 *
 * We keep a table that maps boolean variables to pairs of literals:
 * for a variable x: def[x] is either -1 (no definition) or the
 * index i of in array eq: eq[i] is a pair {a, b}.
 * This records that the assertion pos_lit(x) := (eq a b) was asserted.
 *
 * Given l := (xor a b)
 * - if l is neg_lit(x), we convert the constraint to (not l) := (xor (not a) b)
 * - after this sterp we can assume the constraint is of the form
 *      pos_lit(x) := (xor a b), which is equivalent to
 *      pos_lit(x) := (eq (not a) b)
 * - we then store the pair {a, b} in def[x]
 */

#ifndef __BOOLEQ_TABLE_H
#define __BOOLEQ_TABLE_H

#include <stdint.h>
#include <stdbool.h>

#include "solvers/cdcl/smt_core_base_types.h"


/*
 * Table:
 * -  def maps variables to eq descriptor indices
 *    def[x] is valid for all x such that 0 <= x < nvars
 *    dsize = full size of array def
 * -  eq = array of equality descriptors
 *    neq = number of equalities stored
 *    esize = full size of array eq
 * TODO: add support for push/pop
 */

// boolean equality = pair of literals
typedef struct booleq_s {
  literal_t lit[2];
} booleq_t;

typedef struct booleq_table_s {
  int32_t *def;
  booleq_t *eq;
  uint32_t nvars;
  uint32_t dsize;
  uint32_t neqs;
  uint32_t esize;
} booleq_table_t;


// default and max size for array def
#define BOOLEQ_DEFAULT_DSIZE 100
#define BOOLEQ_MAX_DSIZE     (UINT32_MAX/sizeof(int32_t))

// default and max size for array eq
#define BOOLEQ_DEFAULT_ESIZE 100
#define BOOLEQ_MAX_ESIZE     (UINT32_MAX/sizeof(booleq_t))


/*
 * Initialize table:
 * - nothing allocated yet: dsize and esize are 0
 */
extern void init_booleq_table(booleq_table_t *table);


/*
 * Empty the table
 */
extern void reset_booleq_table(booleq_table_t *table);


/*
 * Free all memory used
 */
extern void delete_booleq_table(booleq_table_t *table);


/*
 * Record the constraint l := (eq a b)
 * - there must not be any definition for var_of(l)
 */
extern void booleq_table_record_eq(booleq_table_t *table, literal_t l, literal_t a, literal_t b);


/*
 * Record the constraint l := (xor a b)
 */
static inline void booleq_table_record_xor(booleq_table_t *table, literal_t l, literal_t a, literal_t b) {
  booleq_table_record_eq(table, l, not(a), b);
}


/*
 * Check whether x has a definition in the table
 * - x must be a valid variable index (non-negative)
 */
extern bool boolvar_is_eq(booleq_table_t *table, bvar_t x);


/*
 * Same thing for a literal l
 */
static inline bool literal_is_eq(booleq_table_t *table, literal_t l) {
  return boolvar_is_eq(table, var_of(l));
}


/*
 * Get the equality equivalent to l
 * - return false if there's no such equality in table
 * - return true otherwise and set *a and *b
 * If the result is true then the equivalence l <=> (eq *a *b) holds
 */
extern bool get_booleq(booleq_table_t *table, literal_t l, literal_t *a, literal_t *b);


#endif /* __BOOLEQ_TABLE_H */
