/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * EXPERIMENTAL CODE: TABLE OF ROWS FOR SIMPLEX PROPAGATION
 */

/*
 * Each row is an equation a_1 x_1 + ... + a_n x_n = 0
 * - rows are added on the fly
 * - each row has an activity, similar to the activity of learned clauses
 *   in smt_core.
 *
 * For row deletion:
 * - a row is locked if it's used as explanation for an implied literal/atom
 *   (the lock for is the first implied literal in the smt_core's queue).
 *   if the lock is null_literal, then the row is not used as an explanation.
 *
 * Two propagation rules are associated with this equality:
 *
 * 1) Implied lower bound:
 *    let u_1, ..., u_n be constants and U = u_1 + ... + u_n then
 *    a_1 x_1 <= u_1, ..., a_n x_n <= u_n implies a_i x_i >= U - u_i
 *
 * 2) Implied upper bound:
 *    let l_1, ..., l_n be constants and L = l_1 + ... + l_n then
 *    a_1 x_1 >= l_1, ..., a_n x_n >= l_n implies a_i x_i <= L - l_i
 *
 */

#ifndef __SIMPLEX_PROP_TABLE_H
#define __SIMPLEX_PROP_TABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "terms/polynomials.h"
#include "solvers/simplex/matrices.h"
#include "utils/int_vectors.h"
#include "solvers/cdcl/smt_core.h"


/*
 * Propagation row:
 * - activity
 * - lock = literal
 * - nterms = number of monomials
 * - mono = array of monomials of size (nterms + 1)
 *   mono[nterms] is an end marker, as in polynomials.h
 */
typedef struct prop_row_s {
  float activity;
  literal_t lock;
  uint32_t nterms;
  monomial_t mono[0];
} prop_row_t;


/*
 * Propagation table = array of prop rows
 * - for each variable x, we keep track of the rows where x occurs
 * - nrows = total number of rows (includes NULL rows)
 * - nvars = number of variables
 * - row_size = size of the row and mark arrays
 * - var_size = size of the column array
 * - row[i] = propagation row
 * - mark = bitvector for marking rows
 * - col[x] = column = array of indices of rows where x occurs
 *   (col[x] is an index_vector object so its size is stored in a hidden header)
 *
 * When row i is deleted, we set row[i] = NULL and we store i into a vector
 * (to be reused later).
 *
 * To deal with activities
 * - act_inc = activity increment
 * - inv_act_decay = inverse of the activity decay factor (e.g., 1/0.99)
 */
typedef struct prop_table_s {
  uint32_t nrows;
  uint32_t nvars;
  uint32_t row_size;
  uint32_t var_size;
  prop_row_t **row;
  byte_t *mark;
  int32_t **col;
  // activities
  float act_increment;
  float inv_act_decay;
  // vector of empty row indices
  ivector_t free_rows;
} prop_table_t;


// Maximal and default sizes
#define DEF_PROPTABLE_ROW_SIZE 50
#define DEF_PROPTABLE_VAR_SIZE 100
#define MAX_PROPTABLE_ROW_SIZE (UINT32_MAX/8)
#define MAX_PROPTABLE_VAR_SIZE (UINT32_MAX/8)

// Initial size of the free_rows vector
#define PROPTABLE_FREE_ROWS_SIZE  20

// Default values of activity-increment and relatives
#define PROPTABLE_DECAY_FACTOR      (0.999F)
#define PROPTABLE_ACT_INCREMENT     (1.0F)
#define PROPTABLE_ACT_THRESHOLD     (1e20F)
#define PROPTABLE_INV_ACT_THRESHOLD (1e-20F)

// Maximal number of terms in a propagation row (not counting end marker)
#define MAX_PROP_ROW_SIZE ((uint32_t)(((UINT32_MAX-sizeof(prop_row_t))/sizeof(monomial_t))-1))



/*
 * Encoding of rows in the col[x] array:
 * - every integer d in col[x] encodes a row index k
 *  + the sign of the coefficient of x in that row
 * - the sign is stored in the low-order bit of d
 *   (0 means positive, 1 means negative)
 * - the row index is the rest of d
 */

// index for row i, positive sign
static inline int32_t pos_row_idx(uint32_t i) {
  assert(i < MAX_PROPTABLE_ROW_SIZE);
  return (int32_t)(i << 1);
}

// index for row i, negative sign
static inline int32_t neg_row_idx(uint32_t i) {
  assert(i < MAX_PROPTABLE_ROW_SIZE);
  return (int32_t)((i<<1) | 1);
}

// extract the row from index d
static inline uint32_t row_of_row_idx(int32_t d) {
  return (uint32_t)(d>>1);
}

// get the sign bit from index d: 0 if positive, 1 if negative
static inline uint32_t sign_of_row_idx(int32_t d) {
  return (uint32_t)(d & 1);
}

// check the sign of index d
static inline bool is_pos_row_idx(int32_t d) {
  return (uint32_t)(d & 1) == 0;
}

static inline bool is_neg_row_idx(int32_t d) {
  return (uint32_t)(d & 1) != 0;
}





/*
 * TABLE OPERATIONS
 */

/*
 * Initialize a propagation table
 * - n = initial row capacity. If n == 0, the default is used.
 * - m = initial var capacity. If m == 0, the default is used.
 * - nrows and nvars are initialized to 0.
 */
extern void init_prop_table(prop_table_t *table, uint32_t n, uint32_t m);


/*
 * Set the number of variables to m
 * - no changes if prop->nvars >= m
 * - otherwise, the column vector is made large enough for m variables
 * - for all new variables, col[x] is initialized to NULL
 */
extern void prop_table_set_numvars(prop_table_t *table, uint32_t m);


/*
 * Delete the table: free all memory
 */
extern void delete_prop_table(prop_table_t *table);


/*
 * Empty the table: delete all rows and columns
 * - reset nvars and nrows to 0
 * - do not delete arrays row, mark, and col
 */
extern void reset_prop_table(prop_table_t *table);




/*
 * ROW ADDITION/ACTIVITY
 */

/*
 * Return row of index i
 */
static inline prop_row_t *prop_row(prop_table_t *table, uint32_t i) {
  assert(i < table->nrows);
  return table->row[i];
}


/*
 * Mark row i
 */
static inline void mark_prop_row(prop_table_t *table, uint32_t i) {
  assert(i < table->nrows);
  set_bit(table->mark, i);
}


/*
 * Clear mark of row i
 */
static inline void unmark_prop_row(prop_table_t *table, uint32_t i) {
  assert(i < table->nrows);
  clr_bit(table->mark, i);
}


/*
 * Check whether row i is marked
 */
static inline bool prop_row_is_marked(prop_table_t *table, uint32_t i) {
  assert(i < table->nrows);
  return tst_bit(table->mark, i);
}


/*
 * Get the number of non-null rows
 */
static inline uint32_t num_prop_rows(prop_table_t *table) {
  return table->nrows - table->free_rows.size;
}




/*
 * Copy row (from a matrix) into table
 * - the table is resized if necessary (to add variables)
 * - the row is added to the column vector of all its variables
 * - its activity is set to table->act_increment
 */
extern void prop_table_add_row(prop_table_t *table, row_t *row);

/*
 * Decay activities
 * - multiply table->act_increment by table->inv_act_decay
 */
static inline void prop_table_decay_activities(prop_table_t *table) {
  table->act_increment *= table->inv_act_decay;
}


/*
 * Increase the activity of row i
 * - rescale all row activities if that goes above the max activity threshold
 */
extern void prop_table_increase_row_activity(prop_table_t *table, uint32_t i);


/*
 * Reduce the table: remove all unmarked rows of low activity
 * - marked rows are not deleted irrespective of their activity
 */
extern void prop_table_reduce(prop_table_t *table);



#endif /* __SIMPLEX_PROP_TABLE_H */
