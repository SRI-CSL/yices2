/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include "terms/bv_constants.h"
#include "terms/term_utils.h"
#include "mcsat/bv/bv_explainer.h"

/**
   BV arithmetic intervals
**/

// Type for bvconstant intervals. An interval is a set of consecutive numbers modulo 2^n:
// [ 3; 1 [ is not empty but contains 3 and 0.
// Upper bound is always *excluded* from interval.
// Convention: the type cannot construct empty intervals: [ a ; a [ is the full set.

typedef struct {
  bvconstant_t lo;
  bvconstant_t hi;
  bvconstant_t length; // always hi - lo -1 (so technically it's not the length, but otherwise the full interval would have length 0, so now it has length -1, i.e. maximal)
  term_t lo_term;
  term_t hi_term; 
  term_t reason; // reason for being the full interval (NULL_TERM if not)
  ivector_t reasons; // other reasons for the interval to reflect its original constraint
  term_t var;  // The variable whose values are forbidden to be in this interval
} interval_t;

static inline
uint32_t get_bitwidth(interval_t* i){
  return i->lo.bitsize;
}

static inline
bool is_full(interval_t* i){
  return bvconstant_eq(&i->lo,&i->hi);
}

void bv_interval_delete(interval_t* i);

// delete + free
void bv_interval_destruct(interval_t* i);

void bv_interval_print(FILE* out, term_table_t* terms, interval_t* i);

// Comparing bv_constants, with a baseline that serves as the zero
bool bvconst_le_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline);
bool bvconst_lt_base(const bvconstant_t* a, const bvconstant_t* b, const bvconstant_t* baseline);

// Determines if interval i contains value a. Happens if (a - i->lo) < (i->hi - i->lo)
bool bv_interval_is_in(const bvconstant_t* a, const interval_t* i);

// Comparing two intervals: first look at bitwidth, then lower bound, then span.
// When lower bounds are compared, an optional baseline can be provided, in data,
// which must have the same bitwidth as x and y.
bool bv_interval_cmp(void *data, void *x, void *y);

// inhabits output
void bv_interval_construct(bv_subexplainer_t* exp,
                           const bvconstant_t* lo,
                           const bvconstant_t* hi,
                           term_t lo_term,
                           term_t hi_term,
                           term_t var,
                           term_t reason,
                           interval_t* output);

// Returns a newly constructed interval on the heap
interval_t* bv_interval_mk(bv_subexplainer_t* exp,
                           const bvconstant_t* lo,
                           const bvconstant_t* hi,
                           term_t lo_term,
                           term_t hi_term,
                           term_t var,
                           term_t reason);

// Returns a newly constructed full interval on the heap
interval_t* bv_interval_full_mk(bv_subexplainer_t* exp, term_t reason, uint32_t width);
