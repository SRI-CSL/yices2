/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONDITIONALS
 */

/*
 * By a conditional, we mean a generalization of if-then-else to
 * multiple conditions. Something semantically equivalent to
 *
 *   if c1 then t1
 *   if c2 then t2
 *    ...
 *   if c_n then t_n
 *   else t_0
 *
 * provided the conditions c_1 ... c_n are pairwise disjoint (i.e.
 * for any i/=j, c_i /\ c_j is false). This is a common pattern
 * that's normally written using nested if-then-elses.
 *
 * Converting a nested if-then-else to a conditional leads to
 * a nicer conversion to CNF.
 */

#ifndef __CONDITIONALS_H
#define __CONDITIONALS_H


#include <stdint.h>

#include "terms/terms.h"


/*
 * Data structure to represent conditionals
 * - terms = pointer to the relevant term table
 * - nconds = number of pairs [c_i, t_i]
 * - size = size of the pair array
 * - defval = default value = t_0
 * - array of pairs condition, value
 *   where both conditions and value are terms
 */
typedef struct cond_pair_s {
  term_t cond;
  term_t val;
} cond_pair_t;

typedef struct conditional_s {
  term_table_t *terms;
  cond_pair_t *pair;
  term_t defval;
  uint32_t nconds;
  uint32_t size;
} conditional_t;

#define DEF_CONDITIONAL_SIZE 10
#define MAX_CONDITIONAL_SIZE (UINT32_MAX/sizeof(cond_pair_t))


/*
 * Initialize:
 * - empty pair array
 * - defval = NULL_TERM
 */
extern void init_conditional(conditional_t *d, term_table_t *terms);

/*
 * Delete: free the array
 */
extern void delete_conditional(conditional_t *d);

/*
 * Reset: reset defval to NULL_TERM and nconds to 0, but don't
 * delete the array
 */
extern void reset_conditional(conditional_t *d);



/*
 * Convert term t to a conditional; store the result in d
 * - d is reset first
 * - t must be a valid term defined in d->terms
 * - if t is not an if-then-else term, the result is
 *     d->nconds = 0
 *     d->defval = t
 * - if t is (ite c a b) then the conversion depends on whether
 *   a or b is an if-then-else term.
 */
extern void convert_term_to_conditional(conditional_t *d, term_t t);


/*
 * Variant: convert (if c a b) to a conditional
 */
extern void convert_ite_to_conditional(conditional_t *d, term_t c, term_t a, term_t b);



#endif /* __CONDITIONALS_H */
