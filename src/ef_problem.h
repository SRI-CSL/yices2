/*
 * INPUT TO THE EXISTS/FORALL SOLVER
 */

/*
 * Data structure to store an exist/forall problem.
 * The basic form is 
 *
 *    A(x) AND (FORALL y: B(y) => C(x, y))
 *
 * and the goal is to find x that satisfies this constraint.
 *
 * Generalization:
 * - A(x) is a conjunction: A_1(x) .... A_n(x)
 * - several universal constraints:
 *     (forall y_1: B_1(y_1) => C_1(x, y_1))
 *       ...
 *     (forall y_t: B_t(y_t) => C_t(x, y_t))
 *
 * To represent such problems, we store:
 * - the set of all existential variables
 * - the set of all universal variables (the union of y_1 ... y_t)
 * - the of all constraints on x (A_1(x) ... A_n(x))
 * - a descriptor for each forall constraint
 *
 * For a constraint (forall y: B(y) => C(x, y)), the descriptor includes* 
 * - the set of existential variables occurring in C (i.e., a subset of x)
 * - the set of universal variables occurring in B or C
 * - the assumption B(y)
 * - the guarantee C(x, y)
 *
 * To store sets of terms: we use the index_vector data structure
 * (cf. index_vectors.h).
 */

#ifndef __EFINPUT_H
#define __EFINPUT_H

#include <stdint.h>

#include "terms.h"


/*
 * Descriptor for a forall constraint
 */
typedef struct forall_cnstr_s {
  term_t *evars;     // existential variables 
  term_t *uvars;     // universal variables
  term_t assumption; // B(y)
  term_t guarantee;  // C(x, y)
} forall_cnstr_t;


/*
 * Descriptor for the full problem
 */
typedef struct ef_prob_s {
  term_t *all_evars;      // existential variables
  term_t *all_uvars;      // universal variables
  term_t *conditions;     // constraints on x = A_1(x), ..., A_n(x)
  uint32_t num_cnstr;     // number of forall constraints
  uint32_t cnstr_size;    // size of array cnstr
  forall_cnstr_t *cnstr;  // array of constraint descriptors
} ef_prob_t;



/*
 * Initialization: all empty
 */
extern void init_ef_prob(ef_prob_t *prob);

/*
 * Reset to empty
 */
extern void reset_ef_prob(ef_prob_t *prob);

/*
 * Delete the whole thing
 */
extern void delete_ef_prob(ef_prob_t *prob);


/*
 * Add v[0...n-1] to all_evars or all_uvars (remove duplicates)
 */
extern void ef_prob_add_evars(ef_prob_t *prob, term_t *v, uint32_t n);
extern void ef_prob_add_uvars(ef_prob_t *prob, term_t *v, uint32_t n);

/*
 * Add t as a constraint on x
 */
extern void ef_prob_add_condition(ef_prob_t *prob, term_t t);

/*
 * Add a forall constraint:
 * - ev = existential variables, nev = size of the ev array
 * - uv = universal variables, nuv = size of the uv array
 * - assumption = formula on uv
 * - guarantee = formula on uv and ev
 *
 * The global arrays all_evars and all_uvars are updated:
 * - all_evars := all_evars union ev
 * - all_uvars := all_uvars union uv
 */
extern void ef_prob_add_constraint(ef_prob_t *prob, term_t *ev, uint32_t nev, term_t *uv, uint32_t nuv,
				   term_t assumption, term_t guarantee);



/*
 * Number of existential/universal variables
 */
extern uint32_t ef_prob_num_evars(ef_prob_t *prob); // size of all_evars
extern uint32_t ef_prob_num_uvars(ef_prob_t *prob); // size of all_uvars


/*
 * Number of conditions
 */
extern uint32_t ef_prob_num_conditions(ef_prob_t *prob);


#endif /* __EFINPUT_H */
