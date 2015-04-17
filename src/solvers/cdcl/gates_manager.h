/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * ENCODING OF BOOLEAN OPERATORS IN CLAUSAL FORM
 */

/*
 * This module is used to build auxiliary literal definition:
 * For example, to create l0 = (OR l1 ...  l_n)
 * - the module simplifies (OR l1 ... l_n)
 * - then it creates a fresh boolean l0 = pos_lit(v0)
 * - and it asserts clauses equivalent to "l0 = (OR ....)"
 * Hash consing is used to avoid duplications
 */

#ifndef __GATES_MANAGER_H
#define __GATES_MANAGER_H

#include "solvers/cdcl/gates_hash_table.h"
#include "solvers/cdcl/smt_core.h"
#include "utils/int_vectors.h"


/*
 * Manager = smt_core + hash table + an internal literal buffer
 */
typedef struct gate_manager_s {
  smt_core_t *core;
  gate_table_t htbl;
  ivector_t buffer;
} gate_manager_t;


/*
 * Hash consing bound: hash consing is not used for
 * operators with more than MAX_HASHCONS_SIZE input parameters
 * MAX_HASHCONS_SIZE must be no more than MAX_INDEGREE
 */
#define MAX_HASHCONS_SIZE 50



/***********************************
 *  INITIALIZATION/PUSH/POP/RESET  *
 **********************************/

/*
 * Initialization:
 * - htbl is initialized to its default size
 * - core must be initialized outside this function
 */
extern void init_gate_manager(gate_manager_t *m, smt_core_t *core);

/*
 * Deletion: doesn't delete the core, just the hash table
 */
extern void delete_gate_manager(gate_manager_t *m);


/*
 * Push/pop/reset just apply to the internal gate table
 */
static inline void gate_manager_push(gate_manager_t *m) {
  gate_table_push(&m->htbl);
}

static inline void gate_manager_pop(gate_manager_t *m) {
  gate_table_pop(&m->htbl);
}

static inline void reset_gate_manager(gate_manager_t *m) {
  reset_gate_table(&m->htbl);
}




/***********************
 *  GATE CONSTRUCTION  *
 **********************/

/*
 * AND, OR, XOR, IFF, IMPLIES constructors
 *
 * The generic constructors take an array of n literals a[0 ... n-1] as input
 * - they do the right thing if n=0 or n=1
 * - short-cuts are provided for n=2 and n=3
 * - the constructors do not modify array a
 */
extern literal_t mk_or_gate(gate_manager_t *m, uint32_t n, literal_t *a);
extern literal_t mk_and_gate(gate_manager_t *m, uint32_t n, literal_t *a);
extern literal_t mk_xor_gate(gate_manager_t *m, uint32_t n, literal_t *a);

// two-arguments
extern literal_t mk_or_gate2(gate_manager_t *m, literal_t l1, literal_t l2);
extern literal_t mk_and_gate2(gate_manager_t *m, literal_t l1, literal_t l2);
extern literal_t mk_xor_gate2(gate_manager_t *m, literal_t l1, literal_t l2);

// three-arguments
extern literal_t mk_or_gate3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3);
extern literal_t mk_and_gate3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3);
extern literal_t mk_xor_gate3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3);

// iff and implies are derived from xor and or
static inline literal_t mk_iff_gate(gate_manager_t *m, literal_t l1, literal_t l2) {
  return mk_xor_gate2(m, not(l1), l2);
}

static inline literal_t mk_implies_gate(gate_manager_t *m, literal_t l1, literal_t l2) {
  return mk_or_gate2(m, not(l1), l2);
}

/*
 * returns l0 == (ITE c l1 l2)
 */
extern literal_t mk_ite_gate(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2);


/*
 * Direct assertions for the following constraints
 *  (XOR l1  ... ln ) == v
 *  (XOR l1 l2) == v
 *  (XOR l1 l2 l3) == v
 *  (IFF l1 l2) == v
 *  (ITE c l1 l2) == v
 * where v is true or false
 */
extern void assert_xor(gate_manager_t *m, uint32_t n, literal_t *a, bool v);
extern void assert_xor2(gate_manager_t *m, literal_t l1, literal_t l2, bool v);
extern void assert_xor3(gate_manager_t *m, literal_t l1, literal_t l2, literal_t l3, bool v);

extern void assert_ite(gate_manager_t *m, literal_t c, literal_t l1, literal_t l2, bool v);

static inline void assert_iff(gate_manager_t *m, literal_t l1, literal_t l2, bool v) {
  assert_xor2(m, l1, l2, ! v);
}




#endif /* __GATES_MANAGER_H */
