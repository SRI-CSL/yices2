/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TABLE OF ATOMS FOR THE BITVECTOR SOLVER
 */

/*
 * Bit vector atoms are of three kinds:
 * - bveq x y
 * - bvge x y: x <= y, where x and y are interpreted
 *   as unsigned integers
 * - bvsge x y: x <= y, where x and y are as signed
 *   integers
 */

#ifndef __BV_ATOMTABLE_H
#define __BV_ATOMTABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/int_hash_tables.h"
#include "solvers/egraph/egraph_base_types.h"


/*
 * Tags for atom types
 * - each atom maps an external boolean variable (in the core)
 *   to a constraint on two variables x and y.
 * - there are three kinds of atoms: eq, ge, sge
 */
typedef enum bvatm_tag {
  BVEQ_ATM,     // (x == y)
  BVUGE_ATM,    // (x >= y) unsigned
  BVSGE_ATM,    // (x >= y) signed
} bvatm_tag_t;



/*
 * ATOMS
 */

/*
 * Atom structure:
 * - the header encodes the tag + a mark
 * - lit is a literal in the core.
 *   if lit == true_literal, the atom is true at the toplevel
 *   if lit == false_literal, the atom is false at the toplevel
 *   otherwise the atom is attached to a boolean variable v
 *   in the core and lit is pos_lit(v).
 * - left/right are x and y
 */
typedef struct bvatm_s {
  uint32_t header;
  literal_t lit;
  thvar_t left;
  thvar_t right;
} bvatm_t;



/*
 * Access to tag and mark
 * - the two low order bits of the header contain the tag
 * - the next bit is the mark
 */
static inline bvatm_tag_t bvatm_tag(bvatm_t *atm) {
  return (bvatm_tag_t) (atm->header & 0x3);
}

static inline bool bvatm_is_eq(bvatm_t *atm) {
  return bvatm_tag(atm) == BVEQ_ATM;
}

static inline bool bvatm_is_ge(bvatm_t *atm) {
  return bvatm_tag(atm) == BVUGE_ATM;
}

static inline bool bvatm_is_sge(bvatm_t *atm) {
  return bvatm_tag(atm) == BVSGE_ATM;
}

static inline bool bvatm_is_marked(bvatm_t *atm) {
  return (atm->header & 0x4) != 0;
}

static inline void bvatm_set_mark(bvatm_t *atm) {
  atm->header |= 0x4;
}


/*
 * Boolean variable of atm
 * - if lit == null_literal, return null_bvar
 */
static inline bvar_t bvatm_bvar(bvatm_t *atm) {
  return var_of(atm->lit);
}


/*
 * Conversions between void* pointers and atom indices
 * - an atom index is packed into a void * pointer, with a two-bit tag
 *   to indicate that it's an bitvector atom (cf. egraph_base_types.h)
 * - there's no loss of data even if pointers are 32 bits (because
 *   the tag is 2bits and i is less than MAX_BVATOMTABLE_SIZE (i.e., 2^32/16)
 */
static inline void *bvatom_idx2tagged_ptr(int32_t i) {
  return tagged_bv_atom((void *)((size_t) (i << 2)));
}

static inline int32_t bvatom_tagged_ptr2idx(void *p) {
  return (int32_t)(((size_t) p) >> 2);
}




/*
 * ATOM TABLE
 */

/*
 * Atom descriptors are stored in array data
 * - natoms = number of atoms
 * - size = size of the data array
 */
typedef struct bv_atomtable_s {
  uint32_t natoms;
  uint32_t size;
  bvatm_t *data;

  int_htbl_t htbl;  // for hash consing
} bv_atomtable_t;


#define DEF_BVATOMTABLE_SIZE 100
#define MAX_BVATOMTABLE_SIZE (UINT32_MAX/sizeof(bvatm_t))




/*
 * OPERATIONS
 */

/*
 * Initialization
 * - use the default size
 * - the table is initially empty
 */
extern void init_bv_atomtable(bv_atomtable_t *table);


/*
 * Delete the table
 */
extern void delete_bv_atomtable(bv_atomtable_t *table);


/*
 * Empty the table
 */
extern void reset_bv_atomtable(bv_atomtable_t *table);


/*
 * Remove all atoms of index >= na
 */
extern void bv_atomtable_remove_atoms(bv_atomtable_t *table, uint32_t na);


/*
 * Constructors
 * - get_bv_atom(table, op, x, y): check whether atom (op x y) exists.
 *   If it does not create a new atom, with literal set to null_literal.
 *   Return the atom index.
 * - get_bveq_atom normalizes (eq x y) then calls get_bv_atom.
 */
extern int32_t get_bv_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y);
extern int32_t get_bveq_atom(bv_atomtable_t *table, thvar_t x, thvar_t y);

static inline int32_t get_bvuge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return get_bv_atom(table, BVUGE_ATM, x, y);
}

static inline int32_t get_bvsge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return get_bv_atom(table, BVSGE_ATM, x, y);
}


/*
 * Search for an atom
 * - return the atom id if it exists
 * - return -1 otherwise
 */
extern int32_t find_bv_atom(bv_atomtable_t *table, bvatm_tag_t op, thvar_t x, thvar_t y);
extern int32_t find_bveq_atom(bv_atomtable_t *table, thvar_t x, thvar_t y);

static inline int32_t find_bvuge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return find_bv_atom(table, BVUGE_ATM, x, y);
}

static inline int32_t find_bvsge_atom(bv_atomtable_t *table, thvar_t x, thvar_t y) {
  return find_bv_atom(table, BVSGE_ATM, x, y);
}




/*
 * Get the descriptor of atom i
 */
static inline bvatm_t *bvatom_desc(bv_atomtable_t *atbl, int32_t i) {
  assert(0 <= i && i < atbl->natoms);
  return atbl->data + i;
}




#endif /* __BV_ATOMTABLE_H */
