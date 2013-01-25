/*
 * TABLE OF ATOMS FOR ARITHMETIC SOLVERS
 */

/*
 * The atoms can be of the form (x >= k) or (x <= k) or (x == k),
 * where x is a variable in the arithmetic solver and k is a rational
 * constant. Each atom is identified by an index in the table.
 * The table uses hash consing and it supports removal of atoms for push/pop 
 * operations. 
 *
 * The components of an atom are:
 * - a 2bit tag to specify which type of atom it is (>=, <=, or ==)
 * - the variable x (30bits index)
 * - the rational constant k
 * - a boolean variable (mapped to the atom in the smt-core)
 *
 * The table also maintains a list of unassigned atoms (doubly-linked list).
 * This is similar to what's used in idl_floyd_warshal and rdl_floyd_warshal.
 */

#ifndef __ARITH_ATOMTABLE_H
#define __ARITH_ATOMTABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bitvectors.h"
#include "int_hash_tables.h"
#include "smt_core.h"
#include "rationals.h"
#include "egraph_base_types.h"


/*
 * Tags for atom types
 */
typedef enum arithatm_tag {
  GE_ATM = 0x00,  // x >= k
  LE_ATM = 0x01,  // x <= k
  EQ_ATM = 0x02,  // x == k
} arithatm_tag_t;


/*
 * Atom structure
 * - header = variable index + tag
 * - boolvar = boolean variable
 * - bound = constant
 */
typedef struct arith_atom_s {
  uint32_t header;
  bvar_t boolvar;
  rational_t bound;
} arith_atom_t;



/*
 * Access to variable and tag, and other atom components
 */
static inline thvar_t var_of_atom(arith_atom_t *atom) {
  return (thvar_t) (atom->header >> 2);
}

static inline arithatm_tag_t tag_of_atom(arith_atom_t *atom) {
  return (arithatm_tag_t) (atom->header & 0x3);
}

static inline bool atom_is_ge(arith_atom_t *atm) {
  return tag_of_atom(atm) == GE_ATM;
}

static inline bool atom_is_le(arith_atom_t *atm) {
  return tag_of_atom(atm) == LE_ATM;
}

static inline bool atom_is_eq(arith_atom_t *atm) {
  return tag_of_atom(atm) == EQ_ATM;
}

static inline bvar_t boolvar_of_atom(arith_atom_t *atom) {
  return atom->boolvar;
}

static inline rational_t *bound_of_atom(arith_atom_t *atom) {
  return &atom->bound;
}



/*
 * Build header for variable x and tag
 */
static inline uint32_t arithatom_mk_header(int32_t x, arithatm_tag_t tag) {
  assert(tag == GE_ATM || tag == LE_ATM || tag == EQ_ATM);
  assert(0 <= x && x < UINT32_MAX/4);
  return (((uint32_t) x) << 2) | ((uint32_t) tag);
}


/*
 * Conversions between void* pointers and atom indices
 * - an atom index is packed into a void * pointer, with a two-bit tag 
 *   to indicate that this is  an arithmetic atom (cf. egraph_types.h)
 * - there's no loss of data even if pointers are 32 bits (because
 *   the tag is 2bits and i is less than MAX_ARITHATOMTABLE_SIZE (i.e., 2^32/16)
 */
static inline void *arithatom_idx2tagged_ptr(int32_t i) {
  return tagged_arith_atom((void *)((size_t) (i << 2)));
}

static inline int32_t arithatom_tagged_ptr2idx(void *p) {
  return (int32_t)(((size_t) p) >> 2);
}



/*
 * Element of a doubly-linked list of atom indices
 */
typedef struct arith_listelem_s {
  int32_t pre;
  int32_t next;  
} arith_listelem_t;


/*
 * Atom table
 * - size = size of the atom array
 * - natoms = number of atoms created
 * - atoms = atom array
 * - free_list = array of natoms+1 list elements (indexed from -1 to natoms-1)
 *   the free_list has full size = size + 1 but only the first natoms elements are used
 * - mark = one bit per atom
 *   if mark = 1 the atom is assigned (not in the free list)
 *   if mark = 0 the atom is unassigned (in the free list)
 */
typedef struct arith_atomtable_s {
  uint32_t size;
  uint32_t natoms;
  arith_atom_t *atoms;
  arith_listelem_t *free_list;
  byte_t *mark;

  // pointer to the smt_core object
  smt_core_t *core;

  // table for hash consing
  int_htbl_t htbl;

  // auxiliary rational buffer
  rational_t aux;
} arith_atomtable_t;


/*
 * The table can store as many as (UINT32_MAX/16) atoms,
 * which should be way more than what we can deal with.
 */
#define DEF_ARITHATOMTABLE_SIZE 100
#define MAX_ARITHATOMTABLE_SIZE (UINT32_MAX/sizeof(arith_atom_t))



/*
 * Initialization:
 * - all data structures are allocated with their default initial size
 * - core = smt_core attached to the arithmetic solver.
 */
extern void init_arith_atomtable(arith_atomtable_t *table, smt_core_t *core);


/*
 * Deletion: free all allocated memory (delete all atoms)
 */
extern void delete_arith_atomtable(arith_atomtable_t *table);


/*
 * Reset: empty the table: delete all atoms
 */
extern void reset_arith_atomtable(arith_atomtable_t *table);


/*
 * Support for pop: remove all atoms of index >= natoms
 */
extern void arith_atomtable_remove_atoms(arith_atomtable_t *table, uint32_t natoms);





/*
 * READ TABLE CONTENT
 */

/*
 * Get atom descriptor for atom i
 */
static inline arith_atom_t *arith_atom(arith_atomtable_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms);
  return table->atoms + i;
}

/*
 * Get the index of atom a
 */
static inline int32_t arith_atom_id(arith_atomtable_t *table, arith_atom_t *a) {
  assert(table->atoms <= a && a < table->atoms + table->natoms);
  return (int32_t)(a - table->atoms);
}

/*
 * Number of atoms
 */
static inline uint32_t num_arith_atoms(arith_atomtable_t *table) {
  return table->natoms;
}


/*
 * Get atom index for boolean var v
 * - return -1 if there's no atom for v or the atom is not arithmetic
 */
extern int32_t arith_atom_id_for_bvar(arith_atomtable_t *table, bvar_t v);


/*
 * Get atom descriptor for boolean variable v
 * - return NULL if there's no atom for v or the atom is not arithmetic
 */
extern arith_atom_t *arith_atom_for_bvar(arith_atomtable_t *table, bvar_t v);



/*
 * MARKS AND FREE LIST
 */

/*
 * Check whether atom i is marked
 */
static inline bool arith_atom_is_marked(arith_atomtable_t *table, int32_t i) {
  assert(0 <= i && i < table->natoms);
  return tst_bit(table->mark, i);
}

static inline bool arith_atom_is_unmarked(arith_atomtable_t *table, int32_t i) {
  return ! arith_atom_is_marked(table, i);
}

#define USE_FREE_LIST 0

#if USE_FREE_LIST 

/*
 * Mark atom i and remove it from the free list
 * - the atom must be unmarked
 */
extern void mark_arith_atom(arith_atomtable_t *table, int32_t i);

/*
 * Put atom i back into the free list and clear its mark
 * IMPORTANT: i must be the last marked atom 
 * (marking/unmarking must be done in LIFO order)
 */
extern void unmark_arith_atom(arith_atomtable_t *table, int32_t i);


/*
 * Get the first element in the free list, (or -1 if the list is empty)
 */
static inline int32_t first_free_arith_atom(arith_atomtable_t *table) {
  return table->free_list[-1].next;
}

/*
 * Successor of i in the free list (-1 if i is the last element)
 */
static inline int32_t next_free_arith_atom(arith_atomtable_t *table, int32_t i) {
  return table->free_list[i].next;
}


#else 


/*
 * Mark atom i
 * - the atom must be unmarked
 */
static inline void mark_arith_atom(arith_atomtable_t *table, int32_t i) {
  assert(arith_atom_is_unmarked(table, i));
  set_bit(table->mark, i);
}

/*
 * Put atom i back into the free list and clear its mark
 * IMPORTANT: i must be the last marked atom 
 * (marking/unmarking must be done in LIFO order)
 */
static inline void unmark_arith_atom(arith_atomtable_t *table, int32_t i) {
  assert(arith_atom_is_marked(table, i));
  clr_bit(table->mark, i);
}

#endif



/*
 * ATOM CONSTRUCTION
 */

/*
 * Search for an atom (x op k) where op is one of GE_ATM, LE_ATM, EQ_ATM
 * - return -1 if there's no such atom, otherwise, return the atom index
 */
extern int32_t find_arith_atom(arith_atomtable_t *table, thvar_t x, arithatm_tag_t op, rational_t *k);

/*
 * Search for atom (x op k)
 * - create a new atom if it's not in the table
 * - return the atom index 
 * - set new_atom to true if the result is a new atom, to false otherwise
 *
 * If a new atom is created, it's attached to the core and it's assigned to 
 * a fresh boolean variable.
 */
extern int32_t get_arith_atom(arith_atomtable_t *table, thvar_t x, arithatm_tag_t op, rational_t *k, bool *new_atom);

/*
 * Variants: return a literal, create a new atom if needed
 * - is_int indicates whether x is an integer variable
 * If x is an integer variable, then k must be an integer,
 * and atom (x <= k) is rewritten to not (x >= k+1)
 *
 * Returned atom index in *new_idx:
 * - *new_idx = -1 if the atom was already present in the table
 * - if a new atom is created, *new_idx is set to that atom's index
 */
extern literal_t get_literal_for_eq_atom(arith_atomtable_t *table, thvar_t x, rational_t *k, int32_t *new_idx);
extern literal_t get_literal_for_ge_atom(arith_atomtable_t *table, thvar_t x, bool is_int, rational_t *k, int32_t *new_idx);
extern literal_t get_literal_for_le_atom(arith_atomtable_t *table, thvar_t x, bool is_int, rational_t *k, int32_t *new_idx);



#endif /* __ARITH_ATOMTABLE_H */
