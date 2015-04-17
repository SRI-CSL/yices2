/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TABLE OF VARIABLES FOR ARITHMETIC SOLVERS
 */

/*
 * This table maps theory variables within an arithmetic
 * solver to their definition, and to the attached eterm if any.
 * It provides hash-consing and it supports removal of variables for pop.
 * The table is intended primarily for the Simplex solver,
 * but it should be usable by future variants.
 *
 * The table also maintains a variable assignment (i.e., a mapping from
 * variables to extended_rationals), and it keeps track of the current
 * lower and upper bound on all variables. These bounds are identified
 * by an integer index (i.e., an index into a global queue where asserted
 * and derived bounds are pushed).
 *
 * More precisely, for each arithmetic variable v, the table stores
 * - the definition of v, which can be
 *     either NULL
 *     or a pointer to a polynomial_t object
 *     or a pointer to a pprod_t object (for non-linear arithmetic)
 *     or a pointer to a rational_t object
 * - whether v is an integer or a real variable
 * - the egraph term attached to v (or null_eterm if there's none)
 * - a vector of atoms indices (all the atoms whose variable is v)
 * - the value of v in the current assignment
 * - the index of lower/upper bounds on v
 */

#ifndef __ARITH_VARTABLE_H
#define __ARITH_VARTABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/egraph/egraph_base_types.h"
#include "terms/extended_rationals.h"
#include "terms/polynomials.h"
#include "terms/power_products.h"
#include "utils/bitvectors.h"
#include "utils/index_vectors.h"
#include "utils/int_hash_tables.h"


/********************
 *  VARIABLE FLAGS  *
 *******************/

/*
 * For each variable x we keep data used during assignment updates,
 * and other simplex operations.
 * - whether value[x] is equal to the lower bound on x
 * - whether value[x] is equal to the upper bound on x
 * - a generic 1bit mark
 *
 * This data is stored into an 8bit variable tag
 * - bit 0: mark
 * - bit 1: x == lower bound
 * - bit 2: x == upper bound
 *
 * The mark bit is currently used only in simplex make_feasible
 * - variable x is marked if it was the leaving variable in a pivoting step
 * - this is used to switch to Blend's rule after too many variables
 *   leave the basis
 *
 * Other bits in this tag store information about x's type and
 * definition:
 * - bit 3 is 1 is x is an integer variable, 0 otherwise
 * - bit 4 and 5 specify how to interpret def[x]:
 *    00 --> x is a variable (def[x] = NULL)
 *    01 --> def[x] is a polynomial
 *    10 --> def[x] is a power product
 *    11 --> def[x] is a rational constant
 */

#define AVARTAG_MARK_MASK  ((uint8_t) 0x1)
#define AVARTAG_ATLB_MASK  ((uint8_t) 0x2)
#define AVARTAG_ATUB_MASK  ((uint8_t) 0x4)
#define AVARTAG_INT_MASK    ((uint8_t) 0x8)

#define AVARTAG_KIND_MASK   ((uint8_t) 0x30)


/*
 * Variable kinds: 00 to 11
 */
typedef enum {
  AVAR_FREE = 0,  // 0b00
  AVAR_POLY = 1,  // 0b01
  AVAR_PPROD = 2, // 0b10
  AVAR_CONST = 3, // 0b11
} avar_kind_t;


/*
 * Two bits stored in the kind field (bits 4 and 5)
 */
#define AVARTAG_KIND_FREE  ((uint8_t) 0x00)
#define AVARTAG_KIND_POLY  ((uint8_t) 0x10)
#define AVARTAG_KIND_PPROD ((uint8_t) 0x20)
#define AVARTAG_KIND_CONST ((uint8_t) 0x30)





/********************
 *  VARIABLE TABLE  *
 *******************/

/*
 * - nvars = number of variables
 * - ivars = number of integer variables
 * - size = size of all variable-indexed arrays
 * - def = array of tagged pointers = variable definition
 * - atoms = atom vector for each variable
 * - eterm = array of egraph terms
 *
 * - value = current assignment
 * - upper_index, lower_index = indices in the bound queue (-1) means no bound
 * - tag = variable tag
 */
typedef struct arith_vartable_s {
  uint32_t nvars;
  uint32_t ivars;
  uint32_t size;

  // variable definition and related data
  void **def;
  int32_t **atoms;
  eterm_t *eterm;
  uint8_t *tag;

  // assignment and bounds
  xrational_t *value;
  int32_t *lower_index;
  int32_t *upper_index;

  int_htbl_t htbl;   // for hash consing
} arith_vartable_t;


/*
 * Default and maximal size
 */
#define DEF_AVARTABLE_SIZE 100
#define MAX_AVARTABLE_SIZE (UINT32_MAX/sizeof(xrational_t))




/**********************
 *  TABLE OPERATIONS  *
 *********************/

/*
 * Initialization:
 * - the table is initialized with its default size
 * - the eterm array is not allocated here, but on the first
 *   call to attach_eterm.
 */
extern void init_arith_vartable(arith_vartable_t *table);


/*
 * Deletion: delete all internal tables and all polynomials/varprod objects
 */
extern void delete_arith_vartable(arith_vartable_t *table);


/*
 * Reset: empty the table, delete all polynomials and varprod objects
 */
extern void reset_arith_vartable(arith_vartable_t *table);


/*
 * Support for pop: delete all variables of index >= nvars
 */
extern void arith_vartable_remove_vars(arith_vartable_t *table, uint32_t nvars);


/*
 * Support for pop: remove all references to egraph terms of indices >= nterms.
 * - go through all variables x in the table.
 *   if eterm[x] is defined and >= nterms, then it's reset to null_eterm
 */
extern void arith_vartable_remove_eterms(arith_vartable_t *table, uint32_t nterms);


/*
 * Read the number of variables
 */
static inline uint32_t num_arith_vars(arith_vartable_t *table) {
  return table->nvars;
}


/*
 * Get the number of integer variables
 */
static inline uint32_t num_integer_vars(arith_vartable_t *table) {
  return table->ivars;
}


/*
 * Number of variables not marked as integer
 */
static inline uint32_t num_real_vars(arith_vartable_t *table) {
  return table->nvars - num_integer_vars(table);
}


/*
 * Collect the set of integer variables as a bit vector
 * - i.e., return a bitvector V of size n = table->nvars
 * - bit i of V is 1 if variable i has integer type.
 * - V must be deleted when no longer used by calling delete_bitvector(V)
 *   (cf. bitvectors.h)
 */
extern byte_t *get_integer_vars_vector(arith_vartable_t *table);



/*
 * VARIABLE CREATION
 */

/*
 * All new variables are created with the following default initialization:
 * - no eterm attached
 * - empty atom vector
 * - value = 0
 * - lower bound and upper bound indices = -1
 * - all flags are 0 (not marked, not at lower/upper bound)
 *
 * The kind and the integer bit set according to the definition
 */

/*
 * Create a new variable
 * - if is_int is true, the variable has integer type, otherwise it's a real variable
 * - the definition is NULL
 */
extern thvar_t create_arith_var(arith_vartable_t *table, bool is_int);


/*
 * Return a variable equal to rational q
 * - return null_thvar if there's no such variable in table
 */
extern thvar_t find_var_for_constant(arith_vartable_t *table, rational_t *q);


/*
 * Get a variable equal to rational q
 * - create a fresh variable if needed, and set new_var to true
 * - otherwise, set new_var to false
 */
extern thvar_t get_var_for_constant(arith_vartable_t *table, rational_t *q, bool *new_var);


/*
 * Find a variable whose definition is equal to polynomial p
 * - if there's no such variable, return null_thvar = -1
 * - p must be normalized and all its variables must exist in table
 * (i.e., p must have its variables sorted and it must be terminated by the end-marker max_idx)
 * - n must be the length of p, excluding the end marker
 */
extern thvar_t find_var_for_poly(arith_vartable_t *table, monomial_t *p, uint32_t n);


/*
 * Get a variable whose definition is equal to p
 * - create a fresh variable if there's no such variable in the table
 * - if a new variable is created, the flag *new_var is set to true,
 * - if an existing variable is returned, then *new_var is set false
 * - if p is an integer polynomial (all variables and coefficients are integer) then
 *   the fresh variable is an integer variable, otherwise it's a real variable.
 */
extern thvar_t get_var_for_poly(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var);


/*
 * Find a variable whose definition is equal to the non-constant part of p
 * - i.e., write p as k + q where k is the constant term, then find a variable for q
 */
extern thvar_t find_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n);


/*
 * Get a variable whose definition is equal to the non-constant part of p
 * - i.e., write p as k + q where k is the constant term, then get a variable for q
 *
 * NOTE: this is used to construct atoms: for example, atom (a + q >= 0)
 * can be internalized to (x >= -a) with x = var_for_poly_offset(a + q) = var for q
 */
extern thvar_t get_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var);


/*
 * Find a variable whose definition is equal to the product p
 * - if there's no such variable, return null_thvar = -1
 * - p = array of pairs (variable, exponents)
 * - n = number of pairs in p
 * - p must normalized (cf. power_products.h)
 *
 * IMPORTANT: p must have degree at least 2.
 * (i.e., p must not be the empty product, or the end marker,
 *        or reducible to a single variable).
 */
extern thvar_t find_var_for_product(arith_vartable_t *table, varexp_t *p, uint32_t n);


/*
 * Return a variable equal to product p. Create a new variable if needed.
 * - set *new_flag to true if a new variable is created
 *
 * IMPORTANT: As above, p must have degree at least 2.
 * (i.e., p must not be the empty product, or the end marker,
 *        or reducible to a single variable).
 */
extern thvar_t get_var_for_product(arith_vartable_t *table, varexp_t *p, uint32_t n, bool *new_var);




/*
 * ACCESS TO VARIABLE DATA
 */

/*
 * Check whether x is a valid variable index
 */
static inline bool valid_arith_var(arith_vartable_t *table, thvar_t x) {
  return 0 <= x && x < table->nvars;
}


/*
 * Check type: integer or not
 */
static inline bool arith_var_is_int(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_INT_MASK) != 0;
}


/*
 * Get/check the kind
 */
static inline avar_kind_t arith_var_kind(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (avar_kind_t)((table->tag[x] >> 4) & 3);
}

static inline bool arith_var_is_free(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_KIND_MASK) == AVARTAG_KIND_FREE;
}

static inline bool arith_var_def_is_poly(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_KIND_MASK) == AVARTAG_KIND_POLY;
}

static inline bool arith_var_def_is_product(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_KIND_MASK) == AVARTAG_KIND_PPROD;
}

static inline bool arith_var_def_is_rational(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_KIND_MASK) == AVARTAG_KIND_CONST;
}


/*
 * Definition of x
 */
static inline void* arith_var_def(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->def[x];
}

static inline polynomial_t *arith_var_poly_def(arith_vartable_t *table, thvar_t x) {
  assert(arith_var_def_is_poly(table, x));
  return table->def[x];
}

static inline pprod_t *arith_var_product_def(arith_vartable_t *table, thvar_t x) {
  assert(arith_var_def_is_product(table, x));
  return table->def[x];
}

static inline rational_t *arith_var_rational_def(arith_vartable_t *table, thvar_t x) {
  assert(arith_var_def_is_rational(table, x));
  return table->def[x];
}


/*
 * Atoms involving x
 */
static inline int32_t *arith_var_atom_vector(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->atoms[x];
}

static inline bool arith_var_has_atoms(arith_vartable_t *table, thvar_t x) {
  return arith_var_atom_vector(table, x) != NULL;
}

// number of atoms with variable x
static inline uint32_t arith_var_num_atoms(arith_vartable_t *table, thvar_t x) {
  int32_t *tmp;
  tmp = arith_var_atom_vector(table, x);
  return tmp == NULL ? 0 : iv_size(tmp);
}


/*
 * Value of x in the current assignment
 */
static inline xrational_t *arith_var_value(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->value + x;
}


/*
 * Lower and upper bound indices
 */
static inline int32_t arith_var_lower_index(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->lower_index[x];
}

static inline int32_t arith_var_upper_index(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->upper_index[x];
}


/*
 * Check the flags of x
 */
static inline bool arith_var_is_marked(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_MARK_MASK) != 0;
}

static inline bool arith_var_at_lower_bound(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_ATLB_MASK) != 0;
}

static inline bool arith_var_at_upper_bound(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & AVARTAG_ATUB_MASK) != 0;
}

// check whether x is at its lower or upper bound
static inline bool arith_var_at_bound(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & (AVARTAG_ATLB_MASK|AVARTAG_ATUB_MASK)) != 0;
}

// check whether x is a fixed variable (both flags are set)
static inline bool arith_var_is_fixed(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return (table->tag[x] & (AVARTAG_ATLB_MASK|AVARTAG_ATUB_MASK)) ==
    (AVARTAG_ATLB_MASK|AVARTAG_ATUB_MASK);
}

// get the full 8-bit tag
static inline uint8_t arith_var_tag(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->tag[x];
}



/*
 * Set or clear the flags for x
 */
static inline void set_arith_var_mark(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  table->tag[x] |= AVARTAG_MARK_MASK;
}

static inline void clear_arith_var_mark(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  table->tag[x] &= ~AVARTAG_MARK_MASK;
}

static inline void set_arith_var_lb(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  table->tag[x] |= AVARTAG_ATLB_MASK;
}

static inline void clear_arith_var_lb(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  table->tag[x] &= ~AVARTAG_ATLB_MASK;
}

static inline void set_arith_var_ub(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  table->tag[x] |= AVARTAG_ATUB_MASK;
}

static inline void clear_arith_var_ub(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  table->tag[x] &= ~AVARTAG_ATUB_MASK;
}


// set the full tag
static inline void set_arith_var_tag(arith_vartable_t *table, thvar_t x, uint8_t tg) {
  assert(valid_arith_var(table, x));
  table->tag[x] = tg;
}






/*
 * ETERM AND ATOMS
 */

/*
 * Attach eterm t to variable x
 * - x must not have an existing eterm attached
 */
extern void attach_eterm_to_arith_var(arith_vartable_t *table, thvar_t x, eterm_t t);


/*
 * Check whether there's at least one variable with an attached eterm in table
 */
extern bool arith_vartable_has_eterms(arith_vartable_t *table);


/*
 * Check whether x has an eterm attached
 */
static inline bool arith_var_has_eterm(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->eterm != NULL && table->eterm[x] != null_eterm;
}

/*
 * Get the eterm attached to x
 * - x must have an eterm attached
 */
static inline eterm_t arith_var_eterm(arith_vartable_t *table, thvar_t x) {
  assert(arith_var_has_eterm(table, x));
  return table->eterm[x];
}


/*
 * Variant: get the eterm attached to x or null_eterm if x has no eterm attached
 */
static inline eterm_t arith_var_get_eterm(arith_vartable_t *table, thvar_t x) {
  eterm_t t;

  assert(valid_arith_var(table, x));
  t = null_eterm;
  if (table->eterm != NULL) {
    t = table->eterm[x];
  }

  return t;
}


/*
 * Add atom index i to the vector atoms[x]
 * - x must be the variable of atom i
 * - i must not be already present in atoms[x]
 */
extern void attach_atom_to_arith_var(arith_vartable_t *table, thvar_t x, int32_t i);


/*
 * Remove i from the vector atoms[x]
 * - x must be the variable of atom i
 * - i must be present in atoms[x]
 */
extern void detach_atom_from_arith_var(arith_vartable_t *table, thvar_t x, int32_t i);




/*
 * ASSIGNMENT AND BOUNDS
 */

/*
 * Set value[x] to d
 */
static inline void set_arith_var_value(arith_vartable_t *table, thvar_t x, xrational_t *d) {
  assert(valid_arith_var(table, x));
  xq_set(table->value + x, d);
}


/*
 * Check whether value[x] is an integer
 */
static inline bool arith_var_value_is_int(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return xq_is_integer(table->value + x);
}


/*
 * Round value[x] up to the nearest integer
 */
static inline void set_arith_var_value_to_ceil(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  xq_ceil(table->value + x);
}


/*
 * Round value[x] down to the nearest integer
 */
static inline void set_arith_var_value_to_floor(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  xq_floor(table->value + x);
}




/*
 * Set upper_index/lower_index indices for x
 */
static inline void set_arith_var_lower_index(arith_vartable_t *table, thvar_t x, int32_t i) {
  assert(valid_arith_var(table, x));
  table->lower_index[x] = i;
}

static inline void set_arith_var_upper_index(arith_vartable_t *table, thvar_t x, int32_t i) {
  assert(valid_arith_var(table, x));
  table->upper_index[x] = i;
}


#endif /* __ARITH_VARTABLE_H */
