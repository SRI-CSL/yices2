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
 *     or a pointer to a varprod_t object (for non-linear arithmetic)
 * - whether v is an integer or a real variable
 * - the egraph term attached to v (or null_eterm if there's none)
 * - a vector of atoms indices (all the atoms whose variable is v)
 * - the value of v in the current assignment
 * - the index of lower/upper bounds on v
 *
 * There can be a special variable used to represent constant terms in
 * polynomials. The definition for that variable is the empty varprod
 * objects (i.e., 1). Its value is always 1.
 */

#ifndef __ARITH_VARTABLE_H
#define __ARITH_VARTABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bitvectors.h"
#include "int_hash_tables.h"
#include "index_vectors.h"
#include "varproducts.h"

#include "polynomials.h"
#include "egraph_base_types.h"
#include "extended_rationals.h"





/*
 * POINTER TAGGING
 */

/*
 * Tags for the definitions:
 * - to distinguish between pointers to polynomial_t and 
 *   pointers to varprod_t, we tag the low-order bits
 * - tag = 00 --> polynomial (or NULL)
 * - tag = 01 --> varprod objects
 */
#define POLY_PTR_TAG     ((size_t) 0x0)
#define VARPROD_PTR_TAG  ((size_t) 0x1)
#define ARITH_DEFPTR_TAG ((size_t) 0x3)


// get or check the tag of pointer d
static inline uint32_t get_ptr_tag(void *d) {
  return (uint32_t) (((size_t) d) & ARITH_DEFPTR_TAG);
}

static inline bool is_poly_ptr(void *d) {
  return get_ptr_tag(d) == POLY_PTR_TAG;
}

static inline bool is_varprod_ptr(void *d) {
  return get_ptr_tag(d) == VARPROD_PTR_TAG;
}

// tagging
static inline void *tag_poly_ptr(polynomial_t *p) {
  assert(get_ptr_tag(p) == 0);
  return (void *) p;
}

static inline void *tag_varprod_ptr(varprod_t *v) {
  assert(get_ptr_tag(v) == 0);
  return (void *) (((size_t) v) | VARPROD_PTR_TAG);
}

// untagging
static inline void *untag_ptr(void *d) {
  return (void *)(((size_t) d) & ~ARITH_DEFPTR_TAG);
}

static inline polynomial_t *untag_poly_ptr(void *d) {
  assert(is_poly_ptr(d));
  return (polynomial_t *) d;
}

static inline varprod_t *untag_varprd_ptr(void *d) {
  assert(is_varprod_ptr(d));
  return (varprod_t *) untag_ptr(d);
}





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
 */

#define AVARTAG_MARK_MASK  ((uint8_t) 0x1)
#define AVARTAG_ATLB_MASK  ((uint8_t) 0x2)
#define AVARTAG_ATUB_MASK  ((uint8_t) 0x4)




/********************
 *  VARIABLE TABLE  *
 *******************/

/*
 * - nvars = number of variables
 * - ivars = number of integer variables
 * - size = size of all variable-indexed arrays
 * - def = array of tagged pointers = variable definition
 * - atoms = atom vector for each variable
 * - eterm_of = array of egraph terms
 * - i_flag = bitvector: i_flag[x] is 1 if x is an integer variable, 0 otherwise
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
  byte_t *i_flag; 
  int32_t **atoms;
  eterm_t *eterm_of;

  // assignment, bounds, flags
  xrational_t *value;
  int32_t *lower_index;
  int32_t *upper_index;
  uint8_t *tag;
  
  int_htbl_t htbl;   // for hash consing
} arith_vartable_t;


/*
 * Default and maximal size 
 */
#define DEF_AVARTABLE_SIZE 100
#define MAX_AVARTABLE_SIZE (UINT32_MAX/sizeof(xrational_t))




/*
 * Initialization:
 * - the table is initialized with its default size
 * - the eterm_of array is not allocated here, but on the first
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
 * Support for push: delete all variables of index >= nvars
 */
extern void arith_vartable_remove_vars(arith_vartable_t *table, uint32_t nvars);


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
 * VARIABLE CREATION
 */

/*
 * All new variables are created with the following default initialization:
 * - no eterm attached
 * - empty atom vector
 * - value = 0
 * - lower bound and upper bound indices = -1
 */

/*
 * Create a new variable
 * - if is_int is true, the variable has integer type, otherwise it's a real variable
 * - the definition is NULL
 */
extern thvar_t create_arith_var(arith_vartable_t *table, bool is_int);



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
 * - i.e., write p as k + q where k is the constant term, then find variable for q
 */
extern thvar_t find_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n);

/*
 * Get a variable whose definition is equal to the non-constant part of p
 * - i.e., write p as k + q where k is the constant term, then get variable for q
 *
 * NOTE: this is used to construct atoms: for example, atom (a + q >= 0)
 * can be internalized to (x >= -a) with x = var_for_poly_offset(a + q) = var for q
 */
extern thvar_t get_var_for_poly_offset(arith_vartable_t *table, monomial_t *p, uint32_t n, bool *new_var);



/*
 * Find a variable whose definition is equal to the product p
 * - if there's no such variable, return null_thvar = -1
 * - p must normalized (cf. varproducts.h)
 */
extern thvar_t find_var_for_product(arith_vartable_t *table, varprod_t *p);

/*
 * Return a variable equal to product p. Create a new variable if needed.
 * - set *new_flag to true if a new variable is created
 */
extern thvar_t get_var_for_product(arith_vartable_t *table, varprod_t *p, bool *new_var);


/*
 * Variant: find a variable whose definition is equal to the content of a varproduct buffer
 * - if there's no such variable, return null_thvar = -1
 * - buffer must normalized (cf. varproducts.h)
 */
extern thvar_t find_var_for_vpbuffer(arith_vartable_t *table, vpbuffer_t *buffer);

/*
 * Return a variable equal to product p. Create a new variable if needed.
 * - set *new_flag to true if a new variable is created
 */
extern thvar_t get_var_for_vpbuffer(arith_vartable_t *table, vpbuffer_t *buffer, bool *new_var);



/*
 * CONSTANT
 */

/*
 * Return a variable equal to the empty product (i.e, the constant)
 * - return null_thvar if it's not been created
 */
extern thvar_t find_var_for_constant(arith_vartable_t *table);


/*
 * Get a variable whose definition is the empty product
 * - create a fresh variable if needed, and set new_var to true
 * - otherwise, set new_var to false
 *
 * NOTE: To make sure the constant has index 0 == const_idx, this
 * function should be called first, before any other variable is
 * constructed.
 */
extern thvar_t get_var_for_constant(arith_vartable_t *table, bool *new_var);




/*
 * ACCESS TO VARIABLE DATA
 */
static inline bool valid_arith_var(arith_vartable_t *table, thvar_t v) {
  return 0 <= v && v < table->nvars;
}

static inline bool arith_var_is_int(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return tst_bit(table->i_flag, v);
}

static inline bool arith_var_is_free(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->def[v] == NULL;
}

static inline bool arith_var_def_is_poly(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->def[v] != NULL && is_poly_ptr(table->def[v]);
}

static inline bool arith_var_def_is_product(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return is_varprod_ptr(table->def[v]);
}

// definition of v
static inline void* arith_var_def(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->def[v];
}

static inline polynomial_t *arith_var_poly_def(arith_vartable_t *table, thvar_t v) {
  assert(arith_var_def_is_poly(table, v));
  return untag_poly_ptr(table->def[v]);
}

static inline varprod_t *arith_var_product_def(arith_vartable_t *table, thvar_t v) {
  assert(arith_var_def_is_product(table, v));
  return untag_varprd_ptr(table->def[v]);
}

// atoms involving v
static inline int32_t *arith_var_atom_vector(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->atoms[v];
}

static inline bool arith_var_has_atoms(arith_vartable_t *table, thvar_t v) {
  return arith_var_atom_vector(table, v) != NULL;
}

// number of atoms with variable v
static inline uint32_t arith_var_num_atoms(arith_vartable_t *table, thvar_t v) {
  int32_t *tmp;
  tmp = arith_var_atom_vector(table, v);
  return tmp == NULL ? 0 : iv_size(tmp);
}

// value of v in the current assignment
static inline xrational_t *arith_var_value(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->value + v;
}


// lower and upper bound indices
static inline int32_t arith_var_lower_index(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->lower_index[v];
}

static inline int32_t arith_var_upper_index(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return table->upper_index[v];
}


/*
 * Check the flags of v
 */
static inline bool arith_var_is_marked(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return (table->tag[v] & AVARTAG_MARK_MASK) != 0;
}

static inline bool arith_var_at_lower_bound(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return (table->tag[v] & AVARTAG_ATLB_MASK) != 0;
}

static inline bool arith_var_at_upper_bound(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return (table->tag[v] & AVARTAG_ATUB_MASK) != 0;
}

// check whether v is at its lower or upper bound
static inline bool arith_var_at_bound(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return (table->tag[v] & (AVARTAG_ATLB_MASK|AVARTAG_ATUB_MASK)) != 0;
}

// check whether v is a fixed variable (both flags are set)
static inline bool arith_var_is_fixed(arith_vartable_t *table, thvar_t v) {
  assert(valid_arith_var(table, v));
  return (table->tag[v] & (AVARTAG_ATLB_MASK|AVARTAG_ATUB_MASK)) == 
    (AVARTAG_ATLB_MASK|AVARTAG_ATUB_MASK);
}

// get the full 8-bit tag
static inline uint8_t arith_var_tag(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->tag[x];
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
 * Check whether x has an eterm attached
 */
static inline bool arith_var_has_eterm(arith_vartable_t *table, thvar_t x) {
  assert(valid_arith_var(table, x));
  return table->eterm_of != NULL && table->eterm_of[x] != null_eterm;
}

/*
 * Get the eterm attached to x
 * - x must have an eterm attached
 */
static inline eterm_t arith_var_eterm(arith_vartable_t *table, thvar_t x) {
  assert(arith_var_has_eterm(table, x));
  return table->eterm_of[x];
}


/*
 * Variant: get the eterm attached to x or null_eterm if x has no eterm attached
 */
static inline eterm_t arith_var_get_eterm(arith_vartable_t *table, thvar_t x) {
  eterm_t t;

  assert(valid_arith_var(table, x));
  t = null_eterm;
  if (table->eterm_of != NULL) {
    t = table->eterm_of[x];
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
 * SET ASSIGNMENT, BOUNDS, FLAGS
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


/*
 * Set/clear the mark for v
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

static inline void set_arith_var_tag(arith_vartable_t *table, thvar_t x, uint32_t tg) {
  assert(valid_arith_var(table, x));
  table->tag[x] = tg;
}


#endif /* __ARITH_VARTABLE_H */
