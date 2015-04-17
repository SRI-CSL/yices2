/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * TABLE OF VARIABLES FOR THE BITVECTOR SOLVER
 */

/*
 * For each variable x, we store
 * - bit_size[x] = number of bits in x
 * - kind[x] = tag so that we know how to interpret def[x]
 * - def[x] = definition of x
 * - eterm[x] = attached egraph term (optional)
 * - map[x] = array of literals (bit blasting)
 *
 * Several variables may share the same map. To delete the maps
 * correctly in push/pop, we use reference counting.  The literal
 * arrays assigned to map[x] must be allocated with the
 * refcount_int_array functions.
 *
 * We use two bits in kind[x] to mark variables and to record which variables
 * have been bit-blasted:
 */

#ifndef __BV_VARTABLE_H
#define __BV_VARTABLE_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/egraph_base_types.h"
#include "terms/bvpoly_buffers.h"
#include "terms/power_products.h"
#include "utils/int_hash_tables.h"
#include "utils/refcount_int_arrays.h"



/*
 * Tags for kind[x]
 * - variables (no definition)
 * - constants (small/large bitvector constants)
 * - bit expressions
 * - array of bit expressions
 * - binary and unary operators (arithmetic + shift)
 *
 * For polynomials, we use two representations:
 * - when created, polynomials have a bvpoly or bvpoly64 descriptor
 * - in the first step of bit-blasting, we compile the polynomial
 *   expressions into the simpler operations that the bitblaster supports
 *   (i.e., binary ADD, SUB, MUL + NEG)
 */
typedef enum bvvar_tag {
  BVTAG_VAR,           // uninterpreted bitvector
  BVTAG_CONST64,       // constant represented as a 64bit unsigned integer
  BVTAG_CONST,         // constant represented as an array of 32bit words
  BVTAG_POLY64,        // polynomial with small coefficients
  BVTAG_POLY,          // polynomial with large coefficients
  BVTAG_PPROD,         // power product
  BVTAG_BIT_ARRAY,     // array of literals
  BVTAG_ITE,           // if-then-else (mux)
  BVTAG_UDIV,          // quotient in unsigned division
  BVTAG_UREM,          // remainder in unsigned division
  BVTAG_SDIV,          // quotient in signed division (rounding towards 0)
  BVTAG_SREM,          // remainder in signed division (rounding towards 0)
  BVTAG_SMOD,          // remainder in floor division (rounding towards -infinity)
  BVTAG_SHL,           // shift left
  BVTAG_LSHR,          // logical shift right
  BVTAG_ASHR,          // arithmetic shift right

  // auxiliary arithmetic operators for compilation of polynomials
  BVTAG_ADD,           // binary ADD
  BVTAG_SUB,           // binary SUB
  BVTAG_MUL,           // binary MUL
  BVTAG_NEG,           // opposite (one argument)
} bvvar_tag_t;

#define NUM_BVTAGS (BVTAG_NEG + 1)


/*
 * Descriptor for (if c then x else y)
 */
typedef struct bv_ite_s {
  literal_t cond;
  thvar_t left;
  thvar_t right;
} bv_ite_t;


/*
 * Descriptor (definition)
 */
typedef union bvvar_desc_u {
  uint64_t val;     // for const64
  thvar_t op[2];    // two variable operands
  void *ptr;        // pointer to polynomial/pprod/ite
} bvvar_desc_t;



/*
 * Variable table
 * - nvars = number of variables
 * - size = size of arrays bit_size, kind, def, map
 *        = size of eterm if eterm isn't NULL
 * - kind[x] is used both to store the tag for x and to mark x
 *   marking is done by setting the high-order bit of kind[x] to 1
 * - the mark indicates whether or not bit-blasting has been done on x
 */
typedef struct bv_vartable_s {
  uint32_t nvars;
  uint32_t size;

  // definition, size, etc.
  uint32_t *bit_size;
  uint8_t *kind;
  bvvar_desc_t *def;
  eterm_t *eterm;

  // mapping to literals
  literal_t **map;

  // hash consing
  int_htbl_t htbl;
} bv_vartable_t;


#define DEF_BVVARTABLE_SIZE 100
#define MAX_BVVARTABLE_SIZE (UINT32_MAX/sizeof(bvvar_desc_t))



/*
 * Bit masks for the kind:
 * - bit 7: mark
 * - bit 6: bit-blasted bit
 * - bit 5 to 0: the tag
 */

#define BVVAR_MARK_MASK ((uint8_t) 0x80)
#define BVVAR_BLST_MASK ((uint8_t) 0x40)
#define BVVAR_TAG_MASK  ((uint8_t) 0x3F)



/*
 * OPERATIONS
 */

/*
 * Initialize table
 * - use the default size
 * - the eterm array is not allocated here, but on the first
 *   call to attach_eterm
 * - variable 0 is reserved to prevent confusion with const_idx
 */
extern void init_bv_vartable(bv_vartable_t *table);


/*
 * Delete the table
 */
extern void delete_bv_vartable(bv_vartable_t *table);


/*
 * Reset: empty the table
 * - the variable 0 marker is kept
 */
extern void reset_bv_vartable(bv_vartable_t *table);


/*
 * Attach egraph term t to variable x
 * - x must be not have an eterm attached already
 */
extern void attach_eterm_to_bvvar(bv_vartable_t *table, thvar_t x, eterm_t t);


/*
 * Check whether x has an eterm attached
 */
static inline bool bvvar_has_eterm(bv_vartable_t *table, thvar_t x) {
  assert(1 <= x && x < table->nvars);
  return table->eterm != NULL && table->eterm[x] != null_eterm;
}


/*
 * Get the eterm attached to x or null_eterm
 */
static inline eterm_t bvvar_get_eterm(bv_vartable_t *table, thvar_t x) {
  eterm_t t;

  assert(1 <= x && x < table->nvars);
  t = null_eterm;
  if (table->eterm != NULL) {
    t = table->eterm[x];
  }
  return t;
}


/*
 * Remove all eterms of id >= nterms
 */
extern void bv_vartable_remove_eterms(bv_vartable_t *table, uint32_t nterms);



/*
 * Remove all variables of index >= nv
 */
extern void bv_vartable_remove_vars(bv_vartable_t *table, uint32_t nv);



/*
 * VARIABLE CONSTRUCTORS
 */

/*
 * All constructors check whether a variable matching the given definition
 * is present in table. If so they return it. Otherwise, they create
 * a new variable with the right descriptor and return it.
 */

/*
 * New variable: n = number of bits
 */
extern thvar_t make_bvvar(bv_vartable_t *table, uint32_t n);


/*
 * Constants: n = number of bits, val = constant value
 * - val must be normalized modulo 2^n
 */
extern thvar_t get_bvconst64(bv_vartable_t *table, uint32_t n, uint64_t val);
extern thvar_t get_bvconst(bv_vartable_t *table, uint32_t n, uint32_t *val);


/*
 * Polynomials and power products
 */
extern thvar_t get_bvpoly64(bv_vartable_t *table, bvpoly_buffer_t *buffer);
extern thvar_t get_bvpoly(bv_vartable_t *table, bvpoly_buffer_t *buffer);
extern thvar_t get_bvpprod(bv_vartable_t *table, uint32_t n, pp_buffer_t *buffer);


/*
 * For all these constructors: n = number of bits
 */
extern thvar_t get_bvarray(bv_vartable_t *table, uint32_t n, literal_t *a);
extern thvar_t get_bvite(bv_vartable_t *table, uint32_t n, literal_t l, thvar_t x, thvar_t y);
extern thvar_t get_bvdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvsdiv(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvsrem(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvsmod(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvshl(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvlshr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);
extern thvar_t get_bvashr(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y);


/*
 * Search for (div x y), (rem x y), etc.
 * - return -1 if the term is not in the table
 */
extern thvar_t find_div(bv_vartable_t *table, thvar_t x, thvar_t y);
extern thvar_t find_rem(bv_vartable_t *table, thvar_t x, thvar_t y);
extern thvar_t find_sdiv(bv_vartable_t *table, thvar_t x, thvar_t y);
extern thvar_t find_srem(bv_vartable_t *table, thvar_t x, thvar_t y);



/*
 * Auxiliary arithmetic nodes:
 * - n = number of bits
 * - x (and y is present) = operands
 * - set new_var to true if a new variable is created
 *   set new_var to false if the variable was already present in table
 */
extern thvar_t get_bvadd(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y, bool *new_var);
extern thvar_t get_bvsub(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y, bool *new_var);
extern thvar_t get_bvmul(bv_vartable_t *table, uint32_t n, thvar_t x, thvar_t y, bool *new_var);
extern thvar_t get_bvneg(bv_vartable_t *table, uint32_t n, thvar_t x, bool *new_var);

extern thvar_t find_bvadd(bv_vartable_t *table, thvar_t x, thvar_t y);
extern thvar_t find_bvsub(bv_vartable_t *table, thvar_t x, thvar_t y);
extern thvar_t find_bvmul(bv_vartable_t *table, thvar_t x, thvar_t y);
extern thvar_t find_bvneg(bv_vartable_t *table, thvar_t x);



/*
 * Extract the tag out of kind[x]
 * - kind[x] stores
 *   bit 7: mark bit
 *   bit 6: bitblasted bit
 *   bit 5--0: tag
 */
static inline bvvar_tag_t tag_of_kind(uint8_t k) {
  return (bvvar_tag_t) (k & BVVAR_TAG_MASK);
}

static inline bool mark_of_kind(uint8_t k) {
  return (k & BVVAR_MARK_MASK) != 0;
}

static inline bool blasted_of_kind(uint8_t k) {
  return (k & BVVAR_BLST_MASK) != 0;
}



/*
 * ACCESS TO VARIABLE ATTRIBUTES
 */
static inline bool valid_bvvar(bv_vartable_t *table, thvar_t x) {
  return 0 <= x && x < table->nvars;
}

static inline bvvar_tag_t bvvar_tag(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return tag_of_kind(table->kind[x]);
}

static inline bool bvvar_is_marked(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return mark_of_kind(table->kind[x]);
}

static inline bool bvvar_is_bitblasted(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return blasted_of_kind(table->kind[x]);
}

static inline uint32_t bvvar_bitsize(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return table->bit_size[x];
}

static inline bool bvvar_is_uninterpreted(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_VAR;
}

static inline bool bvvar_is_const64(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_CONST64;
}

static inline bool bvvar_is_const(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_CONST;
}

static inline bool bvvar_is_poly64(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_POLY64;
}

static inline bool bvvar_is_poly(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_POLY;
}

static inline bool bvvar_is_pprod(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_PPROD;
}

static inline bool bvvar_is_bvarray(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_BIT_ARRAY;
}

static inline bool bvvar_is_ite(bv_vartable_t *table, thvar_t x) {
  return bvvar_tag(table, x) == BVTAG_ITE;
}


/*
 * Value of a constant
 */
static inline uint64_t bvvar_val64(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_const64(table, x));
  return table->def[x].val;
}

static inline uint32_t *bvvar_val(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_const(table, x));
  return table->def[x].ptr;
}


/*
 * Definition of a variable x
 */
static inline bvpoly_t *bvvar_poly_def(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_poly(table, x));
  return table->def[x].ptr;
}

static inline bvpoly64_t *bvvar_poly64_def(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_poly64(table, x));
  return table->def[x].ptr;
}

static inline pprod_t *bvvar_pprod_def(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_pprod(table, x));
  return table->def[x].ptr;
}

static inline literal_t *bvvar_bvarray_def(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_bvarray(table, x));
  return table->def[x].ptr;
}

static inline bv_ite_t *bvvar_ite_def(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_ite(table, x));
  return table->def[x].ptr;
}

// pair of operands
static inline thvar_t *bvvar_binop(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_tag(table, x) >= BVTAG_UDIV);
  return table->def[x].op;
}


/*
 * Check whether variable x is mapped to something
 */
static inline bool bvvar_is_mapped(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return table->map[x] != NULL;
}


/*
 * Return the literal array mapped to x (NULL if nothing is mapped)
 */
static inline literal_t *bvvar_get_map(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  return table->map[x];
}


/*
 * Map literal array a to variable x
 * - a must be non-null and allocated using int_array_alloc
 */
static inline void bvvar_set_map(bv_vartable_t *table, thvar_t x, literal_t *a) {
  assert(! bvvar_is_mapped(table, x) && a != NULL);
  int_array_incref(a);
  table->map[x] = a;
}


/*
 * Reset the map of x to NULL
 * - x must have a non-null map
 */
static inline void bvvar_reset_map(bv_vartable_t *table, thvar_t x) {
  assert(bvvar_is_mapped(table, x));
  int_array_decref(table->map[x]);
  table->map[x] = NULL;
}


/*
 * Set/clear the mark on x
 */
static inline void bvvar_set_mark(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  table->kind[x] |= BVVAR_MARK_MASK;
}

static inline void bvvar_clr_mark(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  table->kind[x] &= (uint8_t)(~BVVAR_MARK_MASK);
}


/*
 * Set/clear the bit-blasted bit on x
 */
static inline void bvvar_set_bitblasted(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  table->kind[x] |= BVVAR_BLST_MASK;
}

static inline void bvvar_clr_bitblasted(bv_vartable_t *table, thvar_t x) {
  assert(valid_bvvar(table, x));
  table->kind[x] &= (uint8_t) (~BVVAR_BLST_MASK);
}



#endif /* __BV_VARTABLE_H */
