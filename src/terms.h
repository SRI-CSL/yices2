/*
 * Internal term representation
 * ----------------------------
 *
 * This module provides low-level functions for term construction
 * and management of a global term table.
 * 
 * Changes:
 *
 * Feb. 20, 2007.  Added explicit variables for dealing with
 * quantifiers, rather than DeBruijn indices. DeBruijn indices
 * do not mix well with hash consing because different occurrences
 * of the same variable may have different indices.
 * Removed free_vars field since we can't represent free variables
 * via a bit vector anymore.
 *
 * March 07, 2007. Removed bvconstant as a separate representation.
 * They can be stored as bdd-arrays. That's simpler and does not cause
 * much overhead.
 *
 * March 24, 2007. Removed mandatory names for uninterpreted constants.
 * Replaced by a function that creates a new uninterpreted constant (with
 * no name) of a given type. Also removed built-in names for the boolean
 * constants.
 *
 * April 20, 2007. Put back a separate representation for bvconstants.
 *
 * June 6, 2007. Added distinct as a builtin term kind.
 *
 * June 12, 2007. Added the bv_apply constructor to support bit-vector operations
 * that are overloaded but that we want to treat as uninterpreted terms (mostly).
 * This is a hack to support the overloaded operators from SMT-LIB 2007 (e.g., bvdiv,
 * bvlshr, etc.) 
 *
 * December 11, 2008. Added arith_bineq constructor.
 *
 * January 27, 2009. Removed BDD representation of bvlogic_expressions
 *
 *
 * MAJOR REVISION: April 2010
 *
 * 1) Removed the arithmetic and bitvector variables in polynomials
 *    To replace them, we represent power-products directly as 
 *    terms in the term table.
 *
 * 2) Removed the AIG-style data structures for bitvectors (these 
 *    are replaced by arrays of boolean terms). Added an n-ary 
 *    (xor ...) term constructor to help representing bv-xor.
 *
 * 3) Removed the term constructor 'not' for boolean negation.
 *    Used positive/negative polarity bits to replace that:
 *    For a boolean term t, we use a one bit tag to denote t+ and t-,
 *    where t- means (not t).
 *
 * 5) Added terms for converting between boolean and bitvector terms:
 *    Given a term u of type (bitvector n) then (bit u i) is 
 *    a boolean term for i=0 to n-1. (bit u 0) is the low-order bit.
 *    Conversely, given n boolean terms b_0 ... b_{n-1}, the term
 *    (bitarray b0 ... b_{n-1}) is the bitvector formed by b0 ... b_{n-1}.
 *
 * 6) Added support for unit types: a unit type tau is a type of cardinality
 *    one. In that case, all terms of type tau are equal so we build a
 *    single representative term for type tau.
 *
 * 7) General cleanup to make things more consistent: use a generic
 *    structure to represent most composite terms.
 */

/*
 * The internal terms include:
 * 1) constants:
 *    - constants of uninterpreted/scalar
 *    - global uninterpreted constants 
 * 2) generic terms
 *    - ite c t1 t2
 *    - eq t1 t2
 *    - apply f t1 ... t_n
 *    - mk-tuple t1 ... t_n
 *    - select i tuple
 *    - update f t1 ... t_n v
 *    - distinct t1 ... t_n
 * 3) variables and quantifiers
 *    - variables are identified by their type and an integer index.
 *    - quantified formulas are of the form (forall v_1 ... v_n term)
 *      where each v_i is a variable
 * 4) boolean operators
 *    - or t1 ... t_n
 *    - xor t1 ... t_n
 *    - bit i u (extract bit i of a bitvector term u)
 * 6) arithmetic terms and atoms
 *    - terms are either rational constants, power products, or 
 *      polynomials with rational coefficients
 *    - atoms are either of the form (t == 0) or (t >= 0)
 *      where p is a term.
 *    - atoms a x - a y == 0 are rewritten to (x = y)
 * 7) bitvector terms and atoms
 *    - bitvector constants
 *    - power products
 *    - polynomials
 *    - bit arrays
 *    - other operations: divisions/shift
 *    - atoms: three binary predicates
 *      bv_eq t1 t2
 *      bv_ge t1 t2 (unsigned comparison: t1 >= t2)
 *      bv_sge t1 t2 (signed comparison: t1 >= t2)
 *
 * Every term is an index t in a global term table,
 * where 0 <= t <= 2^30. There are two term occurrences
 * t+ and t- associated with term t.  The two occurrences
 * are encoded in signed 32bit integers:
 * - bit[31] = sign bit = 0
 * - bits[30 ... 1] = t
 * - bit[0] = polarity bit: 0 for t+, 1 for t-
 *
 * For a boolean term t, the occurrence t+ means p
 * and t- means (not p). All occurrences of a 
 * non-boolean term t are positive.
 * 
 * For every term, we keep:
 * - type[t] (index in the type table)
 * - kind[t] (what kind of term it is)
 * - desc[t] = descriptor that depends on the kind
 *
 * It is possible to attach names to term occurrences (but not directly 
 * to terms). This is required to deal properly with booleans. For example,
 * we want to allow the user to give different names to t and (not t).
 */

#ifndef __TERMS_H
#define __TERMS_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "bitvectors.h"
#include "int_vectors.h"
#include "ptr_vectors.h"
#include "int_hash_tables.h"
#include "int_hash_map.h"
#include "ptr_hash_map.h"
#include "symbol_tables.h"

#include "types.h"
#include "pprod_table.h"
#include "arith_buffers.h"
#include "bvarith_buffers.h"
#include "bvarith64_buffers.h"


/*
 * TERM INDICES
 */

/*
 * type_t and term_t are aliases for int32_t, defined in yices_types.h.
 *
 * We use the type term_t to denote term occurrences (i.e., a pair
 * term index + polarity bit packed into a singed 32bit integer as
 * defined in term_occurrences.h).
 * 
 * NULL_TERM and NULL_TYPE are also defined in yices_types.h (used to
 * report errors).
 *
 * Limits defined in yices_limits.h are relevant here:
 *
 * 1) YICES_MAX_TERMS = bound on the number of terms
 * 2) YICES_MAX_TYPES = bound on the number of tuypes
 * 3) YICES_MAX_ARITY = bound on the term arity
 * 4) YICES_MAX_VARS = bound on n in (FORALL (x_1.... x_n) P)
 * 5) YICES_MAX_DEGREE = bound on the total degree of polynomials and power-products
 * 6) YICES_MAX_BVSIZE = bound on the size of bitvector
 *
 */
#include "yices_types.h"
#include "yices_limits.h"



/*
 * TERM KINDS
 */
typedef enum {
  UNUSED_TERM,    // deleted term
  RESERVED_TERM,  // mark for term indices that can't be used

  // Generic atomic terms
  CONSTANT_TERM,  // constant of uninterpreted/scalar/boolean types
  UNINTERPRETED_TERM,  // (i.e., global variables, can't be bound).
  VARIABLE,       // variable in quantifiers 

  // Generic composite terms
  ITE_TERM,       // if-then-else 
  APP_TERM,       // application of an uninterpreted function 
  UPDATE_TERM,    // function update
  TUPLE_TERM,     // tuple constructor
  SELECT_TERM,    // tuple projection

  // Boolean terms
  EQ_TERM,        // equality
  DISTINCT_TERM,  // distinct t_1 ... t_n
  FORALL_TERM,    // quantifier
  OR_TERM,        // n-ary OR
  XOR_TERM,       // n-ary XOR
  BIT_TERM,       // bit-select

  // Power products: can be either arithmetic or bitvector terms
  POWER_PRODUCT,

  // Arithmetic terms and atoms
  ARITH_CONSTANT,   // rational constant
  ARITH_POLY,       // polynomial
  ARITH_EQ_ATOM,    // atom p == 0
  ARITH_GE_ATOM,    // atom p >= 0
  ARITH_BINEQ_ATOM, // equality: (t1 == t2)  (between two arithmetic terms)

  // Bitvector terms and atoms
  BV64_CONSTANT,   // compact bitvector constant (64bit at most)
  BV_CONSTANT,     // generic bitvector constant
  BV64_POLY,       // polynomial with 64bit coefficients
  BV_POLY,         // generic polynomial
  BV_ARRAY,        // array of boolean terms
  BV_DIV,          // unsigned division
  BV_REM,          // unsigned remainder
  BV_SDIV,         // signed division
  BV_SREM,         // remainder in signed division (rounding to 0)
  BV_SMOD,         // remainder in signed division (rounding to -infinity)
  BV_SHL,          // shift left (padding with 0)
  BV_LSHR,         // logical shift right (padding with 0)
  BV_ASHR,         // arithmetic shift right (padding wih sign bit)
  BV_EQ_ATOM,      // equality: (t1 == t2)
  BV_GE_ATOM,      // unsigned comparison: (t1 >= t2)
  BV_SGE_ATOM,     // signed comparison (t1 >= t2)
} term_kind_t;



/*
 * PREDEFINED TERMS
 */

/*
 * Term index 0 is reserved to make sure there's no possibility
 * that a real term has index equal to const_idx (= 0) used in 
 * polynomials.
 *
 * The boolean constant true is built-in and always has index 1.
 * This gives two terms:
 * - true_term = pos_occ(bool_const) = 2
 * - false_term = neg_occ(bool_const) = 3
 *
 * The constant 0 is also built-in and always has index 2
 * - so zero_term = pos_occ(zero_const) = 4
 */
enum {
  // indices
  bool_const = 1,
  zero_const = 2,
  // terms
  true_term = 2,
  false_term = 3,
  zero_term = 4,
};


/*
 * TERM DESCRIPTORS
 */

/*
 * Composite: array of n terms
 */
typedef struct composite_term_s {
  uint32_t arity;  // number of subterms
  term_t arg[0];  // real size = arity
} composite_term_t;


/*
 * Tuple projection and bit-extraction:
 * - an integer index + a term occurrence
 */
typedef struct select_term_s {
  uint32_t idx;
  term_t arg;
} select_term_t;


/*
 * Bitvector constants of arbitrary size:
 * - bitsize = number of bits
 * - data = array of 32bit words (of size equal to ceil(nbits/32))
 */
typedef struct bvconst_term_s {
  uint32_t bitsize;
  uint32_t data[0];
} bvconst_term_t;


/*
 * Bitvector constants of no more than 64bits
 */
typedef struct bvconst64_term_s {
  uint32_t bitsize; // between 1 and 64
  uint64_t value;   // normalized value: high-order bits are 0
} bvconst64_term_t;


/*
 * Descriptor: one of
 * - integer index for constant terms and variables
 * - rational constant
 * - ptr to a composite, polynomial, or power-product
 */
typedef union {
  int32_t integer;
  void *ptr;
  rational_t rational;
} term_desc_t;

 
/*
 * Term table: valid terms have indices between 0 and nelems - 1
 *
 * For each i between 0 and nelems - 1
 * - kind[i] = term kind
 * - type[i] = type
 * - desc[i] = term descriptor
 * - mark[i] = one bit used during garbage collection
 * - size = size of these arrays.
 *
 * After deletion, term indices are recycled into a free list.
 * - free_idx = start of the free list (-1 if the list is empty)
 * - if i is in the free list then kind[i] is UNUSED and 
 *   desc[i].integer is the index of the next term in the free list
 *   (or -1 if i is the last element in the free list).
 *
 * Symbol table and name table:
 * - stbl is a symbol table that maps names (strings) to term occurrences.
 * - the name table is the reverse. If maps term occurrence to a name.
 * The base name of a term occurrence t, is what's mapped to t in ntbl.
 * It's used to display t in pretty printing. The symbol table is 
 * more important.
 *
 * Other components:
 * - types = pointer to an associated type table
 * - pprods = pointer to an associated power product table
 * - htbl = hash table for hash consing
 * - utbl = table to map singleton types to the unique term of that type
 *
 * Auxilairy vectors
 * - ibuffer: to store an array of integers
 * - pbuffer: to store an array of pprods
 */
typedef struct term_table_s {
  uint8_t *kind;
  term_desc_t *desc;
  type_t *type;
  byte_t *mark;

  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  type_table_t *types;
  pprod_table_t *pprods;
  
  int_htbl_t htbl;
  stbl_t stbl;
  ptr_hmap_t ntbl;
  int_hmap_t utbl;

  ivector_t ibuffer;
  pvector_t pbuffer;
} term_table_t;




/*
 * INITIALIZATION
 */

/*
 * Initialize table:
 * - n = initial size 
 * - ttbl = attached type table
 * - ptbl = attached power-product table
 */
extern void init_term_table(term_table_t *table, uint32_t n, type_table_t *ttbl, pprod_table_t *ptbl);


/*
 * Delete all terms and descriptors, symbol table, hash table, etc.
 */ 
extern void delete_term_table(term_table_t *table);



/*
 * TERM CONSTRUCTORS
 */

/* 
 * All term constructors return a term occurence and all the arguments
 * the constructors must be term occurrences (term index + polarity
 * bit). The constructors do not check type correctness or attempt any
 * simplification. They just do hash consing.
 */

/*
 * Constant of the given type and index.
 * - tau must be uninterpreted or scalar
 * - if tau is scalar of cardinality n, then index must be between 0 and n-1
 */
extern term_t constant_term(term_table_t *table, type_t tau, int32_t index);


/*
 * Declare a new uninterpreted constant of type tau.
 * - this always create a fresh term
 */
extern term_t new_uninterpreted_term(term_table_t *table, type_t tau);


/*
 * Variable of type tau. Index i is used to distinguish it from other variables
 * of the same type.
 */
extern term_t variable(term_table_t *table, type_t tau, int32_t index);


/*
 * Negation: just flip the polarity bit
 * - p must be boolean
 */
extern term_t not_term(term_table_t *table, term_t p);


/*
 * If-then-else term (if cond then left else right)
 * - tau must be the super type of left/right.
 */
extern term_t ite_term(term_table_t *table, type_t tau, term_t cond, term_t left, term_t right);


/*
 * Other constructors compute the result type
 * - for variable-arity constructor: 
 *   arg must be an array of n term occurrences
 *   and n must be no more than YICES_MAX_ARITY.
 */
extern term_t app_term(term_table_t *table, term_t fun, uint32_t n, term_t arg[]);
extern term_t update_term(term_table_t *table, term_t fun, uint32_t n, term_t arg[], term_t new_v);
extern term_t tuple_term(term_table_t *table, uint32_t n, term_t arg[]);
extern term_t select_term(term_table_t *table, uint32_t index, term_t tuple);
extern term_t eq_term(term_table_t *table, term_t left, term_t right);
extern term_t distinct_term(term_table_t *table, uint32_t n, term_t arg[]);
extern term_t forall_term(term_table_t *table, uint32_t n, term_t var[], term_t body);
extern term_t or_term(term_table_t *table, uint32_t n, term_t arg[]);
extern term_t xor_term(term_table_t *table, uint32_t n, term_t arg[]);
extern term_t bit_term(term_table_t *table, uint32_t index, term_t bv);



/*
 * POWER PRODUCT
 */

/*
 * Power product: r must be valid in table->ptbl, and must not be a tagged 
 * variable or empty_pp.
 * - each variable index x_i in r must be a term defined in table
 * - the x_i's must have compatible types: either they are all arithmetic
 *   terms (type int or real) or they are all bit-vector terms of the 
 *   same type.
 * The type of the result is determined from the x_i's type:
 * - if all x_i's are int, the result is int 
 * - if some x_i's are int, some are real, the result is real
 * - if all x_i's have type (bitvector k), the result has type (bitvector k)
 */
extern term_t pprod_term(term_table_t *table, pprod_t *r);




/*
 * ARITHMETIC TERMS
 */

/*
 * Rational constant: the result has type int if a is an integer or real otherwise
 */
extern term_t arith_constant(term_table_t *table, rational_t *a);


/*
 * Arithmetic polynomial
 * - all variables of b must be real or integer terms defined in table
 * - b must be normalized and b->ptbl must be the same as table->ptbl
 * - if b contains a non-linear polynomial then the power products that
 *   occur in p are converted to terms (using pprod_term)
 * - then b is turned into a polynomial object a_1 x_1 + ... + a_n x_n,
 *   where x_i is a term.
 *
 * SIDE EFFECT: b is reset to zero
 */
extern term_t arith_poly(term_table_t *table, arith_buffer_t *b);


/*
 * Atom (t == 0)
 * - t must be an arithmetic term
 */
extern term_t arith_eq_atom(term_table_t *table, term_t t);


/*
 * Atom (t >= 0)
 * - t must be an arithmetic term
 */
extern term_t arith_geq_atom(term_table_t *table, term_t t);


/*
 * Simple equality between two arithmetic terms (left == right)
 */
extern term_t arith_bineq_atom(term_table_t *table, term_t left, term_t right);





/*
 * BITVECTOR TERMS
 */

/*
 * Small bitvector constant
 * - n = bitsize (must be between 1 and 64)
 * - bv = value (must be normalized modulo 2^n)
 */
extern term_t bv64_constant(term_table_t *table, uint32_t n, uint64_t bv);

/*
 * Bitvector constant: 
 * - n = bitsize
 * - bv = array of k words (where k = ceil(n/32))
 * The constant must be normalized (modulo 2^n)
 * This constructor should be used only for n > 64.
 */
extern term_t bvconst_term(term_table_t *table, uint32_t n, uint32_t *bv);


/*
 * Bitvector polynomials are constructed from a buffer b
 * - all variables of b must be bitvector terms defined in table
 * - b must be normalized and b->ptbl must be the same as table->ptbl
 * - if b contains non-linear terms, then the power products that
 *   occur in b are converted to terms (using pprod_term) then 
 *   a polynomial object is created.
 *
 * SIDE EFFECT: b is reset to zero.
 */
extern term_t bv64_poly(term_table_t *table, bvarith64_buffer_t *b);
extern term_t bv_poly(term_table_t *table, bvarith_buffer_t *b);


/*
 * Bitvector formed of arg[0] ... arg[n-1]
 * - n must be positive and no more than YICES_MAX_BVSIZE
 * - arg[0] ... arg[n-1] must be boolean terms
 */
extern term_t bvarray_term(term_table_t *table, uint32_t n, term_t arg[]);


/*
 * Division and shift operators
 * - the two arguments must be bitvector terms of the same type
 * - in the division/remainder operators, b is the divisor
 * - in the shift operator: a is the bitvector to be shifted 
 *   and b is the shift amount
 */
extern term_t bvdiv_term(term_table_t *table, term_t a, term_t b);
extern term_t bvrem_term(term_table_t *table, term_t a, term_t b);
extern term_t bvsdiv_term(term_table_t *table, term_t a, term_t b);
extern term_t bvsrem_term(term_table_t *table, term_t a, term_t b);
extern term_t bvsmod_term(term_table_t *table, term_t a, term_t b);

extern term_t bvshl_term(term_table_t *table, term_t a, term_t b);
extern term_t bvlshr_term(term_table_t *table, term_t a, term_t b);
extern term_t bvashr_term(term_table_t *table, term_t a, term_t b);


/*
 * Bitvector atoms: l and r must be bitvector terms of the same type
 *  (bveq l r): l == r
 *  (bvge l r): l >= r unsigned
 *  (bvsge l r): l >= r signed
 */
extern term_t bveq_atom(term_table_t *table, term_t l, term_t r);
extern term_t bvge_atom(term_table_t *table, term_t l, term_t r);
extern term_t bvsge_atom(term_table_t *table, term_t l, term_t r);





/*
 * SINGLETON TYPES AND REPRESENTATIVE
 */

/*
 * With every singleton type, we assign a unique representative.  The
 * mapping from unit type to representative is stored in an internal
 * hash-table. The following functions add/query this hash table.
 */

/*
 * Store t as the unique term of type tau:
 * - tau must be a singleton type
 * - t must be a valid term occurrence of type tau
 * - there musn't be a representative for tau already
 */
extern void add_unit_type_rep(term_table_t *table, type_t tau, term_t t);


/*
 * Get the unique term of type tau:
 * - tau must be a singleton type
 * - return the term mapped to tau in a previous call to add_unit_type_rep.
 * - return NULL_TERM if there's no such term.
 */
extern term_t unit_type_rep(term_table_t *table, type_t tau);




/*
 * NAMES
 */

/*
 * IMPORTANT: we use reference counting on character strings as
 * implemented in refcount_strings.h.
 *
 * Parameter "name" in set_term_name must be constructed via the
 * clone_string function.  That's not necessary for get_term_by_name
 * or remove_term_name.  When name is added to the term table, its
 * reference counter is increased by 1 or 2.  When remove_term_name is
 * called for an existing symbol, the symbol's reference counter is
 * decremented.  When the table is deleted (via delete_term_table),
 * the reference counters of all symbols present in table are also
 * decremented.
 */

/*
 * Assign name to term occurrence t.
 *
 * If name is already mapped to another term t' then the previous mapping
 * is hidden. The next calls to get_term_by_name will return t. After a 
 * call to remove_term_name, the mapping [name --> t] is removed and 
 * the previous mapping [name --> t'] is revealed.
 *
 * If t does not have a base name already, then 'name' is stored as the 
 * base name for t. That's what's printed for t by the pretty printer.
 *
 * Warning: name is stored as a pointer, no copy is made; name must be 
 * created via the clone_string function.
 */
extern void set_term_name(term_table_t *table, term_t t, char *name);


/*
 * Get term occurrence with the given name (or NULL_TERM)
 */
extern term_t get_term_by_name(term_table_t *table, char *name);


/*
 * Remove a name from the symbol table
 * - if name is not in the symbol table, nothing is done
 * - if name is mapped to a term t, then the mapping [name -> t]
 *   is removed. If name was mapped to a previous term t' then
 *   that mappeing is restored.
 *
 * If name is the base name of a term t, then that remains unchanged.
 */
extern void remove_term_name(term_table_t *table, char *name);


/*
 * Get the base name of term occurrence t
 * - return NULL if t has no base name
 */
extern char *term_name(term_table_t *table, term_t t);


/*
 * Clear name: remove t's base name if any.
 * - If t has name 'xxx' then 'xxx' is first removed from the symbol
 *   table (using remove_type_name) then t's base name is erased.
 *   The reference counter for 'xxx' is decremented twice.
 * - If t doesn't have a base name, nothing is done.
 */
extern void clear_term_name(term_table_t *table, term_t t);






/*
 * TERM INDICES/POLARITY
 */

/*
 * Conversion between indices and terms
 * - the polarity bit is the low-order bit of
 *   0 means positive polarity
 *   1 means negative polarity
 */
static inline term_t pos_term(int32_t i) {
  return (i << 1);
}

static inline term_t neg_term(int32_t i) {
  return (i << 1) | 1;
}


/*
 * Term of index i and polarity tt
 * - true means positive polarity
 * - false means negative polarity
 */
static inline term_t mk_term(int32_t i, bool tt) {
  return (i << 1) | (((int32_t) tt) ^ 1);
}


/*
 * Extract term and polarity bit
 */
static inline int32_t index_of(term_t x) {
  return x>>1;
}

static inline uint32_t polarity_of(term_t x) {
  return ((uint32_t) x) & 1;
} 


/*
 * Check polarity
 */
static inline bool is_pos_term(term_t x) {
  return polarity_of(x) == 0;
}

static inline bool is_neg_term(term_t x) {
  return polarity_of(x) != 0;
}


/*
 * Complement of x = same term, opposite polarity
 * - this can be used instead of not_term(table, x)
 *   if x is known to be a valid boolean term.
 */
static inline term_t opposite_term(term_t x) {
  return x ^ 1;
}


/*
 * Conversion of boolean to true_term or false_term
 */
static inline term_t bool2term(bool tt) {
  return mk_term(bool_const, tt);
}



/*
 * SUPPORT FOR POLYNOMIAL/BUFFER OPERATIONS
 */

/*
 * The term table store polynomials in the form
 *      a_0 t_0 + ... + a_n t_n 
 * where a_i is a coefficient and t_i is a term.
 *
 * For arithmetic and bit-vector operations that involve buffers and
 * terms, we must convert the integer indices t_0 ... t_n to the
 * power products r_0 ... r_n that buffers require. 
 *
 * The translation is defined by:
 * 1) if t_i is const_idx --> r_i is empty_pp
 * 2) if t_i is a power product --> r_i = descriptor for t_i
 * 3) otherwise --> r_i = var_pp(t_i)
 */

/*
 * Convert term t to a power product:
 * - t must be a term (not a term index) present in the table
 * - t must have arithmetic or bitvector type
 */
extern pprod_t *pprod_for_term(term_table_t *table, term_t t);


/*
 * Degree of term t
 * - t must be a good term of arithmetic or bitvector type
 *
 * - if t is a constant --> 0
 * - if t is a power product --> that product degree
 * - if t is a polynomial --> degree of that polynomial
 * - otherwise --> 1
 */
extern uint32_t term_degree(term_table_t *table, term_t t);


/*
 * Convert all indices in polynomial p to power products
 * - all variable indices of p must be either const_idx or 
 *   arithmetic terms present in table.
 * - the result is stored in table's internal pbuffer.
 * - the function returns pbuffer->data
 *
 * The number of elements in pbuffer is equal to p->nterms + 1.
 * - pbuffer->data[i] = pprod_for_term(table, p->mono[i].var)
 * - the last element of buffer->data is the end marker end_pp.
 */
extern pprod_t **pprods_for_poly(term_table_t *table, polynomial_t *p);


/*
 * Convert all indices in bitvector polynomial p to power products
 * - all variable indices of p must be either const_idx or 
 *   bitvector terms of bitsize <= 64 present in table.
 * - the result is stored in table's internal pbuffer.
 * - the function returns pbuffer->data.
 */
extern pprod_t **pprods_for_bvpoly64(term_table_t *table, bvpoly64_t *p);


/*
 * Convert all indices in bitvector polynomial p to power products
 * - all variable indices of p must be either const_idx or 
 *   arithmetic terms present in table.
 * - the result is stored in table's internal pbuffer.
 * - the function returns pbuffer->data.
 */
extern pprod_t **pprods_for_bvpoly(term_table_t *table, bvpoly_t *p);


/*
 * Reset the internal pbuffer
 */
static inline void term_table_reset_pbuffer(term_table_t *table) {
  pvector_reset(&table->pbuffer);
}





/*
 * ACCESS TO TERMS
 */

/*
 * From a term index i
 */
static inline bool valid_term_idx(term_table_t *table, int32_t i) {
  return 0 <= i && i < table->nelems;
}

static inline bool good_term_idx(term_table_t *table, int32_t i) {
  return valid_term_idx(table, i) && table->kind[i] != UNUSED_TERM;
}

static inline type_t type_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return table->type[i];
}

static inline term_kind_t kind_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return table->kind[i];
}

// get descriptor converted to an appropriate type
static inline int32_t integer_value_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return table->desc[i].integer;
}

static inline composite_term_t *composite_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (composite_term_t *) table->desc[i].ptr;
}

static inline select_term_t *select_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (select_term_t *) table->desc[i].ptr;
}

static inline pprod_t *pprod_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (pprod_t *) table->desc[i].ptr;
}

static inline rational_t *rational_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return &table->desc[i].rational;
}

static inline polynomial_t *polynomial_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (polynomial_t *) table->desc[i].ptr;
}

static inline bvconst64_term_t *bvconst64_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (bvconst64_term_t *) table->desc[i].ptr;
}

static inline bvconst_term_t *bvconst_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (bvconst_term_t *) table->desc[i].ptr;
}

static inline bvpoly64_t *bvpoly64_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (bvpoly64_t *) table->desc[i].ptr;
}

static inline bvpoly_t *bvpoly_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return (bvpoly_t *) table->desc[i].ptr;
}


// bitsize of bitvector terms
static inline uint32_t bitsize_for_idx(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  return bv_type_size(table->types, table->type[i]);
}


/*
 * Access components using term occurrence t
 */
static inline bool good_term(term_table_t *table, term_t t) {
  return good_term_idx(table, index_of(t));
}

static inline bool bad_term(term_table_t *table, term_t t) {
  return ! good_term(table, t);
}

static inline term_kind_t term_kind(term_table_t *table, term_t t) {
  return kind_for_idx(table, index_of(t));
}

static inline type_t term_type(term_table_t *table, term_t t) {
  return type_for_idx(table, index_of(t));
}

static inline type_kind_t term_type_kind(term_table_t *table, term_t t) {
  return type_kind(table->types, term_type(table, t));
}


// Checks on the type of t
static inline bool is_arithmetic_term(term_table_t *table, term_t t) {
  return is_arithmetic_type(term_type(table, t));
}

static inline bool is_boolean_term(term_table_t *table, term_t t) {
  return is_boolean_type(term_type(table, t));
}

static inline bool is_real_term(term_table_t *table, term_t t) {
  return is_real_type(term_type(table, t));
}

static inline bool is_integer_term(term_table_t *table, term_t t) {
  return is_integer_type(term_type(table, t));
}

static inline bool is_bitvector_term(term_table_t *table, term_t t) {
  return term_type_kind(table, t) == BITVECTOR_TYPE;
}

static inline bool is_scalar_term(term_table_t *table, term_t t) {
  return term_type_kind(table, t) == SCALAR_TYPE;
}

static inline bool is_function_term(term_table_t *table, term_t t) {
  return term_type_kind(table, t) == FUNCTION_TYPE;
}

static inline bool is_tuple_term(term_table_t *table, term_t t) {
  return term_type_kind(table, t) == TUPLE_TYPE;
}


// Bitsize of term t
static inline uint32_t term_bitsize(term_table_t *table, term_t t) {
  return bitsize_for_idx(table, index_of(t));
}





/*
 * GARBAGE COLLECTION
 */

/*
 * Mark and sweep mechanism:
 * - nothing gets deleted until an explicit call to term_table_gc
 * - before calling the garbage collector, the root terms must be 
 *   marked by calling set_gc_mark.
 * - all the terms that can be accessed by a name (i.e., all the terms
 *   that are present in the symbol table) are also considered root terms.
 *
 * Garbage collection process:
 * - The predefined term (bool_const) and all the terms that are present
 *   in the symbol table are marked.
 * - The marks are propagated to subterms, types, and power products.
 * - Every term that's not marked is deleted.
 * - The type and power-product tables' own garbage collectors are called.
 * - Finally all the marks are cleared.
 */

/*
 * Set or clear the mark on a term i. If i is marked, it is preserved
 * on the next call to the garbage collector (and all terms rechable
 * from i are preserved too).  If the mark is cleared, i may be deleted.
 */
static inline void term_table_set_gc_mark(term_table_t *table, int32_t i) {
  assert(good_term_idx(table, i));
  set_bit(table->mark, i);
}

static inline void term_table_clr_gc_mark(term_table_t *table, int32_t i) {
  assert(valid_term_idx(table, i));
  clr_bit(table->mark, i);
}


/*
 * Test whether i is marked
 */
static inline bool term_idx_is_marked(term_table_t *table, int32_t i) {
  assert(valid_term_idx(table, i));
  return tst_bit(table->mark, i);
}


/*
 * Call the garbage collector:
 * - every term reachable from a marked term is preserved.
 * - recursively calls type_table_gc and pprod_table_gc
 * - then all the marks are cleared.
 */
extern void term_table_gc(term_table_t *table);


#endif /* __TERMS_H */
