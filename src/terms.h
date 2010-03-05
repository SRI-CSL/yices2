/*
 * Internal term representation
 * ----------------------------
 *
 * This module provides low-level functions for term construction,
 * and management of a global term table.
 * 
 * Changes:
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
 * TODO: Rewrite the whole thing. 
 * - Use the same data structures for all composite terms, rather than one per term kind.
 * - Avoid the indirection caused by using arithmetic and bitvector variables.
 *
 * The internal terms include:
 * 1) constants:
 *    - constants of uninterpreted/scalar/boolean types
 *    - global uninterpreted constants
 * 2) constructed terms used by the core:
 *    - ite c t1 t2
 *    - or t1 .... t_n
 *    - not t
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
 * 4) arithmetic terms and atoms
 *    - terms are arbitrary polynomials
 *    - atoms are either of the form (p == 0) or (p >= 0)
 *      where p is a polynomial.
 *    - atoms x - y == 0 are rewritten to (x = y)
 * 5) bitvector terms and atoms
 *    - three kinds of terms:
 *      bv_arith_term: polynomials with bit-vector variables
 *      bv_logical_term: array of bit expressions
 *      bv_const_term: bitvector constant
 *    - atoms: three binary predicates
 *      bv_eq t1 t2
 *      bv_ge t1 t2 (unsigned comparison: t1 >= t2)
 *      bv_sge t1 t2 (signed comparison: t1 >= t2)
 *    - uninterpreted bitvector operations (we use this when we want
 *      to use hashconsing on bitvector operations that can't be
 *      represented otherwise. The translation to the bitvector solver
 *      gives the interpretation.).
 *
 * Every term is an index in a global term table.
 *
 * For every term, we keep:
 * - its type (index in the type table)
 * - name: either a string or NULL
 * - a tag: what kind of term it is
 * - a descriptor (depends on the kind and type)
 * - a theory var: either an arithmetic variable or a bitvector variable, or null.
 */

#ifndef __TERMS_H
#define __TERMS_H 1

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "int_hash_tables.h"
#include "symbol_tables.h"
#include "bitvectors.h"
#include "int_queues.h"

#include "types.h"
#include "polynomials.h"
#include "bv_constants.h"
#include "bvarith_expr.h"
#include "bvlogic_expr.h"
#include "bit_expr.h"


/*
 * Term indices = signed integers
 */
typedef int32_t term_t;

/*
 * Error value
 */
#define NULL_TERM INT32_MIN


/*
 * Upper limit on the size of a term table.
 * - no more than (2^31 - 1) elements
 * - we also want to ensure that no numerical overflow
 *   occurs when (table->size * sizeof(ptr type)) is computed (for malloc).
 *   SIZE_MAX/8 should be a safe limit on 64bit and 32bit architectures.
 */
#if INT32_MAX < (SIZE_MAX/8)
#define MAX_TERMS INT32_MAX
#else
#define MAX_TERMS (SIZE_MAX/8)
#endif


/*
 * Other limits for term creation
 * - max number of variables in a forall term
 * - max arity in an apply/tuple/update/distinct term
 * These bounds ensure no numerical overflow when allocating 
 * term descriptors.
 */
#define MAX_BOUND_VARIABLES (INT32_MAX/16)
#define MAX_TERM_ARITY (INT32_MAX/16)


/*
 * Term kinds
 */
typedef enum {
  UNUSED_TERM,    // deleted terms

  CONSTANT_TERM,  // constant of uninterpreted/scalar/boolean types
  UNINTERPRETED_TERM,  // uninterpreted constants
  VARIABLE,       // quantified variable

  NOT_TERM,
  ITE_TERM,
  EQ_TERM,        // equality between uninterpreted terms
  APP_TERM,       // application of an uninterpreted function
  OR_TERM,
  TUPLE_TERM,     // tuple constructor
  SELECT_TERM,    // tuple projection
  UPDATE_TERM,    // function update
  DISTINCT_TERM,  // distinct t_1 ... t_n
  FORALL_TERM,

  ARITH_TERM,       // polynomial
  ARITH_EQ_ATOM,    // atom p == 0
  ARITH_GE_ATOM,    // atom p >= 0
  ARITH_BINEQ_ATOM, // equality: (t1 == t2)  (arithmetic terms)

  BV_LOGIC_TERM,   // array of bits
  BV_ARITH_TERM,   // polynomial
  BV_CONST_TERM,   // bitvector constant 

  BV_EQ_ATOM,      // equality: (t1 == t2)
  BV_GE_ATOM,      // unsigned comparison: (t1 >= t2)
  BV_SGE_ATOM,     // signed comparison (t1 >= t2)

  BV_APPLY_TERM,   // uninterpreted bitvector operation
} term_kind_t;


/*
 * Predefined bvoperators for BV_APPLY_TERM
 */
typedef enum bvop {
  BVOP_DIV,
  BVOP_REM,
  BVOP_SDIV,
  BVOP_SREM,
  BVOP_SMOD,
  BVOP_SHL,
  BVOP_LSHR,
  BVOP_ASHR,
} bvop_t;

/*
 * Predefined term ids
 */
enum {
  false_term_id = 0,
  true_term_id = 1,
};



/*
 * Descriptors of composite terms
 */
typedef struct {
  term_t cond, then_arg, else_arg;  // (ite c t e)
} ite_term_t;

typedef struct {
  term_t left, right;   // (eq left right)
} eq_term_t;

// (app fun arg[0] ... arg[n-1])
typedef struct {
  int32_t nargs;  // number of arguments
  term_t fun;
  term_t arg[0];  // resized accordingly
} app_term_t;

// (or arg[0] ... arg[n-1])
typedef struct {
  int32_t nargs;  // at least 2
  term_t arg[0];
} or_term_t;

// (mk-tuple arg[0] ... arg[n-1])
typedef struct {
  int32_t nargs; // could be omitted. It's implicit in the type.
  term_t arg[0];
} tuple_term_t;

// (select i tuple)
typedef struct {
  int32_t idx;
  term_t arg;
} select_term_t;

// (update f (arg[0]...arg[n-1]) newvalue)
typedef struct {
  term_t fun;
  term_t newval;
  int32_t nargs; // could be omitted too (type of f has the info)
  term_t arg[0];
} update_term_t;

// (distinct arg[0] ... arg[n])
typedef struct {
  int32_t nargs;
  term_t arg[0];
} distinct_term_t;

// (forall (x_1::t_1 ... x_n::t_n) body)
typedef struct {
  int32_t nvars;
  term_t body;
  term_t var[0]; // variables x_1 to x_n
} forall_term_t;


// arithmetic equality
typedef struct {
  term_t left, right;
} arith_bineq_t;

// bitvector constant (cf. bv_constant.h)
typedef struct {
  int32_t nbits;
  uint32_t bits[0]; // real size = ceil(nbits/32)
} bvconst_term_t;

// bitvector atom: binary predicate
typedef struct {
  term_t left, right;
} bv_atom_t;

// uninterpreted bitvector operators
// only binary operators are supported
typedef struct {
  uint32_t op;
  term_t arg0, arg1; 
} bvapply_term_t;

// descriptor = either an integer or a pointer
typedef union {
  int32_t integer;
  void *ptr;
} term_desc_t;

 
/*
 * Term table: valid terms have indices between 0 and nelems - 1
 *
 * For each i between 0 and nelems - 1
 * - kind[i] = term kind
 * - type[i] = type
 * - name[i] = string or NULL
 * - theory_var[i] = index of an arithmetic or bit-vector variable
 *   attached to the term (-1 if no variable attached).
 * - root: bitvector for garbage collection
 *
 * Other components:
 * - type_table = pointer to an associated type table
 * - arith_manager = manager for arithmetic variables
 * - bv_manager = manager for bitvector variables
 * - size = size of all the term-indexed arrays above
 * - free_idx = start of the free list.
 * - stbl = symbol table that maps names to terms
 * - htbl = hash table for hash consing
 * 
 * - buffer = array of terms or types for intermediate computations
 * - buffer_size = its size
 *
 * Components used for garbage collection
 * - gc_mark: bit vector for marking live terms
 * - gc_mark_queue: for marking terms and subterms
 * - gc_bit_marker: for marking terms reachable from bit nodes,
 *   without visiting them several times.
 * - gc_notifier: function called before garbage collection,
 *   can be used to mark terms that must be kept.
 */

/*
 * Auxiliary marker object for tracking terms reachable from bits, via the chain
 * variable nodes --> bitvector variables --> term indices
 */
typedef struct {
  bit_marking_obj_t marker;      // marking object proper
  // additional components used by the callback function in marker:
  node_table_t *nodes;
  polynomial_manager_t *pm;
  byte_t *mark;    // term mark
  int_queue_t *q;  // term queue
} term_bit_marker_t;


typedef struct term_table_s term_table_t;

typedef void (*term_gc_notifier_t)(term_table_t *tbl);

struct term_table_s {
  unsigned char *kind;
  type_t *type;
  term_desc_t *desc;
  char **name;
  int32_t *theory_var;
  byte_t *root;

  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  type_table_t *type_table;
  arithvar_manager_t *arith_manager;
  bv_var_manager_t *bv_manager;

  int_htbl_t htbl;
  stbl_t stbl;

  int32_t buffer_size;
  int32_t *buffer;

  // Garbage collection 
  byte_t *gc_mark;
  int_queue_t *gc_mark_queue;
  term_bit_marker_t *gc_bit_marker;
  term_gc_notifier_t gc_notifier;
};


/*
 * Null-var marker for theory_var[i]
 */
enum {
  null_theory_var = -1,
};



/*
 * INITIALIZATION
 */

/*
 * Initialize table:
 * - n = initial size 
 * - ttbl = attached type table
 * - arith_m = attached arithmetic variable manager
 * - bv_m = attached bitvectore variable manager
 */
extern void init_term_table(term_table_t *table, uint32_t n, type_table_t *ttbl, 
			    arithvar_manager_t *arith_m, bv_var_manager_t *bv_m);

/*
 * Delete all terms and descriptors, symbol table, hash table, etc.
 * - type_table and arith_manager are not deleted.
 */ 
extern void delete_term_table(term_table_t *table);




/*
 * TERM CONSTRUCTORS
 * 
 * These functions do not check for type correctness.
 * They just do hash_consing.
 */

// Predefined constants: true and false
static inline term_t true_term(term_table_t *table) {
  return true_term_id;
}

static inline term_t false_term(term_table_t *table) {
  return false_term_id;
}

/*
 * Unique constant of the given type and index.
 * - tau must be uninterpreted or scalar
 * - if tau is scalar of cardinality n, then index must be between 0 and n-1
 */
extern term_t constant_term(term_table_t *table, type_t tau, int32_t index);

/*
 * Declare a new uninterpreted constant of type tau.
 */
extern term_t new_uninterpreted_term(term_table_t *table, type_t tau);

/*
 * Variable of type tau. Index i is used to distinguish it from other variables
 * of the same type.
 */
extern term_t variable(term_table_t *table, type_t tau, int32_t index);


/*
 * Composite terms: all must be well typed.
 * - for if-then-else, tau must be the super_type of then_term and else_term types.
 * - for app_term, or_term, update_term, distinct_term n must be positive and 
 *   less than MAX_TERM_ARITY
 * - for forall_term, n must be positive and less than MAX_BOUND_VARIABLES
 */
extern term_t ite_term(term_table_t *table, term_t cond, term_t then_term, 
		       term_t else_term, type_t tau);

extern term_t eq_term(term_table_t *table, term_t left, term_t right);
extern term_t app_term(term_table_t *table, term_t fun, int32_t n, term_t arg[]);
extern term_t or_term(term_table_t *table, int32_t n, term_t arg[]);
extern term_t not_term(term_table_t *table, term_t arg);
extern term_t tuple_term(term_table_t *table, int32_t n, term_t arg[]);
extern term_t select_term(term_table_t *table, int32_t index, term_t tuple);
extern term_t update_term(term_table_t *table, term_t fun, int32_t n, term_t arg[], term_t new_v);
extern term_t distinct_term(term_table_t *table, int32_t n, term_t arg[]);
extern term_t forall_term(term_table_t *table, int32_t n, term_t var[], term_t body);


/*
 * Arithmetic terms and atoms: two sources for construction.
 * - either an arith_buffer b or a monomial array p, which must be normalized.
 * - for monomial array p, n must be its length = number of monomials
 *   (excluding end marker).
 * - tag determines the kind of object created: tag must be ARITH_TERM,
 *   ARITH_EQ_ATOM, or ARITH_GE_ATOM.
 */
extern term_t arith_object_from_buffer(term_table_t *table, term_kind_t tag, arith_buffer_t *b);
extern term_t arith_object_from_monarray(term_table_t *table, term_kind_t tag, monomial_t *p, int32_t n);

/*
 * Construction of arithmetic terms and atoms
 */
static inline term_t arith_term(term_table_t *table, arith_buffer_t *b) {
  return arith_object_from_buffer(table, ARITH_TERM, b);
}

static inline term_t arith_eq_atom(term_table_t *table, arith_buffer_t *b) {
  return arith_object_from_buffer(table, ARITH_EQ_ATOM, b);
}

static inline term_t arith_geq_atom(term_table_t *table, arith_buffer_t *b) {
  return arith_object_from_buffer(table, ARITH_GE_ATOM, b);
}

/*
 * Variants: use monomial array rather than arith_buffer
 */
static inline term_t arith_term_from_monarray(term_table_t *table, monomial_t *p, int32_t n) {
  return arith_object_from_monarray(table, ARITH_TERM, p, n);
}

static inline term_t arith_eq_atom_from_monarray(term_table_t *table, monomial_t *p, int32_t n)  {
  return arith_object_from_monarray(table, ARITH_EQ_ATOM, p, n);
}

static inline term_t arith_geq_atom_from_monarray(term_table_t *table, monomial_t *p, int32_t n) {
  return arith_object_from_monarray(table, ARITH_GE_ATOM, p, n);
}


/*
 * Simple equality between two arithmetic terms (l == r)
 */
extern term_t arith_bineq_atom(term_table_t *table, term_t l, term_t r);




/*
 * Bitvector terms
 * - bvarith_term: b = bitvector polynomial
 * - bvlogic_term: b = array of bit expressions
 * - bvconst_term: n = number of bits, b = array of words
 * in all three cases, b must be normalized.
 */
extern term_t bvarith_term(term_table_t *table, bvarith_buffer_t *b);
extern term_t bvlogic_term(term_table_t *table, bvlogic_buffer_t *b);
extern term_t bvconst_term(term_table_t *table, int32_t n, uint32_t *b);


/*
 * Bitvector atoms
 */
extern term_t bitvector_atom(term_table_t *table, term_kind_t tag, term_t l, term_t r);

static inline term_t bveq_atom(term_table_t *table, term_t l, term_t r) {
  return bitvector_atom(table, BV_EQ_ATOM, l, r);
}

static inline term_t bvge_atom(term_table_t *table, term_t l, term_t r) {
  return bitvector_atom(table, BV_GE_ATOM, l, r);
}

static inline term_t bvsge_atom(term_table_t *table, term_t l, term_t r) {
  return bitvector_atom(table, BV_SGE_ATOM, l, r);
}


/*
 * Binary bitvector operations.
 * - op identifies the operator,
 * - l and r are the arguments (bitvectors of the same size)
 * - the result has the same type as l and r
 */
extern term_t bvapply_term(term_table_t *table, uint32_t op, term_t l, term_t r);



/*
 * NAMES
 */

/*
 * IMPORTANT: we use reference counting on character strings as
 * implemented in memalloc.h.
 *
 * - Parameter "name" in set_term_name must be constructed via the clone_string function.
 *   That's not necessary for get_type_by_name or remove_type_name.
 * - when name is added to the term table, its reference counter is increased by 1 or 2
 * - when remove_term_name is called for an existing symbol, the symbol's reference counter 
 *   is decremented
 * - when the table is deleted (via delete_type_table), the reference counters
 *   of all symbols present in table are also decremented.
 */

/*
 * Assign name to term t.
 *
 * If name is already mapped to another term t' then the previous mapping
 * is hidden. Next calls to get_term_by_name will return t. After a 
 * call to remove_term_name, the mapping name --> t is removed and 
 * the previous mapping name --> t' is revealed.
 *
 * Warning: name is stored as a pointer, no copy is made; name must be 
 * created via the clone_string function in memalloc.h.
 */
extern void set_term_name(term_table_t *table, term_t t, char *name);

/*
 * Get term with the given name (or NULL_TERM)
 */
extern term_t get_term_by_name(term_table_t *table, char *name);

/*
 * Remove term name.
 */
extern void remove_term_name(term_table_t *table, char *name);




/*
 * THEORY VARIABLES
 */

/*
 * Return the arithmetic variable associated with term t.
 * - t must be an arithmetic term (type = int or real)
 * - a new variable if allocated in table->arith_manager if t 
 *   does not have a variable attached already.
 * - otherwise, table->theory_var[t] is returned.
 */
extern int32_t get_arithmetic_variable(term_table_t *table, term_t t);

/*
 * Return the bitvector variable associated with term t
 * - t must be a bitvector term
 * - a new variable is allocated in table->bv_manager if t does
 *   not have an existing theory variable, otherwise that variable
 *   is returned.
 */
extern int32_t get_bitvector_variable(term_table_t *table, term_t t);





/*
 * GARBAGE COLLECTION
 */

/*
 * Support for type-table garbage collection
 * - mark all types in the term table to prevent them from
 *   being removed from the type table
 * - must be called only via the gc_notifier attached to the type
 *   table m->type_table.
 */
extern void mark_term_types(term_table_t *m);


/*
 * Set or clear the root flag of term t
 * If the root flag is set, t is preserved by the garbage collector
 * Newly created terms have root flag 0 (so they may be deleted).
 */
extern void set_root_term_flag(term_table_t *table, term_t t);
extern void clr_root_term_flag(term_table_t *table, term_t t);

/*
 * Set gc notifier
 */
static inline void set_term_gc_notifier(term_table_t *table, term_gc_notifier_t fun) {
  table->gc_notifier = fun;
}

/*
 * Mark term t and all its subterms to preserve them from garbage collection
 * This function must not be called outside the gc_notifier.
 */
extern void gc_mark_term(term_table_t *table, term_t i);

/*
 * Call the garbage collector
 */
extern void term_table_garbage_collection(term_table_t *table);



/*
 * ACCESS TO TERMS
 */

// Generic
static inline bool valid_term(term_table_t *table, term_t t) {
  return 0 <= t && t < table->nelems;
}

static inline term_kind_t term_kind(term_table_t *table, term_t t) {
  assert(valid_term(table, t));
  return table->kind[t];
}

static inline bool good_term(term_table_t *table, term_t t) {
  return valid_term(table, t) && table->kind[t] != UNUSED_TERM;
}

static inline bool bad_term(term_table_t *table, term_t t) {
  return ! good_term(table, t);
}

static inline type_t term_type(term_table_t *table, term_t t) {
  assert(good_term(table, t));
  return table->type[t];  
}

static inline type_kind_t term_type_kind(term_table_t *table, term_t t) {
  return type_kind(table->type_table, term_type(table, t));
}

static inline char *term_name(term_table_t *table, term_t t) {
  assert(good_term(table, t));
  return table->name[t];
}

static inline int32_t term_theory_var(term_table_t *table, term_t t) {
  assert(good_term(table, t));
  return table->theory_var[t];
}

static inline bool term_has_theory_var(term_table_t *table, term_t t) {
  return term_theory_var(table, t) != null_theory_var;
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


// Functions that depend on term kind
static inline int32_t constant_term_index(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == CONSTANT_TERM);
  return table->desc[t].integer;
}

static inline int32_t variable_index(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == VARIABLE);
  return table->desc[t].integer;
}

static inline term_t not_term_arg(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == NOT_TERM);
  return table->desc[t].integer;
}

static inline ite_term_t *ite_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == ITE_TERM);
  return (ite_term_t *) table->desc[t].ptr;
}

static inline term_t ite_term_cond(term_table_t *table, term_t t) {
  return ite_term_desc(table, t)->cond;
}

static inline term_t ite_term_then(term_table_t *table, term_t t) {
  return ite_term_desc(table, t)->then_arg;
}

static inline term_t ite_term_else(term_table_t *table, term_t t) {
  return ite_term_desc(table, t)->else_arg;
}

static inline eq_term_t *eq_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == EQ_TERM);
  return (eq_term_t *) table->desc[t].ptr;
}

static inline term_t eq_term_left(term_table_t *table, term_t t) {
  return eq_term_desc(table, t)->left;
}

static inline term_t eq_term_right(term_table_t *table, term_t t) {
  return eq_term_desc(table, t)->right;
}

static inline app_term_t *app_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == APP_TERM);
  return (app_term_t *) table->desc[t].ptr;
}

static inline term_t app_term_fun(term_table_t *table, term_t t) {
  return app_term_desc(table, t)->fun;
}

static inline int32_t app_term_nargs(term_table_t *table, term_t t) {
  return app_term_desc(table, t)->nargs;
}

static inline term_t app_term_arg(term_table_t *table, term_t t, int32_t i) {
  assert(0 <= i && i < app_term_nargs(table, t));
  return app_term_desc(table, t)->arg[i];
}

static inline or_term_t *or_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == OR_TERM);
  return (or_term_t *) table->desc[t].ptr;
}

static inline int32_t or_term_nargs(term_table_t *table, term_t t) {
  return or_term_desc(table, t)->nargs;
}

static inline term_t or_term_arg(term_table_t *table, term_t t, int32_t i) {
  assert(0 <= i && i < or_term_nargs(table, t));
  return or_term_desc(table, t)->arg[i];
}

static inline tuple_term_t *tuple_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == TUPLE_TERM);
  return (tuple_term_t *) table->desc[t].ptr;
}

static inline int32_t tuple_term_nargs(term_table_t *table, term_t t) {
  return tuple_term_desc(table, t)->nargs;
}

static inline term_t tuple_term_arg(term_table_t *table, term_t t, int32_t i) {
  assert(0 <= i && i < tuple_term_nargs(table, t));
  return tuple_term_desc(table, t)->arg[i];
}

static inline select_term_t *select_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == SELECT_TERM);
  return (select_term_t *) table->desc[t].ptr;
}

static inline int32_t select_term_index(term_table_t *table, term_t t) {
  return select_term_desc(table, t)->idx;
}

static inline term_t select_term_arg(term_table_t *table, term_t t) {
  return select_term_desc(table, t)->arg;
}

static inline update_term_t *update_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == UPDATE_TERM);
  return (update_term_t *) table->desc[t].ptr;
}

static inline term_t update_term_fun(term_table_t *table, term_t t) {
  return update_term_desc(table, t)->fun;
}

static inline term_t update_term_newval(term_table_t *table, term_t t) {
  return update_term_desc(table, t)->newval;
}

static inline int32_t update_term_nargs(term_table_t *table, term_t t) {
  return update_term_desc(table, t)->nargs;
}

static inline term_t update_term_arg(term_table_t *table, term_t t, int32_t i) {
  assert(0 <= i && i < update_term_nargs(table, t));
  return update_term_desc(table, t)->arg[i];
}

static inline distinct_term_t *distinct_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == DISTINCT_TERM);
  return (distinct_term_t *) table->desc[t].ptr;
}

static inline int32_t distinct_term_nargs(term_table_t *table, term_t t) {
  return distinct_term_desc(table, t)->nargs;
}

static inline term_t distinct_term_arg(term_table_t *table, term_t t, int32_t i) {
  assert(0 <= i && i < distinct_term_nargs(table, t));
  return distinct_term_desc(table, t)->arg[i];
}

static inline forall_term_t *forall_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == FORALL_TERM);
  return (forall_term_t *) table->desc[t].ptr;
}

static inline term_t forall_term_body(term_table_t *table, term_t t) {
  return forall_term_desc(table, t)->body;
}

static inline int32_t forall_term_nvars(term_table_t *table, term_t t) {
  return forall_term_desc(table, t)->nvars;
}

static inline term_t forall_term_var(term_table_t *table, term_t t, int32_t i) {
  assert(0 <= i && i < forall_term_nvars(table, t));
  return forall_term_desc(table, t)->var[i];
}

// arithmetic
static inline polynomial_t *arith_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == ARITH_TERM || term_kind(table, t) == ARITH_EQ_ATOM || 
	 term_kind(table, t) == ARITH_GE_ATOM);
  return (polynomial_t *) table->desc[t].ptr;  
}

static inline polynomial_t *arith_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == ARITH_TERM);
  return (polynomial_t *) table->desc[t].ptr;
}

static inline polynomial_t *arith_atom_desc(term_table_t *table, term_t t) {
  assert((term_kind(table, t) == ARITH_EQ_ATOM) || (term_kind(table, t) == ARITH_GE_ATOM));
  return (polynomial_t *) table->desc[t].ptr;
}

static inline arith_bineq_t *arith_bineq_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == ARITH_BINEQ_ATOM);
  return (arith_bineq_t *) table->desc[t].ptr;
}

static inline term_t arith_bineq_left(term_table_t *table, term_t t) {
  return arith_bineq_desc(table, t)->left;
}

static inline term_t arith_bineq_right(term_table_t *table, term_t t) {
  return arith_bineq_desc(table, t)->right;
}

// bitvectors
static inline bvarith_expr_t *bvarith_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == BV_ARITH_TERM);
  return (bvarith_expr_t *) table->desc[t].ptr;
}

static inline bvlogic_expr_t *bvlogic_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == BV_LOGIC_TERM);
  return (bvlogic_expr_t *) table->desc[t].ptr;
}

static inline bvconst_term_t *bvconst_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == BV_CONST_TERM);
  return (bvconst_term_t *) table->desc[t].ptr;
}

static inline uint32_t *bvconst_term_value(term_table_t *table, term_t t) {
  return bvconst_term_desc(table, t)->bits;
}

static inline bv_atom_t *bvatom_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == BV_EQ_ATOM || term_kind(table, t) == BV_GE_ATOM ||
	 term_kind(table, t) == BV_SGE_ATOM);
  return (bv_atom_t *) table->desc[t].ptr;
}

static inline term_t bvatom_lhs(term_table_t *table, term_t t) {
  return bvatom_desc(table, t)->left;
}

static inline term_t bvatom_rhs(term_table_t *table, term_t t) {
  return bvatom_desc(table, t)->right;
}

// Binary bitvector operations
static inline bvapply_term_t *bvapply_term_desc(term_table_t *table, term_t t) {
  assert(term_kind(table, t) == BV_APPLY_TERM);
  return (bvapply_term_t *) table->desc[t].ptr;
}

static inline uint32_t bvapply_term_op(term_table_t *table, term_t t) {
  return bvapply_term_desc(table, t)->op;
}

static inline term_t bvapply_term_arg0(term_table_t *table, term_t t) {
  return bvapply_term_desc(table, t)->arg0;
}

static inline term_t bvapply_term_arg1(term_table_t *table, term_t t) {
  return bvapply_term_desc(table, t)->arg1;
}


// Number of bits in bit-vector terms
static inline int32_t bvarith_term_bitsize(term_table_t *table, term_t t) {
  return bvarith_term_desc(table, t)->size;
}

static inline int32_t bvlogic_term_bitsize(term_table_t *table, term_t t) {
  return bvlogic_term_desc(table, t)->nbits;
}

static inline int32_t bvconst_term_bitsize(term_table_t *table, term_t t) {
  return bvconst_term_desc(table, t)->nbits;
}

// generic form: use the type. t must have bitvector type.
static inline int32_t term_bitsize(term_table_t *table, term_t t) {
  assert(good_term(table, t));
  return bv_type_size(table->type_table, table->type[t]);
}


#endif /* __TERMS_H */
