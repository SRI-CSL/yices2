/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Type descriptors and type table. Includes hash-consing and support
 * for attaching names to types.
 *
 * Changes:
 *
 * March 24, 2007. Removed mandatory name for uninterpreted
 * and scalar types. Replaced by functions to create new
 * uninterpreted/scalar types with no names. If names are
 * needed they can be added as for any other types.
 *
 * Also removed built-in names "int" "bool"
 * "real" for primitive types.
 *
 *
 * March 08, 2010. Updates to the data structures:
 * - store the pseudo cardinality in the type table (rather
 *   than computing it on demand)
 * - added flags for each type tau to indicate
 *   - whether tau is finite
 *   - whether tau is a unit type (finite type with cardinality 1)
 *   - whether card[tau] is exact. (If card[tau] is exact, then
 *     it's the cardinality of tau. Otherwise, card[tau] is set to
 *      UINT32_MAX.)
 * - added hash_maps to use as caches to make sure recursive
 *   functions such as is_subtype, super_type, and inf_type don't
 *   explode.
 *
 * August 2011: Added type variables and substitutions to support
 * SMT-LIB 2.0.
 *
 * July 2012:
 * - Added type instances (do deal with abstract type constructors)
 * - Merged type_macros.c into this module.
 *
 * Limits are now imported from yices_limits.h:
 * - YICES_MAX_TYPES = maximal size of a type table
 * - YICES_MAX_ARITY = maximal arity for tuples and function types
 * - YICES_MAX_BVSIZE = maximal bitvector size
 */

#ifndef __TYPES_H
#define __TYPES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#include "utils/int_hash_map.h"
#include "utils/int_hash_map2.h"
#include "utils/int_hash_tables.h"
#include "utils/indexed_table.h"
#include "utils/symbol_tables.h"
#include "utils/tuple_hash_map.h"

#include "yices_types.h"


/*
 * Different kinds of types:
 * - primitive types are BOOL, INT, REAL,
 *   BITVECTOR[n] for any n (0 < n <= MAX_BVSIZE)
 * - declared types can be either scalar or uninterpreted
 * - constructed types: tuple types and function types
 *
 * New kinds to support polymorphism
 * - type variables
 * - instance of an abstract type constructor (e.g., if we have
 *   a constructor list[T] then we can create list[int],
 *   list[list[U]])
 *
 * The enumeration order is important. The atomic type kinds
 * must be smaller than non-atomic kinds TUPLE and FUNCTION.
 */
typedef enum {
  UNUSED_TYPE,    // for deleted types
  BOOL_TYPE,
  INT_TYPE,
  REAL_TYPE,
  BITVECTOR_TYPE,
  SCALAR_TYPE,
  UNINTERPRETED_TYPE,
  VARIABLE_TYPE,
  TUPLE_TYPE,
  FUNCTION_TYPE,
  INSTANCE_TYPE,
} type_kind_t;

#define NUM_TYPE_KINDS (INSTANCE_TYPE+1)

/*
 * Ids of the predefined types
 */
enum {
  bool_id = 0,
  int_id = 1,
  real_id = 2,
};


/*
 * Descriptors of tuple and function types.
 */
typedef struct {
  uint32_t nelem; // number of components
  type_t elem[0]; // elem[0] .. elem[nelem-1]: component types
} tuple_type_t;

typedef struct {
  type_t range;     // range type
  uint32_t ndom;    // number of domain types
  type_t domain[0]; // domain[0] .. domain[ndom - 1]: domain types
} function_type_t;


/*
 * Descriptor of a type instance:
 * - cid = id of a type constructor
 * - arity = number of type parameters
 * - param[0 ... arity-1] = parameters
 *
 * NOTE: this is used for something like (Set T) when we instantiate T
 * with a real type. The cid is the index of a type constructor in
 * the macro table. For now, an instance type is treated like an
 * uninterpreted type.
 */
typedef struct {
  int32_t cid;
  uint32_t arity;
  type_t param[0];
} instance_type_t;


/*
 * TYPE MACROS
 */

/*
 * Macros are intended to support SMT LIB2 commands such as
 *     (declare-sort <name> <arity>)
 * and (define-sort <name> (<list-of-names>) <sort>)
 *
 * With these constructs, we create a macro descriptor
 * that consists of a name, an arity, a body, and a finite
 * array of type variables.
 * - for (declare-sort <name> <arity> )
 *   the macro descriptor is as follows:
 *       name = <name>
 *       arity = <arity>
 *       body = NULL_TYPE
 *       vars = none
 * - for (define-sort <name> (<X1> ... <Xn>) <sort> ),
 *   the macro descriptor is
 *       name = <name>
 *       arity = n
 *       body = <sort>
 *       vars = [<X1> ... <Xn>]
 *
 * We also need to keep track of existing macro applications
 * in a hash table. The hash table contains:
 *     [macro-id, type1, ..., type_n --> type]
 * where macro-id refers to a macro or arity n.
 */

/*
 * Macro descriptor
 */
typedef struct type_macro_s {
  char *name;
  uint32_t arity;
  type_t body;
  type_t vars[0]; // real size = arity unless body = NULL_TYPE
} type_macro_t;



/*
 * Maximal arity: it must satisfy two constraints
 * - max_arity <= TUPLE_HMAP_MAX_ARITY
 * - sizeof(type_macro_t) + sizeof(type_t) * max_arity <= UINT32_MAX
 * - a limit of 128 should be more than enough
 */
#define TYPE_MACRO_MAX_ARITY 128

/*
 * The type of an element in the macro table.
 */
typedef struct type_mtbl_elem_s {
  union {
    indexed_table_elem_t elem;
    type_macro_t *data;
  };
} type_mtbl_elem_t;

/*
 * Table of macros
 * - macros are identified by an index
 * - the table maps the index to a macro descriptor
 * - it also includes a symbol table that maps a macro name
 *   to its id, and a hash table that stores macro instances
 */
typedef struct type_mtbl_s {
  indexed_table_t macros;
  stbl_t stbl;          // symbol table
  tuple_hmap_t cache;   // existing macro instances
} type_mtbl_t;



/*
 * Default and maximal size
 */
#define TYPE_MACRO_DEF_SIZE   20
#define TYPE_MACRO_MAX_SIZE   (UINT32_MAX/sizeof(void*))


typedef struct type_desc_s {
  union {
    indexed_table_elem_t elem;
    uint32_t integer;
    void *ptr;
  };
  
  /* The kind of type. */
  uint8_t kind;

  /*
   *    bit 0 of flag is 1 if i is finite
   *    bit 1 of flag is 1 if i is a unit type
   *    bit 2 of flag is 1 if card[i] is exact
   *    bit 3 of flag is 1 if i has no strict supertype
   *    bit 4 of flag is 1 if i has no strict subtype
   *
   *    bit 5 of flag is 1 if i is a ground type (i.e., no variables
   *    occur in i). If this bit is '0', then bits 0 to 4 are not used,
   *    but they must all be set to '0' too.
   *
   *    bit 7 is used as a mark during garbage collection
   */
  uint8_t flags;

  /* Cardinality, of UINT32_MAX if infinite or >= UINT32_MAX. */
  uint32_t card;

  /* string id or NULL */
  char *name;

  /*
   * syntactic depth:
   * for atomic types and type variables: depth = 0
   * or tuple type (tau_1 x ... x tau_n): depth = 1 + max depth(tau_i)
   * for function type (tau_1 ... tau_n -> tau_0): depth = 1 + max depth(tau_i)
   * for instance type F(tau_1, ... , tau_n): depth = 1 + max depth(tau_i)
   */
  uint32_t depth;
} type_desc_t;

/*
 * Type table: valid type indices are between 0 and nelems - 1
 *
 * - types = indexed_table_t of type_desc_t
 * - htbl = hash table for hash consing
 * - stbl = symbol table for named types
 *   stbl stores a mapping from strings to type ids.
 *   If name[i] is non-null, then it's in stbl (mapped to i).
 *   There may be other strings that refer to i (aliases).
 *
 * Hash tables allocated on demand:
 * - sup_tbl = maps pairs (tau_1, tau_2) to the smallest common
 *   supertype of tau_1 and tau_2 (or to NULL_TYPE if
 *   tau_1 and tau_2 are not compatible).
 * - inf_tbl = maps pairs (tau_1, tau_2) to the largest common
 *   subtype of tau_1 and tau_2 (or to NULL_TYPE if
 *   tau_1 and tau_2 are not compatible).
 * - max_tbl = map tau to its maximal super type
 *
 * Macro table: also allocated on demand
 */
typedef struct type_table_s {
  indexed_table_t types;

  int_htbl_t htbl;
  stbl_t stbl;
  int_hmap2_t *sup_tbl;
  int_hmap2_t *inf_tbl;
  int_hmap_t *max_tbl;

  type_mtbl_t *macro_tbl;
} type_table_t;



/*
 * Bitmask to access the flags
 */
#define TYPE_IS_FINITE_MASK  ((uint8_t) 0x01)
#define TYPE_IS_UNIT_MASK    ((uint8_t) 0x02)
#define CARD_IS_EXACT_MASK   ((uint8_t) 0x04)
#define TYPE_IS_MAXIMAL_MASK ((uint8_t) 0x08)
#define TYPE_IS_MINIMAL_MASK ((uint8_t) 0x10)
#define TYPE_IS_GROUND_MASK  ((uint8_t) 0x20)

#define TYPE_GC_MARK         ((uint8_t) 0x80)


// select the cardinality/finiteness bits
#define CARD_FLAGS_MASK     ((uint8_t) 0x07)

// select the max/min bits
#define MINMAX_FLAGS_MASK   ((uint8_t) 0x18)


/*
 * Abbreviations for valid flag combinations:
 * - UNIT_TYPE: ground, finite, card = 1, exact cardinality
 * - SMALL_TYPE: ground, finite, non-unit, exact cardinality
 * - LARGE_TYPE: ground, finite, non-unit, inexact card
 * - INFINITE_TYPE: ground, infinite, non-unit, inexact card
 *
 * All finite types are both minimal and maximal so we set bit 3 and 4
 * for them. For infinite types, the minimal and maximal bits must be
 * set independently.
 *
 * Flag for types that contain variables
 * - FREE_TYPE: all bits are 0
 */
#define UNIT_TYPE_FLAGS     ((uint8_t) 0x3F)
#define SMALL_TYPE_FLAGS    ((uint8_t) 0x3D)
#define LARGE_TYPE_FLAGS    ((uint8_t) 0x39)
#define INFINITE_TYPE_FLAGS ((uint8_t) 0x20)
#define FREE_TYPE_FLAGS     ((uint8_t) 0x00)



/*
 * TYPE MATCHER
 */

/*
 * Given a polymorphic function f of type [tau_1 ... tau_n -> sigma]
 * where tau_1 ... tau_n contain variables X, Y, Z we want to
 * compute the type of (f a_1 ... a_n) where a_1, ..., a_n have
 * fixed types.
 *
 * This means finding  a type substitution for X, Y, and Z
 * that satisfies a set of type constraints of the form
 *    sigma_1 subtype of tau_1[X, Y, Z]
 *     ...
 *    sigma_2 subtype of tau_n[X, Y, Z]
 *
 * We also need to handle constraints of the form sigma_k equals
 * tau_k[X, Y, Z]. There may be several solutions, we want the minimal
 * one (i.e., the most precise).
 *
 * To solve these constraints, we used a type_matcher structure:
 * - The int_hmap_t tc stores the set of constraints.
 *   For any type tau, it's enough to keep a single constraint on tau.
 *   We store it as a 32bit integer in tc[tau]:
 *     tc[tau] = -1: no constraints on tau
 *     tc[tau] = 2 * sigma + 1: equality constraint: tau = sigma
 *     tc[tau] = 2 * sigma + 0: subtype constraint:  tau must be a
 *                                                   supertype of sigma
 *   (i.e., the lower order bit of tc[tau] is used as a flag).
 *
 * Other components:
 * - types = relevant type table
 * - var = array of variables seen so far
 * - map = array of types
 * - nvars = number of variables = number of elements in map
 * - varsize = size of arrays var and map
 * Arrays var, map are intended to store the solution to the current set of
 * constraints: var[i] is a type variable, map[i] is what's map to var[i]
 * in the solution.
 *
 * NOTE: 2 * sigma + 0 and 2 * sigma + 1 fit in a signed 32bit integer
 * (because sigma < YICES_MAX_TYPE).
 */
typedef struct type_matcher_s {
  type_table_t *types;
  int_hmap_t tc;
  type_t *var;
  type_t *map;
  uint32_t nvars;
  uint32_t varsize;
} type_matcher_t;

// default/max sizes of arrays var and map
#define DEF_TYPE_MATCHER_SIZE 10
#define MAX_TYPE_MATCHER_SIZE (UINT32_MAX/sizeof(type_t))




/*
 * TYPE TABLE OPERATIONS
 */

/*
 * Initialization: n = initial size of the table.
 * htbl and stbl have default initial size (i.e., 64)
 */
extern void init_type_table(type_table_t *table, uint32_t n);


/*
 * Delete table and all attached data structures.
 */
extern void delete_type_table(type_table_t *table);

/*
 * Returns the number of types.
 */
static inline uint32_t ntypes(const type_table_t *table) {
  return indexed_table_nelems(&table->types);
}

/*
 * Returns the number of live types.
 */
static inline uint32_t live_types(const type_table_t *table) {
  return indexed_table_live_elems(&table->types);
}

/*
 * Reset: remove all types and macros, and empty the symbol_table
 */
extern void reset_type_table(type_table_t *table);

/* 
 * Return the ith type descriptor.
 */
static inline type_desc_t *type_desc(const type_table_t *table,
				     int32_t i) {
  return &((type_desc_t *) table->types.elems)[i];
}

static inline bool valid_type(type_table_t *tbl, type_t i) {
  return 0 <= i && i < ntypes(tbl);
}

static inline type_kind_t type_kind(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_desc(tbl, i)->kind;
}

/*
 * TYPE CONSTRUCTORS
 */

/*
 * Predefined types
 */
static inline type_t bool_type(type_table_t *table) {
  assert(type_kind(table, bool_id) == BOOL_TYPE);
  return bool_id;
}

static inline type_t int_type(type_table_t *table) {
  assert(type_kind(table, int_id) == INT_TYPE);
  return int_id;
}

static inline type_t real_type(type_table_t *table) {
  assert(type_kind(table, real_id) == REAL_TYPE);
  return real_id;
}

/*
 * Bitvector types
 * This requires 0 < size <= YICES_MAX_BVSIZE
 */
extern type_t bv_type(type_table_t *table, uint32_t size);

/*
 * Declare a new scalar of cardinality size
 * Require size > 0.
 */
extern type_t new_scalar_type(type_table_t *table, uint32_t size);

/*
 * Declare a new uninterpreted type
 */
extern type_t new_uninterpreted_type(type_table_t *table);

/*
 * Construct tuple type elem[0] ... elem[n-1].
 * - n must positive and no more than YICES_MAX_ARITY
 */
extern type_t tuple_type(type_table_t *table, uint32_t n, const type_t elem[]);

/*
 * Construct function type dom[0] ... dom[n-1] --> range
 * - n must be positive and no more than YICES_MAX_ARITY
 */
extern type_t function_type(type_table_t *table, type_t range, uint32_t n, const type_t dom[]);

/*
 * Construct instance type: (cid tau[0] ... tau[n-1])
 * - cid = constructor id
 * - n = constructor arity (must be positive and no more than YICES_MAX_ARITY)
 */
extern type_t instance_type(type_table_t *table, int32_t cid, uint32_t n, const type_t tau[]);

/*
 * Type variable of the given id
 */
extern type_t type_variable(type_table_t *table, uint32_t id);




/*
 * SUBSTITUTION
 */

/*
 * Apply a type substitution:
 *   v[0 ... n-1] = distinct type variables
 *   s[0 ... n-1] = types
 * the function replaces v[i] by s[i] in tau and returns
 * the result.
 */
extern type_t type_substitution(type_table_t *table, type_t tau, uint32_t n, const type_t v[], const type_t s[]);





/*
 * TYPE NAMES
 */

/*
 * IMPORTANT: We use reference counting on character strings as
 * implemented in refcount_strings.h
 *
 * - Parameter "name" in set_type_name must be constructed via the
 *   clone_string function.
 *   For the other functions (e.g., get_type_by_name and
 *   remove_type_name) "name" must be a '\0' terminated string.
 * - When name is added to the symbol table, its reference counter
 *   is increased by 1 or 2
 * - When remove_type_name is called, the reference counter is decremented
 * - When the table is deleted (via delete_type_table), the
 *   reference counters of all symbols present in table are also
 *   decremented.
 */

/*
 * Assign a name to type i. The first name assigned to i is considered the
 * default name (stored in name[i]). Otherwise, name is an alias and can
 * be used to refer to type i by calling get_type_by_name.
 *
 * If name already refers to another type, then the previous mapping
 * is hidden until remove_type_name is called.
 * This is done by assigning a list to each name (cf. symbol_tables).
 * The current mapping for name is the head of the list.
 */
extern void set_type_name(type_table_t *table, type_t i, char *name);


/*
 * Get type with the given name or NULL_TYPE if no such type exists.
 */
extern type_t get_type_by_name(type_table_t *table, const char *name);


/*
 * Remove a type name: removes the current mapping for name and
 * restore the previous mapping if any. This removes the first
 * element from the list of types attached to name.
 *
 * If name is not in the symbol table, the function does nothing.
 *
 * If name is the default type name for some type tau, then it will
 * still be kept as name[tau] for pretty printing.
 */
extern void remove_type_name(type_table_t *table, const char *name);


/*
 * Clear name: remove t's name if any.
 * - If t has name 'xxx' then 'xxx' is first removed from the symbol
 *   table (using remove_type_name) then name[t] is reset to NULL.
 *   The reference counter for 'xxx' is decremented twice.
 * - If t doesn't have a name, nothing is done.
 */
extern void clear_type_name(type_table_t *table, type_t t);



/*
 * MACRO CONSTRUCTORS
 */

/*
 * NOTES
 *
 * 1) macro names have the same scoping mechanism as
 *    term and type names. If a macro of a given name is
 *    added to the table, and name refers to an existing
 *    macro then the current mapping is hidden. It will be
 *    restored after a call to remove_type_macro_name.
 *
 * 2) the implementation uses character strings with reference
 *    counting (cf. refcount_strings.h). The parameter 'name'
 *    in add_type_macro and add_type_constructor must be
 *    the result of 'clone_string'.
 */

/*
 * Add a macro descriptor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 * - vars = array of n type variables (must be all distinct)
 * - body = type
 *
 * return the macro's id
 */
extern int32_t add_type_macro(type_table_t *table, char *name, uint32_t n, const type_t *vars, type_t body);


/*
 * Add an uninterpreted type constructor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 *
 * return the constructor's id
 */
extern int32_t add_type_constructor(type_table_t *table, char *name, uint32_t n);


/*
 * Get a macro id of the given name
 * - return -1 if there's no macro or constructor with this name
 */
extern int32_t get_type_macro_by_name(type_table_t *table, const char *name);


/*
 * Get the descriptor for the given id
 * - return NULL if id is not valid (including if it refers to a deleted macro)
 */
extern type_macro_t *type_macro(type_table_t *table, int32_t id);


/*
 * Remove the current mapping of 'name' to a macro id
 * - no change if 'name' does not refer to any macro
 * - otherwise, the current reference for 'name' is removed
 *   and the previous mapping is restored (if any).
 */
extern void remove_type_macro_name(type_table_t *table, const char *name);


/*
 * Remove macro of the given id
 * - id must be a valid macro index
 * - the macro name is deleted (from the symbol table)
 * - all instances of this macro are also deleted.
 */
extern void delete_type_macro(type_table_t *table, int32_t id);


/*
 * Macro instance: apply a macro to the given actual parameters
 * - id = macro id
 * - n = number of actuals
 * - actual = array of n types (actual parameters)
 * - each parameter must be a valid type
 * - n must be equal to the macro arity.
 *
 * This first check whether this instance already exists in table->hmap.
 * If so, the instance is returned.
 *
 * Otherwise:
 * - if the macro is a type constructor (i.e., body = NULL_TYPE)
 *   then a new type instance is constructed.
 * - if the macro is a normal macro (body != NULL_TYPE), then
 *   the instance is constructed by substituting the actuals
 *   for the macro variable.
 * In both cases, the instance is stored in table->hmap.
 */
extern type_t instantiate_type_macro(type_table_t *table, int32_t id, uint32_t n, const type_t *actual);

static inline type_macro_t *type_macro_unchecked(type_mtbl_t *table,
						     int32_t id) {
  return indexed_table_elem(type_mtbl_elem_t, table->macros, id)->data;
}

static inline uint32_t type_macro_nelems(type_mtbl_t *table) {
  return indexed_table_nelems(&table->macros);
}

/*
 * Check that id is good
 */
static inline bool good_type_macro(type_mtbl_t *table, int32_t id) {
  return 0 <= id && id < type_macro_nelems(table);
}

static inline type_macro_t *type_macro_def(type_mtbl_t *table, int32_t id) {
  assert(good_type_macro(table, id));
  return type_macro_unchecked(table, id);
}

/*
 * Arity and name of macro
 */
static inline char *type_macro_name(type_mtbl_t *table, int32_t id) {
  return type_macro_def(table, id)->name;
}

static inline uint32_t type_macro_arity(type_mtbl_t *table, int32_t id) {
  return type_macro_def(table, id)->arity;
}



/*
 * ACCESS TO TYPES AND TYPE DESCRIPTORS
 */

/*
 * Checks for arithmetic or boolean types.
 */
static inline bool is_boolean_type(type_t i) {
  return i == bool_id;
}

static inline bool is_integer_type(type_t i) {
  return i == int_id;
}

static inline bool is_real_type(type_t i) {
  return i == real_id;
}

static inline bool is_arithmetic_type(type_t i) {
  return i == int_id || i == real_id;
}


/*
 * Extract components from the table
 */

// check for deleted types
static inline bool good_type(type_table_t *tbl, type_t i) {
  return valid_type(tbl, i) && type_kind(tbl, i) != UNUSED_TYPE;
}

static inline bool bad_type(type_table_t *tbl, type_t i) {
  return ! good_type(tbl, i);
}


static inline uint8_t type_flags(type_table_t *tbl, type_t i) {
  assert(good_type(tbl, i));
  return type_desc(tbl, i)->flags;
}

// ground type: does not contain variables
static inline bool ground_type(type_table_t *tbl, type_t i) {
  assert(good_type(tbl, i));
  return type_flags(tbl, i) & TYPE_IS_GROUND_MASK;
}


// access card, flags, name, depth of non-deleted type
static inline uint32_t type_card(type_table_t *tbl, type_t i) {
  assert(good_type(tbl, i));
  return type_desc(tbl, i)->card;
}

static inline char *type_name(type_table_t *tbl, type_t i) {
  assert(good_type(tbl, i));
  return type_desc(tbl, i)->name;
}

static inline uint32_t type_depth(type_table_t *tbl, type_t i) {
  assert(good_type(tbl, i));
  return type_desc(tbl, i)->depth;
}

// check whether i is atomic (i.e., not a tuple or function type)
static inline bool is_atomic_type(type_table_t *tbl, type_t i) {
  assert(ground_type(tbl, i));
  return type_kind(tbl, i) <= UNINTERPRETED_TYPE;
}

// bit vector types
static inline bool is_bv_type(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == BITVECTOR_TYPE;
}

static inline uint32_t bv_type_size(type_table_t *tbl, type_t i) {
  assert(is_bv_type(tbl, i));
  return type_desc(tbl, i)->integer;
}

// uninterpreted types
static inline bool is_uninterpreted_type(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == UNINTERPRETED_TYPE;
}

// scalar/enumeration types
static inline bool is_scalar_type(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == SCALAR_TYPE;
}

static inline uint32_t scalar_type_cardinal(type_table_t *tbl, type_t i) {
  assert(is_scalar_type(tbl, i));
  return type_desc(tbl, i)->integer;
}


// type variables
static inline bool is_type_variable(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == VARIABLE_TYPE;
}

static inline uint32_t type_variable_id(type_table_t *tbl, type_t i) {
  assert(is_type_variable(tbl, i));
  return type_desc(tbl, i)->integer;
}


// tuple types
static inline bool is_tuple_type(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == TUPLE_TYPE;
}

static inline tuple_type_t *tuple_type_desc(type_table_t *tbl, type_t i) {
  assert(is_tuple_type(tbl, i));
  return (tuple_type_t *) type_desc(tbl, i)->ptr;
}

static inline uint32_t tuple_type_arity(type_table_t *tbl, type_t i) {
  assert(is_tuple_type(tbl, i));
  return ((tuple_type_t *) type_desc(tbl, i)->ptr)->nelem;
}

static inline type_t tuple_type_component(type_table_t *tbl, type_t i, int32_t j) {
  assert(0 <= j && j <  tuple_type_arity(tbl, i));
  return ((tuple_type_t *) type_desc(tbl, i)->ptr)->elem[j];
}


// function types
static inline bool is_function_type(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == FUNCTION_TYPE;
}

static inline function_type_t *function_type_desc(type_table_t *tbl, type_t i) {
  assert(is_function_type(tbl, i));
  return (function_type_t *) type_desc(tbl, i)->ptr;
}

static inline type_t function_type_range(type_table_t *tbl, type_t i) {
  assert(is_function_type(tbl, i));
  return ((function_type_t *) type_desc(tbl, i)->ptr)->range;
}

static inline uint32_t function_type_arity(type_table_t *tbl, type_t i) {
  assert(is_function_type(tbl, i));
  return ((function_type_t *) type_desc(tbl, i)->ptr)->ndom;
}

static inline type_t function_type_domain(type_table_t *tbl, type_t i, int32_t j) {
  assert(0 <= j && j < function_type_arity(tbl, i));
  return ((function_type_t *) type_desc(tbl, i)->ptr)->domain[j];
}


// instance
static inline bool is_instance_type(type_table_t *tbl, type_t i) {
  return type_kind(tbl, i) == INSTANCE_TYPE;
}

static inline instance_type_t *instance_type_desc(type_table_t *tbl, type_t i) {
  assert(is_instance_type(tbl, i));
  return (instance_type_t *) type_desc(tbl, i)->ptr;
}

static inline int32_t instance_type_cid(type_table_t *tbl, type_t i) {
  return instance_type_desc(tbl, i)->cid;
}

static inline uint32_t instance_type_arity(type_table_t *tbl, type_t i) {
  return instance_type_desc(tbl, i)->arity;
}

static inline type_t instance_type_param(type_table_t *tbl, type_t i, int32_t j) {
  assert(0 <= j && j < instance_type_arity(tbl, i));
  return instance_type_desc(tbl, i)->param[j];
}



/*
 * FINITENESS AND CARDINALITY
 */

/*
 * type_card(tbl, t) is a lower bound on the actual size of type t.
 * It's equal to the real size of t if that size fits in a 32bit
 * unsigned integer. It's equal to UINT32_MAX otherwise (largest 32bit
 * unsigned integer).
 *
 * Three bits encode information about a type t's cardinality:
 *    FINITE_FLAG --> 1 if t is finite, 0 otherwise
 *    UNIT_FLAG   --> 1 if t has cardinality 1, 0 otherwise
 *    EXACT_CARD  --> 1 if type_card(tbl, t) is exact, 0 otherwise
 *
 * There are four valid combinations for these flags:
 *    0b111 --> t has cardinality 1
 *    0b101 --> t is finite, 2 <= size t <= UINT32_MAX (exact card)
 *    0b001 --> t is finite, UINT32_MAX < size t
 *    0b000 --> t is infinite
 */
static inline bool is_finite_type(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_flags(tbl, i) & TYPE_IS_FINITE_MASK;
}

static inline bool is_unit_type(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_flags(tbl, i) & TYPE_IS_UNIT_MASK;
}

static inline bool type_card_is_exact(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_flags(tbl, i) & CARD_IS_EXACT_MASK;
}



/*
 * Approximate cardinality of tau[0] x ... x tau[n-1]
 * - returns the same value as card_of(tuple_type(tau[0] ... tau[n-1])) but does not
 *   construct the tuple type.
 */
extern uint32_t card_of_type_product(type_table_t *table, uint32_t n, const type_t *tau);


/*
 * Approximate cardinality of the domain and range of a function type tau
 * - both function return a 32bit unsigned number (which is a lower bound
 *   on the actual domain or range size).
 * - the result is exact if it's less than UINT32_MAX.
 */
extern uint32_t card_of_domain_type(type_table_t *table, type_t tau);
extern uint32_t card_of_range_type(type_table_t *table, type_t tau);


/*
 * Check whether the domain and range of a function type tau are finite
 */
extern bool type_has_finite_domain(type_table_t *table, type_t tau);
extern bool type_has_finite_range(type_table_t *table, type_t tau);




/*
 * SUBTYPING AND COMPATIBILITY
 */

/*
 * The subtype relation is defined inductively by the following rules.
 * 1) int <= real
 * 2) tau <= tau
 * 3) if tau_1 <= sigma_1 ... tau_n <= sigma_n then
 *    [tau_1 ... tau_n] <= [sigma_1 ... sigma_n]
 * 4) if sigma_1 <= sigma_2 then
 *    [tau_1 ... tau_n -> sigma_1] <= [tau_1 ... tau_n -> sigma_2]
 *
 * Two types are compatible if they have a common supertype.
 *
 * Consequences:
 * 1) if tau1 and tau2 are compatible, then they have a smallest
 *    common supertype sup(tau1, tau2).
 * 2) tau1 and tau2 are compatible iff they have a common subtype.
 * 3) if tau1 and tau2 are compatible, then they have a largest
 *    common subtype inf(tau1, tau2).
 */

/*
 * Check whether type i is maximal (i.e., no strict supertype)
 */
static inline bool is_maxtype(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_flags(tbl, i) & TYPE_IS_MAXIMAL_MASK;
}

/*
 * Check whether tau is minimal (i.e., no strict subtype)
 */
static inline bool is_mintype(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_flags(tbl, i) & TYPE_IS_MINIMAL_MASK;
}


/*
 * Compute the sup of tau1 and tau2
 * - return the smallest type tau such that tau1 <= tau and
 *   tau2 <= tau if there is one
 * - return NULL_TYPE otherwise (i.e., if tau1 and tau2 are not compatible)
 */
extern type_t super_type(type_table_t *table, type_t tau1, type_t tau2);


/*
 * Compute the inf of tau1 and tau2
 * - return the largest type tau such that tau <= tau1 and tau <= tau2
 *   if there is one
 * - return NULL_TYPE otherwise (i.e., if tau1 and tau2 are not compatible)
 */
extern type_t inf_type(type_table_t *table, type_t tau1, type_t tau2);


/*
 * Build the largest type that's a supertype of tau
 */
extern type_t max_super_type(type_table_t *table, type_t tau);


/*
 * Check whether tau1 is a subtype if tau2.
 *
 * Side effect: this is implemented using super_type so this may create
 * new types in the table.
 */
extern bool is_subtype(type_table_t *table, type_t tau1, type_t tau2);


/*
 * Check whether tau1 and tau2 are compatible.
 *
 * Side effect: use the super_type function. So this may create new
 * types in the table.
 */
extern bool compatible_types(type_table_t *table, type_t tau1, type_t tau2);



/*
 *  MATCHING
 */

/*
 * Initialize type matcher
 * - types = relevant type table
 */
extern void init_type_matcher(type_matcher_t *matcher, type_table_t *types);


/*
 * Reset to the empty set of constraints
 * - also clears the internal substitution if any
 */
extern void reset_type_matcher(type_matcher_t *matcher);


/*
 * Free memory
 */
extern void delete_type_matcher(type_matcher_t *matcher);


/*
 * Add a type constraint:
 * - both tau and sigma must be valid types defined in matcher->types
 *   (and tau should contain type variables)
 * - if eq is true the constraint is "tau = sigma"
 *   otherwise it's "tau is a supertype of sigma"
 * - return false if the set of constraints is inconsistent
 * - return true otherwise and update the solution
 */
extern bool type_matcher_add_constraint(type_matcher_t *matcher, type_t tau, type_t sigma, bool eq);


/*
 * If all calls to type_matcher_add_constraint succeed, call
 * this function to construct the solution.
 * - the solution is stored in arrays matcher->var and matcher->map
 * - for all i from 0 to matcher->nvars - 1,
 *   matcher->var[i] is a type variable X
 *   matcher->map[i] is the mapping of X in the substitution
 *
 * Important: this function should not be called after a call to
 * type_matcher_add_constraints that returns false.
 */
extern void type_matcher_build_subst(type_matcher_t *matcher);


/*
 * Apply the substitution stored in matcher to type tau
 * - call type_matcher_build_subst first
 */
extern type_t apply_type_matching(type_matcher_t *matcher, type_t tau);




/*
 * GARBAGE COLLECTION
 */

/*
 * We use a simple mark-and-sweep mechanism:
 * - Nothing gets deleted until an explicit call to type_table_gc.
 * - type_table_gc marks every type reachable from a set of
 *   root types, then deletes every type that's not marked.
 * The root types include:
 * - the three predefined types: bool, int, and real
 * - all types that are explicitly marked as roots (using call to set_gc_mark).
 * - if flag keep_named is true, every type that's present in the symbol table
 * At the end of type_table_gc, all marks are cleared.
 */

/*
 * Mark i as a root type (i.e., make sure it's not deleted by the next
 * call to type_table_gc).
 * - i must be a good type (not already deleted)
 */
static inline void type_table_set_gc_mark(type_table_t *tbl, type_t i) {
  assert(good_type(tbl, i));
  type_desc(tbl, i)->flags |= TYPE_GC_MARK;
}

/*
 * Clear mark on type i
 */
static inline void type_table_clr_gc_mark(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  type_desc(tbl, i)->flags &= ~TYPE_GC_MARK;
}

/*
 * Test whether i is marked
 */
static inline bool type_is_marked(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return type_flags(tbl, i) & TYPE_GC_MARK;
}


/*
 * Call the garbage collector:
 * - delete every type not reachable from a root
 * - if keep_named is true, all named types (reachable from the symbol table)
 *   are preserved. Otherwise, all references to dead types are removed
 *   from the symbol table.
 * - then clear all marks
 */
extern void type_table_gc(type_table_t *tbl, bool keep_named);



#endif /* __TYPES_H */
