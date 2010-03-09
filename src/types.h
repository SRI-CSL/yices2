/*
 * Type descriptors and type table
 * Support for hash-consing and attaching names to types.
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
 * March 08, 2009. Updates to the data structures:
 * - store the pseudo cardinality in the type table (rather than 
 *   compute it on demand) 
 * - added flags for each type tau to indicate 
 *   - whether tau is finite 
 *   - whether tau is a unit type (finite type with cardinality 1)
 *   - whether pseudo_card[tau] is exact. (If pseudo_card[tau] 
 *     is exact, then it's the cardinality of tau. Otherwise,
 *     pseudo_card[tau] is set to UINT32_MAX.)
 * - added hash_table to use as caches
 */

#ifndef __TYPES_H
#define __TYPES_H 1

#include <stdint.h>
#include <assert.h>
#include <stdbool.h>

#include "int_queues.h"
#include "int_hash_tables.h"
#include "symbol_tables.h"
#include "bitvectors.h"


#include "yices_types.h"
#include "yices_limits.h"


/*
 * Different kinds of types:
 * - primitive types are BOOL, INT, REAL, 
 *   BITVECTOR[n] for any n (0 < n <= MAX_BVSIZE)
 * - declared types can be either scalar or uninterpreted
 * - constructed types: tuple types and function types
 */
typedef enum {
  UNUSED_TYPE,    // for deleted types 
  BOOL_TYPE,
  INT_TYPE,
  REAL_TYPE,
  BITVECTOR_TYPE,
  SCALAR_TYPE,
  UNINTERPRETED_TYPE,
  TUPLE_TYPE,
  FUNCTION_TYPE,
} type_kind_t;


/*
 * Ids of the predefined types
 */
enum {
  bool_id = 0,
  int_id = 1,
  real_id = 2
};


/*
 * Descriptors of tuple and function types.
 */
typedef struct {
  uint32_t nelem; // number of components (must be positive)
  type_t elem[0]; // elem[0] .. elem[nelem-1]: component types
} tuple_type_t;

typedef struct {
  type_t range;     // range type
  uint32_t ndom;    // number of domains (must be positive)
  type_t domain[0]; // domain[0] .. domain[ndom - 1]: domain types
} function_type_t;

/*
 * Descriptor: either a pointer to a descriptor or an integer The size
 * of a bitvector type or scalar type i is stored in desc[i].integer
 */
typedef union {
  uint32_t integer;
  void *ptr;
} type_desc_t;


/*
 * Type table: valid type indices are between 0 and nelems - 1
 *
 * For each i betwen 0 and nelems - 1,
 * - kind[i] = type kind
 * - desc[i] = type descriptor
 * - card[i] = cardinality of type i or
 *             UINT32_MAX if i is infinite or has card > UINT32_MAX
 * - name[i] = string id or NULL.
 * - flags[i] = 8bit flags:
 *    bit 0 of flag[i] is 1 if i is finite
 *    bit 1 of flag[i] is 1 if i is a unit tupe
 *    bit 2 of flag[i] is 1 if card[i] is exact
 *    bit 3 of flag[i] is used as a mark during garbage collection
 * 
 * Other components:
 * - size = size of all arrays above
 * - nelems = number of elements in the array
 * - free_idx = start of the free list (-1 means empty free list).
 *   The free list contains the deleted types: for each i in the list,
 *     kind[i] = UNUSED_TYPE
 *     desc[i].integer = index of i's successor in the list (or -1).
 * - htbl = hash table for hash consing
 * - stbl = symbol table for named types
 *   stbl stores a mapping from strings to type ids.
 *   If name[i] is non-null, then it's in stbl (mapped to i).
 *   There may be other strings that refer to i (aliases).
 * Garbage collection:
 * - gc_mark: bit vector used in garbage collection
 * - gc_mark_queue: used in garbage collection
 * - gc_notifier: function called before garbage collection,
 *   used to mark types that need to be preserved.
 */
typedef struct type_table_s type_table_t;

typedef void (*type_gc_notifier_t)(type_table_t *tbl);

struct type_table_s {
  uint8_t *kind;
  type_desc_t *desc;
  uint32_t *card;
  uint8_t *flags;
  char **name;

  uint32_t size;
  uint32_t nelems;
  int32_t free_idx;

  int_htbl_t htbl;
  stbl_t stbl;

  byte_t *gc_mark;
  int_queue_t *gc_mark_queue;
  type_gc_notifier_t gc_notifier;
};





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
 * TYPE CONSTRUCTORS
 */

/*
 * Predefined types
 */
static inline type_t bool_type(type_table_t *table) {
  assert(table->nelems > bool_id && table->kind[bool_id] == BOOL_TYPE);
  return bool_id;
}

static inline type_t int_type(type_table_t *table) {
  assert(table->nelems > int_id && table->kind[int_id] == INT_TYPE);
  return int_id;
}

static inline type_t real_type(type_table_t *table) {
  assert(table->nelems > real_id && table->kind[real_id] == REAL_TYPE);
  return real_id;
}

/*
 * Bitvector types, size must be positive
 */
extern type_t bv_type(type_table_t *table, int32_t size);

/*
 * Declare a new scalar of cardinality size
 * - size must be positive.
 */
extern type_t new_scalar_type(type_table_t *table, int32_t size);

/*
 * Declare a new unintrepreted type
 */
extern type_t new_uninterpreted_type(type_table_t *table);

/*
 * Construct tuple type elem[0] ... elem[n-1].
 * - n must positive and less than MAX_TYPE_ARITY
 */
extern type_t tuple_type(type_table_t *table, int32_t n, type_t elem[]);

/*
 * Construct function type dom[0] ... dom[n-1] --> range
 * - n must be positive and less than MAX_TYPE_ARITY
 */
extern type_t function_type(type_table_t *table, type_t range, int32_t n, type_t dom[]);



/*
 * TYPE NAMES
 */

/*
 * IMPORTANT: we use reference counting on character strings as
 * implemented in memalloc.h.
 *
 * - Parameter "name" in set_type_name must be constructed via the clone_string function.
 *   That's not necessary for get_type_by_name or remove_type_name.
 * - When name is added to the symbol table, its reference counter is increased by 1 or 2
 * - When remove_type_name is called, the reference counter is decremented
 * - When the table is deleted (via delete_type_table), the reference counters
 *   of all symbols present in table are also decremented.
 */

/*
 * Assign a name to type i. The first name assigned to i is considered the 
 * default name (stored in name[i]). Otherwise, name is an alias and can
 * be used to refer to type i by calling get_type_by_name.
 *
 * If name already refers to another type, then the previous mapping is hidden,
 * until remove_type_name is called.
 */
extern void set_type_name(type_table_t *table, type_t i, char *name);

/*
 * Get type with the given name or NULL_TYPE if no such type exists.
 */
extern type_t get_type_by_name(type_table_t *table, char *name);

/*
 * Remove a type name: subsequent calls to get_type_by_name 
 * with the same string will return NULL_TYPE.
 * If name is the default type name, then it will still be kept
 * for pretty printing.
 */
extern void remove_type_name(type_table_t *table, char *name);



/*
 * COMPARISON BETWEEN TYPES
 */

/*
 * Check whether tau1 is a subtype if tau2, using the rules
 * 1) int <= real
 * 2) tau <= tau
 * 3) if tau_1 <= sigma_1 ... tau_n <= sigma_n then
 *   (tuple-type tau_1 ... tau_n) <= (tuple-typle sigma_1 ... sigma_n)
 * 4) if sigma_1 <= sigma_2 then 
 *   (tau_1 ... tau_n --> sigma_1) <= (tau_1 ... tau_n -> sigma_2)
 */
extern bool is_subtype(type_table_t *table, type_t tau1, type_t tau2);


/*
 * Check whether tau is maximal (i.e., the only supertype of tau is tau itself)
 */
extern bool is_maxtype(type_table_t *table, type_t tau);


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
 *    if there is one
 * - return NULL_TYPE otherwise (i.e., if tau1 and tau2 are not compatible)
 */
extern type_t inf_type(type_table_t *table, type_t tau1, type_t tau2);


/*
 * Check whether tau1 and tau2 are compatible:
 * - they are compatible if they have a common supertype
 * - this is used to typecheck equalities:
 *   if x has type tau1 and y has type tau2 then (eq x y) is well typed
 *   if tau1 and tau2 are compatible.
 * 
 * NOTE: this used to be defined as
 * static inline bool compatible_types(type_table_t *table, type_t tau1, type_t tau2) {
 *   return super_type(table, tau1, tau2) != NULL_TYPE;
 * }
 * But this definition has side effects. It construct the supertype it's not already 
 * in the table (which may recursively create more types). This new version has 
 * no side effects.
 */
extern bool compatible_types(type_table_t *table, type_t tau1, type_t tau2);




/*
 * CHECK FINITENESS
 */

/*
 * Check whether type tau is finite.
 */
extern bool finite_type(type_table_t *table, type_t tau);

/*
 * Check whether type tau is a singleton
 */
extern bool unit_type(type_table_t *table, type_t tau);

/*
 * Check whether a function type has a finite domain
 * - tau must be a function type.
 */
extern bool type_has_finite_domain(type_table_t *table, type_t tau);

/*
 * Check whether a function type has unit range
 */
static inline bool type_has_unit_range(type_table_t *table, type_t tau) {
  assert(0 <= tau && tau < table->nelems && table->kind[tau] == FUNCTION_TYPE);
  return unit_type(table, ((function_type_t *) table->desc[tau].ptr)->range);
}


/*
 * Approximate cardinality of tau
 * - if tau is infinite or has cardinality >= 2^32 then the function
 *   returns UINT32_MAX (i.e., 2^32 - 1)
 */
extern uint32_t card_of_type(type_table_t *table, type_t tau);


/*
 * Approximate cardinality of tau[0] x ... x tau[n-1]
 * - return the same as card_of(tuple_type(tau[0] ... tau[n-1])) but does not 
 *   construct the tuple type
 */
extern uint32_t card_of_type_product(type_table_t *table, uint32_t n, type_t *tau);



/*
 * Approximate cardinality of the domain and range of a function type tau
 */
extern uint32_t card_of_domain_type(type_table_t *table, type_t tau);
extern uint32_t card_of_range_type(type_table_t *table, type_t tau);



/*
 * GARBAGE COLLECTION
 */

/*
 * Set gc_notifier
 */
static inline void set_type_gc_notifier(type_table_t *table, type_gc_notifier_t fun) {
  table->gc_notifier = fun;
}

/*
 * Mark type t to prevent its deletion. Must be called only from within a gc_notifier. 
 */
extern void gc_mark_type(type_table_t *table, type_t t);

/*
 * Trigger garbage collection.
 */
extern void type_table_garbage_collection(type_table_t *table);

/*
 * Root types are the built-in types + the types accessible by name
 * from the symbol table + the types explicitly marked using set_root_type_flag.
 * Any type reachable from the roots is alive. Every dead type is deleted
 * by the garbage collector.
 */

/*
 * Set/clear the root flag
 */
extern void set_root_type_flag(type_table_t *table, type_t i);
extern void clr_root_type_flag(type_table_t *table, type_t i);



/*
 * ACCESS TO TYPES AND TYPE DESCRIPTORS
 */


/*
 * Extract components from the table
 */
static inline bool valid_type(type_table_t *tbl, type_t i) {
  return 0 <= i && i < tbl->nelems;
}

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
 * Get fields
 */
static inline type_kind_t type_kind(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return tbl->kind[i];
}

static inline bool good_type(type_table_t *tbl, type_t i) {
  return valid_type(tbl, i) && (tbl->kind[i] != UNUSED_TYPE);
}

static inline bool bad_type(type_table_t *tbl, type_t i) {
  return ! good_type(tbl, i);
}

static inline char *type_name(type_table_t *tbl, type_t i) {
  assert(valid_type(tbl, i));
  return tbl->name[i];
}

static inline int32_t bv_type_size(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == BITVECTOR_TYPE);
  return tbl->desc[i].integer;
}

static inline int32_t scalar_type_cardinal(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == SCALAR_TYPE);
  return tbl->desc[i].integer;  
}

static inline tuple_type_t *tuple_type_desc(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == TUPLE_TYPE);
  return (tuple_type_t *) tbl->desc[i].ptr;
}

static inline int32_t tuple_type_ncomponents(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == TUPLE_TYPE);
  return ((tuple_type_t *) tbl->desc[i].ptr)->nelem;
}

static inline type_t tuple_type_component(type_table_t *tbl, type_t i, int32_t j) {
  assert(type_kind(tbl, i) == TUPLE_TYPE);
  assert(0 <= j && j <  ((tuple_type_t *) tbl->desc[i].ptr)->nelem);
  return ((tuple_type_t *) tbl->desc[i].ptr)->elem[j];
}

static inline function_type_t *function_type_desc(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == FUNCTION_TYPE);
  return (function_type_t *) tbl->desc[i].ptr;
}

static inline type_t function_type_range(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == FUNCTION_TYPE);
  return ((function_type_t *) tbl->desc[i].ptr)->range;
}

static inline int32_t function_type_ndomains(type_table_t *tbl, type_t i) {
  assert(type_kind(tbl, i) == FUNCTION_TYPE);
  return ((function_type_t *) tbl->desc[i].ptr)->ndom;
}

static inline type_t function_type_domain(type_table_t *tbl, type_t i, int32_t j) {
  assert(type_kind(tbl, i) == FUNCTION_TYPE);
  assert(0 <= j && j < ((function_type_t *) tbl->desc[i].ptr)->ndom);
  return ((function_type_t *) tbl->desc[i].ptr)->domain[j];
}

#endif /* __TYPES_H */
