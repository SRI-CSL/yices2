/*
 * TYPE MACROS
 */

/*
 * This is intended to support SMT LIB2 functions 
 *     (declare-sort <name> <arity>)
 * and (define-sort <name> (<list-of-names>) <sort>)
 * when the arity is non-zero or the list-of-names is non-empty.
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
 *  where macro-id refers to a macro or arity n.
 */

#ifndef __TYPE_MACROS_H
#define __TYPE_MACROS_H

#include <stdint.h>

#include "symbol_tables.h"
#include "tuple_hmap.h"
#include "types.h"


/*
 * Macro descriptor
 */
typedef type_macro_s {
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
 * Table of macros
 * - macros are identified by an index 
 * - the table maps the index to the macro descriptor
 * - it also includes a symbol table that maps macro name
 *   to its id, and a hash table that stores macro instances.
 */
typedef struct type_mtbl_s {
  type_table_t *types;  // pointer to the type table
  type_macro_t **data;  // descriptors
  uint32_t size;        // size of the data array
  uint32_t nelems;      // number of descriptor/macros stored
  stbl_t stbl;          // symbol table
  tuple_hmap_t cache;   // existing macro instances
} type_mtbl_t;



/*
 * Default and maximal size
 */
#define TYPE_MACRO_DEF_SIZE   20
#define TYPE_MACRO_MAX_SIZE   (UINT32_MAX/sizeof(type_macro_t*))



/*
 * OPERATIONS
 */

/*
 * Initialize the macro table
 * - n = initial size
 * - ttbl = type table
 * - if n is zero, nothing is allocated yet.
 *   an array data of default size will be allocated
 *   on the first addition.
 */
extern void init_type_mtbl(type_mtbl_t *table, uint32_t n, type_table_t *ttbl);


/*
 * Delete the table and its content
 */
extern void delete_type_mtbl(type_mtbl_t *table);


/*
 * Empty the table: delete all macros and macro instances
 */
extern void reset_type_mtbl(type_mtbl_t *table);



/*
 * NOTES
 *
 * 1) macro names have the same scoping mechanism as 
 *    term and type names. If a macro of a given name is 
 *    added to the table, and name used to refer to a previous
 *    macro then the previous mapping is hidden. It will be
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
 */
extern void add_type_macro(type_mtbl_t *table, char *name, 
			   uint32_t n, type_t *vars, type_t body);


/*
 * Add an uninterpreted type constructor:
 * - name = macro name
 * - n = arity. It must be no more than TYPE_MACRO_MAX_ARITY
 */
extern void add_type_constructor(type_mtbl_t *table, char *name, uint32_t n);



/*
 * Get a macro id of the given name
 * - return -1 if there's no macro with this name
 */
extern int32_t get_type_macro_by_name(type_mtbl_t *table, const char *name);



/*
 * Remove the current mapping of 'name' to a macro id
 * - no change if 'name' does not refer to any macro
 * - otherwise, the current reference for 'name' is removed
 *   and the previous mapping is restored (if any).
 */
extern void remove_type_macro_name(type_mtbl_t *table, const char *name);


/*
 * Remove macro of the given id
 * - id must be a valid macro index
 * - the macro name is deleted (from the symbol table)
 * - all instances of this macro are also deleted.
 */
extern void delete_type_macro(type_mtbl_t *table, int32_t id);


/*
 * Macro instance: apply a macro to the given actual parameters
 * - id = macro id
 * - n = number of actuals
 * - actual = array of n types (actual parameters)
 * - each parameter must be a valid type 
 * - n must be equal to the macro arity.
 *
 * This first check, if this instance already exists in table->hmap.
 * If so, the instance is returned.
 *
 * Otherwise;
 * - if the macro is a type constructor (i.e., body = NULL_TYPE) 
 *   then a new uninterpreted type is returned.
 * - if the macro is a normal macro (body != NULL_TYPE), then
 *   the instance is constructed by subsituting the actuals
 *   for the macro variable.
 * In both case, the instance is stored in table->hmap
 */
extern type_t instantiate_type_macro(type_mtbl_t *table, int32_t id,
				     uint32_t n, type_t *actual);


#endif  /* __TYPE_MACROS_H */
