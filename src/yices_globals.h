/*
 * Global variables.
 *
 * Several global tables and data structures are maintained by 
 * module term_api.c. If other modules need to access these internal
 * data structures, they can use the following table of pointers.
 *
 * The table is initialized after a call to yices_init();
 */

#ifndef __YICES_GLOBALS_H
#define __YICES_GLOBALS_H

#include "terms.h"
#include "int_hash_map.h"

typedef struct yices_globals_s {
  type_table_t *types;  // type table
  term_table_t *terms;  // term table
  int_hmap_t *unit_map; // map singleton types to their unique term 

  // arithmetic
  arithvar_manager_t *arith_manager;
  object_store_t *arith_store;

  // bitvectors
  bv_var_manager_t *bv_manager;
  object_store_t *bv_store;
  node_table_t *nodes;

} yices_globals_t;

// the table
extern yices_globals_t __yices_globals;

#endif /* __YICES_GLOBALS_H */
