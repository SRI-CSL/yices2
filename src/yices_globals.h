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
#include "bit_expr.h"
#include "term_stack.h"

typedef struct yices_globals_s {
  type_table_t *types;    // type table
  term_table_t *terms;    // term table
  pprod_table_t *pprods;  // power products
  node_table_t *nodes;    // bit expressions

  object_store_t *arith_store;      // mlist used by arith_buffers
  object_store_t *bvarith_store;    // bvmlist used by bvarith_buffers
  object_store_t *bvarith64_store;  // bvmlist64 used by bvarith64_buffers

  tstack_t *tstack;       // term stack (or NULL)
  error_report_t *error;  // data structure for error reporting  
} yices_globals_t;

extern yices_globals_t __yices_globals;

#endif /* __YICES_GLOBALS_H */
