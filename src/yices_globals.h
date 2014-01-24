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

#include "term_manager.h"
#include "term_stack2.h"
#include "free_var_collector.h"

typedef struct yices_globals_s {
  type_table_t *types;     // type table
  term_table_t *terms;     // term table
  term_manager_t *manager; // full term manager (includes terms)
  tstack_t *tstack;        // term stack (or NULL)
  error_report_t *error;   // data structure for error reporting
  fvar_collector_t *fvars; // to collect free variables of terms
} yices_globals_t;

extern yices_globals_t __yices_globals;

#endif /* __YICES_GLOBALS_H */
