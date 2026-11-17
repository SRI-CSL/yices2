/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * GLOBAL VARIABLES
 */

/*
 * Several global tables and data structures are maintained by
 * yices_api.c. If other modules need to access these internal
 * data structures, they can use the following table of pointers.
 *
 * The table is initialized after a call to yices_init();
 */

#ifndef __YICES_GLOBALS_H
#define __YICES_GLOBALS_H

#include "mt/yices_locks.h"
#include "frontend/yices/yices_parser.h"
#include "parser_utils/term_stack2.h"
#include "terms/free_var_collector.h"
#include "terms/term_manager.h"

typedef struct yices_globals_s {
#ifdef THREAD_SAFE
  yices_lock_t lock;       // a lock protecting the globals
#endif
  type_table_t *types;     // type table
  term_table_t *terms;     // term table
  term_manager_t *manager; // full term manager (includes terms)
  pprod_table_t *pprods;   // pprod table

  // parser, lexer, term stack: all are allocated on demand
  parser_t *parser;        // parser (or NULL)
  lexer_t *lexer;          // lexer (or NULL)
  tstack_t *tstack;        // term stack (or NULL)

  fvar_collector_t *fvars; // to collect free variables of terms

} yices_globals_t;

extern yices_globals_t __yices_globals;

#endif /* __YICES_GLOBALS_H */
