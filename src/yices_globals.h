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
#include "yices_locks.h"
#include "yices_lexer.h"
#include "yices_parser.h"
#include "yices_pp.h"

typedef struct yices_globals_s {
  yices_lock_t lock;                /* a lock protecting the globals                         */

  type_table_t *types;              /* type table                                            */
  term_table_t *terms;              /* term table                                            */
  term_manager_t *manager;          /* full term manager (includes terms)                    */
  pprod_table_t *pprods;            /* pprod table                                           */

  /* the parser bundle: parser, lexer, term stack: all are allocated on demand               */

  parser_t *parser;
  lexer_t *lexer;
  tstack_t *tstack;

} yices_globals_t;

extern yices_globals_t __yices_globals;


#endif /* __YICES_GLOBALS_H */
