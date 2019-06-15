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

#include "parser_utils/term_stack2.h"
#include "terms/free_var_collector.h"
#include "terms/term_manager.h"

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
