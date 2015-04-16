/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRINT STATISTICS ABOUT A CONTEXT
 */

/*
 * These functions used to be declared in yices_extensions.h
 * and implemented in yices_api.c. Moved them here to
 * keep yices_api cleaner.
 */

#ifndef __CONTEXT_STATISTICS_H
#define __CONTEXT_STATISTICS_H

#include <stdio.h>

#include "context/context_types.h"

extern void yices_print_presearch_stats(FILE *f, context_t *ctx);
extern void yices_show_statistics(FILE *f, context_t *ctx);
extern void yices_dump_context(FILE *f, context_t *ctx);



#endif /* __CONTEXT_STATISTICS_H */
