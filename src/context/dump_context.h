/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Print a context (for debugging mostly)
 * Moved the code here to clean-up yices_reval.c
 */

#ifndef __DUMP_CONTEXT_H
#define __DUMP_CONTEXT_H

#include <stdio.h>

#include "context/context_types.h"

/*
 * Print ctx into file f
 * - the amount of details depend on the compilation mode
 * - in MODE=debug, print a lot of stuff
 */
extern void dump_context(FILE *f, context_t *ctx);

#endif /* __DUMP_CONTEXT_H */

