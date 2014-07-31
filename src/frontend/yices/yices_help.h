/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Help command for Yices
 */

#ifndef __YICES_HELP_H
#define __YICES_HELP_H

#include <stdio.h>

/*
 * Print help on the given topic (on file f)
 * - f must be open and writable
 * - if topic is NULL, a generic help is printed
 */
extern void show_help(FILE *f, const char *topic);

#endif /* __YICES_HELP_H */
