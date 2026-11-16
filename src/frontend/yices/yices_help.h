/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
