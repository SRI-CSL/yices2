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
