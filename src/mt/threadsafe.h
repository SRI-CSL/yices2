/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

#ifndef __THREADSAFE_H
#define __THREADSAFE_H

#include <stdio.h>
#include <stdint.h>


#include "terms/types.h"
#include "terms/terms.h"

/*
 * Print the type table
 */
extern void show_types_mt(FILE* output);

/*
 * Print the term table
 */
extern void show_terms_mt(FILE* output);


/* used in the _mt tests */
extern bool has_type_mt(type_t tau, term_t t);

/* used in the _mt tests */
extern void print_term_mt(FILE* output, term_t t);

/* used in the _mt tests */
extern void print_type_mt(FILE* output, type_t t);

extern uint32_t term_bitsize_mt(term_table_t *table, term_t t);

extern bool is_bvtype_mt(type_t tau);


#endif /* __THREADAFES_H */
