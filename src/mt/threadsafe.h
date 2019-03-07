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


/*
 *
 * Thread safe (non api) routines used in testing.
 *
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


/* test_api1_mt tests  */
extern bool check_bool_type_mt(type_t tau);
extern bool check_int_type_mt(type_t tau);
extern bool check_real_type_mt(type_t tau);
extern bool check_uninterpreted_type_mt(type_t tau);
extern bool check_bv_type_mt(type_t tau, uint32_t n);
extern bool check_scalar_type_mt(type_t tau, uint32_t n);
extern bool check_tuple_type_mt(type_t tau, uint32_t n, type_t comp[]);
extern bool check_function_type_mt(type_t tau, uint32_t n, type_t dom[], type_t range);
extern bool check_type_name_mt(type_t tau, const char *name);
extern bool check_pos_int_required_mt(type_t tau);
extern bool check_max_bvsize_exceeded_mt(type_t tau, int64_t size);
extern bool check_too_many_arguments_mt(type_t tau, int64_t n);
extern bool check_invalid_type_mt(type_t tau, type_t bad);

extern bool check_constant_term_mt(term_t t, type_t tau, int32_t idx);
extern bool check_uninterpreted_term_mt(term_t t, type_t tau);
extern bool check_unit_rep_mt(term_t t, type_t tau);
extern bool check_unit_tuple_mt(term_t t, type_t tau);

extern bool check_invalid_type2_mt(term_t t, type_t tau);
extern bool check_scalar_or_utype_required_mt(term_t t, type_t tau);
extern bool check_arith_constant_mt(term_t t, rational_t *q);
extern bool check_bv64_constant_mt(term_t t, uint64_t v, uint32_t n);
extern bool check_bv_constant_mt(term_t t, uint32_t *v, uint32_t n);



#endif /* __THREADAFES_H */
