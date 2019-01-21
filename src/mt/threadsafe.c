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


#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <inttypes.h>

#include "threadsafe.h"
#include "yices.h"
#include "yices_locks.h"
#include "api/yices_globals.h"
#include "io/type_printer.h"
#include "io/term_printer.h"

/*
 * Print the type table
 */
void show_types_mt(FILE* output) {
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  fprintf(output, "\n---- Type table ----\n");
  pp_type_table(output, __yices_globals.types);

  release_yices_lock(lock);

}


/*
 * Print the term table
 */
void show_terms_mt(FILE* output) {
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  fprintf(output, "\n---- Term table -----\n");
  pp_term_table(output, __yices_globals.terms);

  release_yices_lock(lock);

}

/*
 * Predicate: check whether t has type tau
 */
bool has_type_mt(type_t tau, term_t t) {
  bool retval;
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  retval = (term_type(__yices_globals.terms, t) == tau);

  release_yices_lock(lock);

  return retval;
}

void print_term_mt(FILE* output, term_t t){
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  print_term(output, __yices_globals.terms, t);

  release_yices_lock(lock);

}

void print_type_mt(FILE* output, type_t t){
  yices_lock_t *lock = &__yices_globals.lock;

  get_yices_lock(lock);

  print_type(output, __yices_globals.types, t);

  release_yices_lock(lock);

}

uint32_t term_bitsize_mt (term_table_t *table, term_t t) {
  yices_lock_t *lock = &__yices_globals.lock;
  uint32_t retval;

  get_yices_lock(lock);

  retval = term_bitsize (table, t);

  release_yices_lock(lock);

  return retval;
}

bool is_bvtype_mt(type_t tau) {
  yices_lock_t *lock = &__yices_globals.lock;
  bool retval;

  get_yices_lock(lock);

  retval = (type_kind(__yices_globals.types, tau) == BITVECTOR_TYPE);

  release_yices_lock(lock);

  return retval;
}
