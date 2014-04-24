
#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <inttypes.h>

#include "threadsafe.h"
#include "yices.h"
#include "yices_locks.h"
#include "yices_globals.h"
#include "type_printer.h"
#include "term_printer.h"

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

  retval = term_type(__yices_globals.terms, t) == tau;

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
