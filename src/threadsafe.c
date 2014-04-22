
#include "threadsafe.h"
#include "yices_locks.h"
#include "yices_globals.h"
#include "type_printer.h"
#include "term_printer.h"

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
