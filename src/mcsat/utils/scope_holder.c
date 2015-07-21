/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/utils/scope_holder.h"

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

void scope_holder_construct(scope_holder_t* scope) {
  init_ivector(&scope->trace, 0);
  scope->push_size = 0;
}

void scope_holder_destruct(scope_holder_t* scope) {
  delete_ivector(&scope->trace);
}

void scope_holder_push(scope_holder_t* scope, ...) {
  int32_t* var;
  uint32_t count;

  va_list ap;
  va_start(ap, scope);

  count = 0;
  var = va_arg(ap, int32_t*);
  while (var != NULL) {
    ivector_push(&scope->trace, *var);
    count ++;
    var = va_arg(ap, int32_t*);
  }

  assert(count > 0);
  assert(scope->push_size == 0 || scope->push_size == count);

  if (scope->push_size == 0) {
    scope->push_size = count;
  }

  va_end(ap);
}

void scope_holder_pop(scope_holder_t* scope, ...) {
  int32_t *var, *data;
  uint32_t count;

  assert(scope->trace.size > 0);
  assert(scope->trace.size >= scope->push_size);

  va_list ap;
  va_start(ap, scope);

  count = 0;
  var = va_arg(ap, int32_t*);
  data = scope->trace.data + scope->trace.size - scope->push_size;
  while (var != NULL) {
    *var = *data;
    count ++;
    data ++;
    var = va_arg(ap, int32_t*);
  }

  assert(count > 0);
  assert(scope->push_size == count);

  ivector_shrink(&scope->trace, scope->trace.size - count);

  va_end(ap);
}
