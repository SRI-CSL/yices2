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
