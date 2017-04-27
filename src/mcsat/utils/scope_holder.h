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
 
#ifndef MCSAT_SCOPE_HOLDER_H_
#define MCSAT_SCOPE_HOLDER_H_

#include "utils/int_vectors.h"

/**
 * Utility to push/pop values of int32_t and uint32_t variables.
 */
typedef struct scope_holder_s {

  /** Trace of values */
  ivector_t trace;

  /** Size of the push (number of vars) */
  uint32_t push_size;

} scope_holder_t;

/** Construct the scope holder for the given size */
void scope_holder_construct(scope_holder_t* scope);

/** Destruct the scope holder. */
void scope_holder_destruct(scope_holder_t* scope);

/**
 * Push the scope context. Arguments are int32_t* pointers ending with NULL.
 * The scope should be popped with the arguments in the same order.
 */
void scope_holder_push(scope_holder_t* scope, ...);

/**
 * Push the scope context. Arguments are int32_t* pointers ending with NULL.
 * The arguments should be in the same order as they were pushed.
 * */
void scope_holder_pop(scope_holder_t* scope, ...);

#endif /* MCSAT_SCOPE_HOLDER_H_ */
