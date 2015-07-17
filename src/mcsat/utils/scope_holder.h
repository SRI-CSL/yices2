/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
