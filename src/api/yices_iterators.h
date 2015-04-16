/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * FUNCTIONS TO ITERATE THROUGH ALL THE MODELS, CONTEXTS, AND BUFFERS ALLOCATED.
 */

#ifndef __YICES_ITERATORS_H
#define __YICES_ITERATORS_H

#include "context/context_types.h"
#include "model/models.h"
#include "terms/balanced_arith_buffers.h"
#include "terms/bvarith64_buffers.h"
#include "terms/bvarith_buffers.h"
#include "terms/bvlogic_buffers.h"

/*
 * Every iteration function takes an auxiliary pointer aux
 * and a function f and call f(aux, x) for all global
 * objects x of a specified type.
 */
extern void arith_buffer_iterate(void *aux, void (*f)(void *, rba_buffer_t *));
extern void bvarith_buffer_iterate(void *aux, void (*f)(void *, bvarith_buffer_t *));
extern void bvarith64_buffer_iterate(void *aux, void (*f)(void *, bvarith64_buffer_t *));
extern void bvlogic_buffer_iterate(void *aux, void (*f)(void *, bvlogic_buffer_t *));
extern void context_iterate(void *aux, void (*f)(void *, context_t *));
extern void model_iterate(void *aux, void (*f)(void *, model_t *));

#endif /* __YICES_ITERATORS_H */
