/*
 * Functions to iterate through all the models, contexts, and buffers allocated.
 */

#ifndef __YICES_ITERATORS_H
#define __YICES_ITERATORS_H

#include "bvarith_buffers.h"
#include "bvarith64_buffers.h"
#include "bvlogic_buffers.h"
#include "models.h"
#include "context.h"

/*
 * Every iteration function takes an auxiliary pointer aux
 * and a function f and call f(aux, x) for all global
 * objects x of a specified type.
 */
extern void bvarith_buffer_iterate(void *aux, void (*f)(void *, bvarith_buffer_t *));
extern void bvarith64_buffer_iterate(void *aux, void (*f)(void *, bvarith64_buffer_t *));
extern void bvlogic_buffer_iterate(void *aux, void (*f)(void *, bvlogic_buffer_t *));
extern void context_iterate(void *aux, void (*f)(void *, context_t *));
extern void model_iterate(void *aux, void (*f)(void *, model_t *));

#endif /* __YICES_ITERATORS_H */
