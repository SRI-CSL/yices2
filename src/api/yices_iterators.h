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
