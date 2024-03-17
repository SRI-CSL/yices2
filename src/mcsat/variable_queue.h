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
 
#ifndef MCSAT_VAR_QUEUE_H_
#define MCSAT_VAR_QUEUE_H_

#include "mcsat/variable_db.h"

/**
 * Heap and variable activities for variable selection heuristic
 * - activity[x]: for every variable x between 0 and nvars - 1
 *   activity[-1] = DBL_MAX (higher than any activity)
 *   activity[-2] = -1.0 (lower than any variable activity)
 * - heap_index[x]: for every variable x,
 *      heap_index[x] = i if x is in the heap and heap[i] = x
 *   or heap_index[x] = -1 if x is not in the heap
 * - heap: array of nvars + 1 variables
 * - heap_last: index of last element in the heap
 *   heap[0] = -1,
 *   for i=1 to heap_last, heap[i] = x for some variable x
 * - size = number of variable (nvars)
 * - vmax = variable index (last variable not in the heap)
 * - act_inc: variable activity increment
 * - inv_act_decay: inverse of variable activity decay (e.g., 1/0.95)
 *
 * The set of variables is split into two segments:
 * - [0 ... vmax-1] = variables that are in the heap or have been in the heap
 * - [vmax ... size-1] = variables that may not have been in the heap
 *
 * To pick a decision variable:
 * - search for the most active unassigned variable in the heap
 * - if the heap is empty or all its variables are already assigned,
 *   search for the first unassigned variables in [vmax ... size-1]
 *
 * Initially: we set vmax to 0 (nothing in the heap yet) so decision
 * variables are picked in increasing order, starting from 0.
 */
typedef struct var_queue_s {
  double *activity;
  int32_t *heap_index;
  variable_t *heap;
  uint32_t heap_last;
  uint32_t size;
  uint32_t vmax;
  double act_increment;
  double inv_act_decay;
} var_queue_t;

/**
 * Construct heap for n variables
 * - heap is initially empty: heap_last = 0
 * - heap[0] = -1 is a marker, with activity[-1] higher
 *   than any variable activity.
 * - we also use -2 as a marker with negative activity
 * - activity increment and threshold are set to their
 *   default initial value.
 */
void var_queue_construct(var_queue_t *queue);

/** Extend the heap for n variables. */
void var_queue_extend(var_queue_t *queue, uint32_t n);

/** Destruct the queue */
void var_queue_destruct(var_queue_t *queue);

/** Check whether the heap is empty. */
bool var_queue_is_empty(var_queue_t *queue);

/** Get and remove top element (the heap must not be empty) */
variable_t var_queue_pop(var_queue_t *queue);

/** Removes one variable from the heap (var must be on the heap) */
void var_queue_remove(var_queue_t *queue, variable_t var);

/** Get and remove random element (the heap must not be empty) */
variable_t var_queue_random(var_queue_t *queue, double *seed);

/**
 * Insert x into the heap, using its current activity.
 * No effect if x is already in the heap.
 * - x must be between 0 and nvars - 1
 */
void var_queue_insert(var_queue_t *queue, variable_t x);

/** Increase activity of variable x (factor times). */
void var_queue_bump_variable(var_queue_t *heap, variable_t x, uint32_t factor);

/** Get the activity of the variable */
double var_queue_get_activity(const var_queue_t* queue, variable_t x);

/** Set the activity of the variable */
void var_queue_set_activity(var_queue_t* queue, variable_t x, double a);

/** Decay. */
void var_queue_decay_activities(var_queue_t *queue);

/** Compare two variables by score */
int var_queue_cmp_variables(var_queue_t *queue, variable_t x, variable_t y);

/** Sweep the queue */
void var_queue_gc_sweep(var_queue_t* queue, const gc_info_t* gc_vars);

#endif /* MCSAT_VAR_QUEUE_H_ */
