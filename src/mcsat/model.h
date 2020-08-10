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
 
#ifndef MCSAT_MODEL_H_
#define MCSAT_MODEL_H_

#include "mcsat/value.h"
#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"

/** The model */
struct mcsat_model_s {
  /** Size of the model */
  uint32_t size;
  /** Capactity of the model */
  uint32_t capacity;
  /** Map from variables to values */
  mcsat_value_t* values;
  /** Timestamps */
  uint32_t* timestamps;
  /** Global timestamp */
  uint32_t timestamp;
};

/** Construct a new model */
void mcsat_model_construct(mcsat_model_t* m);

/** Construct a copy of the model */
void mcsat_model_construct_copy(mcsat_model_t* m, const mcsat_model_t* from);

/** Destruct a new model */
void mcsat_model_destruct(mcsat_model_t* m);

/** Notification of new variables */
void mcsat_model_new_variable_notify(mcsat_model_t* m, variable_t x);

/** Does the variable have a value */
bool mcsat_model_has_value(const mcsat_model_t* m, variable_t x);

/** Get the timestamp of the variable */
uint32_t mcsat_model_get_value_timestamp(const mcsat_model_t* m, variable_t x);

/** Get the value of the variable */
const mcsat_value_t* mcsat_model_get_value(const mcsat_model_t* m, variable_t x);

/** Set x -> value. */
void mcsat_model_set_value(mcsat_model_t* m, variable_t x, const mcsat_value_t* value);

/** Unset x -> value. */
void mcsat_model_unset_value(mcsat_model_t* m, variable_t x);

#endif /* MODEL_H_ */
