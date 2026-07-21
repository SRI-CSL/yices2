/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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

/** Copy model */
void mcsat_model_copy(mcsat_model_t* m, const mcsat_model_t* from);

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
