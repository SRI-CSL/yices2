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
 
#include "mcsat/model.h"

#include "utils/memalloc.h"

static inline
void mcsat_model_ensure_capacity(mcsat_model_t* m, uint32_t capacity) {
  if (capacity > m->capacity) {
    m->values = (mcsat_value_t*) safe_realloc(m->values, sizeof(mcsat_value_t)*capacity);
    m->timestamps = (uint32_t*) safe_realloc(m->timestamps, sizeof(uint32_t)*capacity);
    m->capacity = capacity;
  }
}

static
void mcsat_model_resize(mcsat_model_t* m, uint32_t size) {
  uint32_t i;

  assert(size >= m->size);

  if (size == m->size) {
    return;
  } else if (size > m->size) {
    mcsat_model_ensure_capacity(m, size + size / 2);
    for (i = m->size; i < size; ++ i) {
      mcsat_value_construct_default(m->values + i);
      m->timestamps[i] = 0;
    }
  }

  m->size = size;
}

#define MCSAT_MODEL_INITIAL_CAPACITY 100

void mcsat_model_construct(mcsat_model_t* m) {
  m->size = 0;
  m->capacity = 0;
  m->values = NULL;
  m->timestamps = NULL;
  m->timestamp = 0;
  mcsat_model_ensure_capacity(m, MCSAT_MODEL_INITIAL_CAPACITY);
}

void mcsat_model_construct_copy(mcsat_model_t* m, const mcsat_model_t* from) {
  m->capacity = 0;
  m->values = NULL;
  m->timestamps = NULL;
  mcsat_model_ensure_capacity(m, from->capacity);
  m->size = from->size;
  mcsat_value_construct_copy_n(m->values, from->values, m->size);
  memcpy(m->timestamps, from->timestamps, m->capacity * sizeof(uint32_t));
  m->timestamp = from->timestamp;
}

void mcsat_model_destruct(mcsat_model_t* m) {
  uint32_t i;
  for (i = 0; i < m->size; ++ i) {
    mcsat_value_destruct(m->values + i);
  }
  safe_free(m->values);
  safe_free(m->timestamps);
}

void mcsat_model_copy(mcsat_model_t* m, const mcsat_model_t* from) {
  mcsat_model_ensure_capacity(m, from->capacity);
  m->size = from->size;
  mcsat_value_construct_copy_n(m->values, from->values, m->size);
  memcpy(m->timestamps, from->timestamps, m->capacity * sizeof(uint32_t));
  m->timestamp = from->timestamp;
}

void mcsat_model_new_variable_notify(mcsat_model_t* m, variable_t x) {
  if (x >= m->size) {
    mcsat_model_resize(m, x + 1);
  }
}

bool mcsat_model_has_value(const mcsat_model_t* m, variable_t x) {
  // Make sure enough space
  if (x >= m->size) {
    return false;
  }
  return (m->values[x].type != VALUE_NONE);
}

const mcsat_value_t* mcsat_model_get_value(const mcsat_model_t* m, variable_t x) {
  if (x >= m->size) {
    return &mcsat_value_none;
  } else {
    return m->values + x;
  }
}

uint32_t mcsat_model_get_value_timestamp(const mcsat_model_t* m, variable_t x) {
  if (x >= m->size) {
    return 0;
  } else {
    return m->timestamps[x];
  }
}

void mcsat_model_set_value(mcsat_model_t* m, variable_t x, const mcsat_value_t* value) {
  // Make sure enough space
  if (x >= m->size) {
    mcsat_model_resize(m, x + 1);
  }
  mcsat_value_t* x_value = m->values + x;
  if ((x_value->type != value->type) || (!mcsat_value_eq(x_value, value))) {
    mcsat_value_assign(x_value, value);
    m->timestamps[x] = ++ m->timestamp;
  }
}

void mcsat_model_unset_value(mcsat_model_t* m, variable_t x) {
  if (x < m->size) {
    assert(m->values[x].type != VALUE_NONE);
    mcsat_value_destruct(m->values + x);
    mcsat_value_construct_default(m->values + x);
    m->timestamps[x] = ++ m->timestamp;
  }
}
