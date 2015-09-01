/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#include "mcsat/model.h"

#include "utils/memalloc.h"

static inline
void mcsat_model_ensure_capacity(mcsat_model_t* m, uint32_t capacity) {
  if (capacity > m->capacity) {
    m->values = (mcsat_value_t*) safe_realloc(m->values, sizeof(mcsat_value_t)*capacity);
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
    }
  }

  m->size = size;
}

#define MCSAT_MODEL_INITIAL_CAPACITY 100

void mcsat_model_construct(mcsat_model_t* m) {
  m->size = 0;
  m->capacity = 0;
  m->values = NULL;
  mcsat_model_ensure_capacity(m, MCSAT_MODEL_INITIAL_CAPACITY);
}

void mcsat_model_destruct(mcsat_model_t* m) {
  uint32_t i;
  for (i = 0; i < m->size; ++ i) {
    mcsat_value_destruct(m->values + i);
  }
  free(m->values);
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

void mcsat_model_set_value(mcsat_model_t* m, variable_t x, const mcsat_value_t* value) {
  // Make sure enough space
  if (x >= m->size) {
    mcsat_model_resize(m, x + 1);
  }
  mcsat_value_assign(m->values + x, value);
}

void mcsat_model_unset_value(mcsat_model_t* m, variable_t x) {
  if (x < m->size) {
    assert(m->values[x].type != VALUE_NONE);
    mcsat_value_destruct(m->values + x);
    mcsat_value_construct_default(m->values + x);
  }
}
