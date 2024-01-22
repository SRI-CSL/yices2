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

#ifndef VALUE_VERSION_SET_H
#define VALUE_VERSION_SET_H

typedef enum {
  VALUE_SET_INTERSECTION,
  VALUE_SET_UNION,
} value_version_set_type_t;

typedef struct value_version_set_struct value_version_set_t;

value_version_set_t* value_version_set_new(value_version_set_type_t type);

void value_version_set_delete(value_version_set_t *set);

uint32_t value_version_set_count(const value_version_set_t *set);

void value_version_set_reset(value_version_set_t *set);

/** Updates the set with regard to new_set. Returns true iff an the set changed. A new timestamp is generated in any case. */
bool value_version_set_push(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size);

/** Behaves like value_version_set_push, but calls f(aux, v) for each value in new_set and pushes the value only iff true is returned. */
typedef bool (*value_version_set_filter_t)(void *aux, const mcsat_value_t *val);
bool value_version_set_push_filter(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size, void *aux, value_version_set_filter_t f);

/** Specific push function that requires an not-empty intersection set. Updates all that are not in new_set. */
bool value_version_set_push_intersect_inverted(value_version_set_t *set, mcsat_value_t *new_set, size_t new_set_size);

void value_version_set_pop(value_version_set_t *set, size_t count);

bool value_version_set_contains(const value_version_set_t *set, const mcsat_value_t *k);

uint32_t value_version_set_get_timestamp(const value_version_set_t *set);

void value_version_set_print(const value_version_set_t *set, FILE *out);

void value_version_set_print_at(const value_version_set_t *set, uint32_t timestamp, FILE *out);

#endif /* VALUE_VERSION_SET_H */
