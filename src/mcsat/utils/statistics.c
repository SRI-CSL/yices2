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
 
#include "mcsat/utils/statistics.h"
#include "utils/memalloc.h"

#include <inttypes.h>

/** A uint32_t statistic */
struct statistic_s {
  const char* name;
  uint32_t data;
  statistic_t* next;
};

/** Construct the statistics */
void statistics_construct(statistics_t* stats) {
  stats->first = NULL;
}

/** Destruct the statistics */
void statistics_destruct(statistics_t* stats) {
  statistic_t* prev, *current;

  current = stats->first;
  while (current != NULL) {
    prev = current;
    current = current->next;
    safe_free(prev);
  }
}

/** Get a new uint32_t statistic */
uint32_t* statistics_new_uint32(statistics_t* stats, const char* name) {
  statistic_t* new;

  new = safe_malloc(sizeof(statistic_t));
  new->data = 0;
  new->name = name;
  new->next = stats->first;

  stats->first = new;

  return &new->data;
}

/** Print the statistics */
void statistics_print(const statistics_t* stats, FILE* out) {
  statistic_t* current;

  current = stats->first;
  while (current != NULL) {
    fprintf(out, " :%s %"PRIu32"\n", current->name, current->data);
    current = current->next;
  }
}
