/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "mcsat/utils/statistics.h"
#include "utils/memalloc.h"
#include "io/simple_printf.h"

#include <assert.h>

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
    safe_free(prev->name);
    safe_free(prev);
  }
}

/** Get a new uint32_t statistic */
statistic_int_t* statistics_new_int(statistics_t* stats, const char* name) {
  statistic_t* new;

  new = safe_malloc(sizeof(statistic_t));
  new->type = STATISTIC_INT;
  new->int_data = 0;
  new->name = safe_strdup(name);
  new->next = stats->first;

  stats->first = new;

  return &new->int_data;
}

/** Get a new uint32_t statistic */
statistic_avg_t* statistics_new_avg(statistics_t* stats, const char* name) {
  statistic_t* new;

  new = safe_malloc(sizeof(statistic_t));
  new->type = STATISTIC_AVG;
  new->avg_data.avg = 0;
  new->avg_data.n = 0;
  new->name = safe_strdup(name);
  new->next = stats->first;

  stats->first = new;

  return &new->avg_data;
}

/** Print the statistics */
void statistics_print(const statistics_t* stats, int out) {
  statistic_t *current;
  print_buffer_t pb;

  reset_print_buffer(&pb);
  current = stats->first;
  while (current != NULL) {
    print_buffer_append_string(&pb, " :");
    print_buffer_append_string(&pb, current->name);
    print_buffer_append_string(&pb, " ");
    write_buffer(out, &pb);
    switch (current->type) {
    case STATISTIC_INT:
      print_buffer_append_int64(&pb, current->int_data);
      break;
    case STATISTIC_AVG:
      print_buffer_append_float(&pb, current->avg_data.avg, 4);
      break;
    default:
      assert(false);
    }
    print_buffer_append_string(&pb, "\n");
    write_buffer(out, &pb);
    current = current->next;
  }
}
