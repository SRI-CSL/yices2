/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
