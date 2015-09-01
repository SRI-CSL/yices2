/*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */
 
#ifndef MCSAT_STATISTICS_H_
#define MCSAT_STATISTICS_H_

#include <stdio.h>
#include <stdint.h>

typedef struct statistic_s statistic_t;

typedef struct {
  statistic_t* first;
} statistics_t;

/** Construct the statistics */
void statistics_construct(statistics_t* stats);

/** Destruct the statistics */
void statistics_destruct(statistics_t* stats);

/** Get a new uint32_t statistic */
uint32_t* statistics_new_uint32(statistics_t* stats, const char* name);

/** Print the statistics */
void statistics_print(const statistics_t* stats, FILE* out);

#endif /* STATISTICS_H_ */
