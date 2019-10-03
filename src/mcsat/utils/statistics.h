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
 
#ifndef MCSAT_STATISTICS_H_
#define MCSAT_STATISTICS_H_

#include <stdio.h>
#include <stdint.h>


typedef enum {
  STATISTIC_INT,
  STATISTIC_AVG,
} statistic_type_t;

typedef int statistic_int_t;

typedef struct statistic_avg_s {
  double avg; // Current average
  uint32_t n; // How many elements
} statistic_avg_t;

static inline
void statistic_avg_add(statistic_avg_t* stat, int x) {
  stat->n ++;
  stat->avg += (x - stat->avg) / stat->n;
}

typedef struct statistic_s statistic_t;

/** A uint32_t statistic */
struct statistic_s {
  char* name;
  statistic_type_t type;
  union {
    statistic_int_t int_data;
    statistic_avg_t avg_data;
  };
  statistic_t* next;
};

typedef struct statistics_s {
  statistic_t* first;
} statistics_t;

/** Construct the statistics */
void statistics_construct(statistics_t* stats);

/** Destruct the statistics */
void statistics_destruct(statistics_t* stats);

/** Get a new int statistic */
statistic_int_t* statistics_new_int(statistics_t* stats, const char* name);

/** Get a new average statistic */
statistic_avg_t* statistics_new_avg(statistics_t* stats, const char* name);

/** Print the statistics */
/*
 * BD: changed this to use a file descriptor instead of a stream.
 */
void statistics_print(const statistics_t* stats, int out);

#endif /* STATISTICS_H_ */
