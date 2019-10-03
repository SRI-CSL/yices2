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
/*
 * BD: changed this to use a file descriptor instead of a stream.
 */
void statistics_print(const statistics_t* stats, int out);

#endif /* STATISTICS_H_ */
