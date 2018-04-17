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

#ifndef __CPUTIME_H
#define __CPUTIME_H

#include <sys/time.h>

#include <sys/types.h>
#include <sys/resource.h>
#include <unistd.h>

#ifdef NDEBUG
  #define TIME  0
#else
  #define TIME  1
#endif

/*
 * get_cpu_time() returns CPU time (user + system time) used
 * by the process since its start. Unit = seconds.
 */
extern double get_cpu_time(void);



/*
 * When printing time differences (t1 - t2),
 * it may happen that rounding errors cause the difference
 * to be printed as -0, even though t1 should always be >= t2.
 * To fix this use time_diff(t1, t2) rather than (t1 - t2)
 */
static inline double time_diff(double t1, double t2) {
  double d;
  d = t1 - t2;
  return d < 0.00001 ? 0.0 : d;
}

static inline long long time_user_diff(struct timeval *end, struct timeval *start) {
  long long msec;
  msec = (end->tv_sec - start->tv_sec)*1000000;
  msec += (end->tv_usec - start->tv_usec);
  return (msec < 0 ? 0 : msec);
}

#if TIME

//extern void get_user_time(struct timeval *start);
static void get_user_time(struct timeval *start) {
  struct rusage ru_buffer;
  getrusage(RUSAGE_SELF, &ru_buffer);
  start->tv_sec = ru_buffer.ru_utime.tv_sec;
  start->tv_usec = ru_buffer.ru_utime.tv_usec;
}

  #define TIME_START()    \
    struct timeval start; \
    get_user_time(&start);

  #define TIME_END(store) {                \
    struct timeval end;                    \
    get_user_time(&end);                   \
    store += time_user_diff(&end, &start); \
  }

  #define TIME_START2()    \
    struct timeval start2; \
    get_user_time(&start2);

  #define TIME_END2(store) {                 \
    struct timeval end2;                     \
    get_user_time(&end2);                    \
    store += time_user_diff(&end2, &start2); \
  }

#else

#define TIME_START()        //
#define TIME_END(store)     //
#define TIME_START2()       //
#define TIME_END2(store)    //

#endif



#endif /* __CPUTIME_H */
