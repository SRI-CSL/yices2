#ifndef __CPUTIME_H
#define __CPUTIME_H


/*
 * get_cpu_time() returns CPU time (user + system time) used
 * by the process since its start.
 *
 * getrusage should work on all platforms we support,
 * except mingw
 */

#ifndef MINGW

#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static struct rusage ru_buffer;

static inline double get_cpu_time(void) {
  getrusage(RUSAGE_SELF, &ru_buffer);
  return ru_buffer.ru_utime.tv_sec + ru_buffer.ru_stime.tv_sec 
    + (ru_buffer.ru_utime.tv_usec + ru_buffer.ru_stime.tv_usec) * 1e-6;
}

#else

#include <time.h>

static inline double get_cpu_time(void) {
  return ((double) clock())/CLOCKS_PER_SEC;
}

#endif


/*
 * When printing time differences (t1 - t2), 
 * it may happen that rounding erors cause the difference
 * to be printed as -0, even though t1 should always be >= t2.
 * To fix this use time_diff(t1, t2) rather than (t1 - t2)
 */
static inline double time_diff(double t1, double t2) {
  double d;
  d = t1 - t2;
  return d < 0.00001 ? 0.0 : d;
}

#endif /* __CPUTIME_H */
