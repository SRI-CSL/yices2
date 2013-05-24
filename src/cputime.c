/*
 * CPU TIME: getrusage should work on all platforms we support,
 * except mingw.
 *
 * The function used to be 'inline' in cputime.h
 * but GCC 4.6.3 gives compilation warnings (r
 */

#include "cputime.h"

#ifndef MINGW

#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

double get_cpu_time(void) {
  static struct rusage ru_buffer;
  getrusage(RUSAGE_SELF, &ru_buffer);
  return ru_buffer.ru_utime.tv_sec + ru_buffer.ru_stime.tv_sec 
    + (ru_buffer.ru_utime.tv_usec + ru_buffer.ru_stime.tv_usec) * 1e-6;
}

#else

#include <time.h>

double get_cpu_time(void) {
  return ((double) clock())/CLOCKS_PER_SEC;
}

#endif

