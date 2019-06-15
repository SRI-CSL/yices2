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

/*
 * ESTIMATE CPU TIME
 *
 * getrusage should work on all platforms we support,
 * except mingw. (Also, not supported by Cygwin on Windows 95 and 98).
 *
 * The function used to be 'inline' in cputime.h
 * but GCC 4.6.3 gives compilation warnings.
 */

#include "utils/cputime.h"

#ifndef MINGW

#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

double get_cpu_time(void) {
  //static struct rusage ru_buffer;  IAM
  struct rusage ru_buffer;
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
