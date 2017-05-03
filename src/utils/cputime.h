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

#endif /* __CPUTIME_H */
