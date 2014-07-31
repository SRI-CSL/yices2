/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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
