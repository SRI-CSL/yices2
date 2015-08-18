 /*
 * The Yices SMT Solver. Copyright 2015 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * timespec arithmetic
 */

typedef struct timespec timespec_t;


/*
 * Return the difference between 'start' and 'end'
 */
static inline timespec_t ts_diff(timespec_t start, timespec_t end)
{
	timespec_t temp;
	if ((end.tv_nsec-start.tv_nsec) < 0) {
		temp.tv_sec  = end.tv_sec - start.tv_sec-1;
		temp.tv_nsec = 1000000000L + end.tv_nsec-start.tv_nsec;
	} else {
		temp.tv_sec  = end.tv_sec  - start.tv_sec;
		temp.tv_nsec = end.tv_nsec - start.tv_nsec;
	}
	return temp;
}


/*
 * Add 'delta' to 'base'
 */
static inline void ts_add(timespec_t *base, timespec_t delta)
{
    base->tv_sec  += delta.tv_sec;
    base->tv_nsec += delta.tv_nsec;
    if (base->tv_nsec >= 1000000000L) {
        base->tv_sec++;
        base->tv_nsec -= 1000000000L;
    }
}
