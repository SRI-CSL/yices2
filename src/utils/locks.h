/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Lock interface
 * - define type lock_t + functions to access them
 *
 * This is implemented using pthreads on Unix or with
 * Windows locks.
 */

#ifndef __LOCKS_H
#define __LOCKS_H

#include <stdint.h>

#ifdef MINGW
/*
 * Windows: use CRITICAL_SECTION
 */
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0403
#endif
#include <windows.h>
typedef CRITICAL_SECTION lock_t;
#else
/*
 * Use pthread_mutex
 */
#include <pthread.h>
typedef pthread_mutex_t lock_t;
#endif


/*
 * Create a lock:
 * - returns 0 on success
 * - returns -1 on failure (and prints an error message) 
 */
extern int32_t create_lock(lock_t *lock);

/*
 * Try to lock (non-blocking)
 *
 * Return codes:
 *    0 on success
 *    1 if the lock was already taken
 *   -1 on failure 
 *
 * Prints an error message on failure
 */
extern int32_t try_lock(lock_t *lock);

/*
 * Get the lock (blocking)
 *
 * Return codes:
 *    0 on success
 *   -1 on failure
 *
 * Prints an error message if this fails.
 */
extern int32_t get_lock(lock_t *lock);

/*
 * Releate a lock
 *
 * Returns codes:
 *    0 on success
 *   -1 on failure 
 * (and prints an error message) 
 */
extern int32_t release_lock(lock_t *lock);

/*
 * Free resources
 */
extern void destroy_lock(lock_t *lock);


#endif /* __LOCKS_H */
