/*
 * The Yices SMT Solver. Copyright 2016 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * Lock interface
 */

#include "utils/locks.h"

#ifndef MINGW

/*
 * POSIX: USE PTHREADS
 */
#include <stdio.h>
#include <assert.h>
#include <errno.h>

/*
 * Set DEBUG to 1 to include debugging code
 */
#define DEBUG 0

#if DEBUG
static pthread_mutexattr_t mta;
static pthread_mutexattr_t *mattr = &mta;
#else
static pthread_mutexattr_t *mattr = NULL;
#endif


/*
 * Create a lock:
 * - returns 0 on success
 * - returns -1 on failure (and prints an error message) 
 */
int32_t create_lock(lock_t *lock) {
  int retcode;

#if DEBUG
  retcode = pthread_mutexattr_settype(&mta, PTHREAD_MUTEX_ERRORCHECK);
  if (retcode) {
    perror("create_lock: pthread_mutexattr_settype: "); 
    return -1;
  }
#endif

  retcode = pthread_mutex_init(lock, mattr);
  if (retcode) {
    perror("create_lock: pthread_mutex_init: ");
    return -1;
  }

  return 0;
}


/*
 * Try to acquire the lock (non-blocking)
 *
 * Return codes:
 *   0 means that this thread got the lock
 *   1 means that the lock is already taken
 *  -1 is an error
 */
int32_t try_lock(lock_t *lock) {
  int retcode;

  retcode = pthread_mutex_trylock(lock);
  if (retcode == 0) return 0;
  if (retcode == EBUSY) return 1;

  // error
  perror("try_lock: pthread_mutex_trylock: ");
  return -1;
}


/*
 * Block then acquire the lock
 *
 * Return codes:
 *    0 means success
 *   -1 means error
 */
int32_t get_lock(lock_t *lock) {
  if (pthread_mutex_lock(lock)) {
    perror("get_lock: pthread_mutex_lock: ");
    return -1;
  }
  return 0;
}

/*
 * Unlock
 */
int32_t release_lock(lock_t *lock) {
  if (pthread_mutex_unlock(lock)) {
    perror("release_lock: pthread_mutex_unlock: ");
    return -1;
  }
  return 0;
}

/*
 * Delete
 */
void destroy_lock(lock_t *lock) {
  if (pthread_mutex_destroy(lock)) {
    perror("destroy_lock: pthread_mutex_destroy: ");
  }
}

#else

/*
 * WINDOWS
 */
int32_t create_lock(lock_t *lock) {
  /* to check the return codes would require knowing the version of windows we are running on :-( */
  InitializeCriticalSectionAndSpinCount(lock, 200);
  return 0;
}

int32_t try_lock(lock_t *lock) {
  if (TryEnterCriticalSection(lock) != 0) {
    return 0;
  }
  return 1;
}

int32_t get_lock(lock_t *lock) {
  EnterCriticalSection(lock);
  return 0;
}

int32_t release_lock(lock_t *lock) {
  LeaveCriticalSection(lock);
  return 0;
}

void destroy_lock(lock_t *lock) {
  DeleteCriticalSection(lock);
}

#endif
