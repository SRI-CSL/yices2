/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

//this should go once we are more at home in yices.
#include <stdio.h>
#include <assert.h>
#include <errno.h>
#include <string.h>

#include "yices_locks.h"
#include "threads.h"

static void print_error(const char *caller, const char *syscall, int errnum) {
  char buffer[64];

  strerror_r(errnum, buffer, sizeof(buffer));
  fprintf(stderr, "%s failed: %s returned %d: %s\n", caller, syscall,
	  errnum, buffer);
}

int32_t create_yices_lock(yices_lock_t* lock){
  pthread_mutexattr_t *mattr = NULL;

#ifndef NDEBUG
  /* Make the mutex detect recursive locks. */
  pthread_mutexattr_t mta;

  mattr = &mta;

  check_thread_api(pthread_mutexattr_init(mattr),
		   "create_yices_lock: pthread_mutexattr_init");
  check_thread_api(pthread_mutexattr_settype(mattr,
					     PTHREAD_MUTEX_ERRORCHECK),
		   "create_yices_lock: pthread_mutextattr_settype");
#endif

  check_thread_api(pthread_mutex_init(lock, mattr),
		   "create_yices_lock: pthread_mutex_init");

#ifndef NDEBUG
  check_thread_api(pthread_mutexattr_destroy(mattr),
		   "create_yices_lock: pthread_mutexattr_destroy");
#endif

  return 0;
}

int32_t create_yices_recursive_lock(yices_lock_t* lock){
  pthread_mutexattr_t mta;

  check_thread_api(pthread_mutexattr_init(&mta),
		   "create_yices_recursive_lock: pthread_mutexattr_init");
  check_thread_api(pthread_mutexattr_settype(&mta,
					     PTHREAD_MUTEX_RECURSIVE),
		   "create_yices_recursive_lock: pthread_mutextattr_settype");

  check_thread_api(pthread_mutex_init(lock, &mta),
		   "create_yices_recursive_lock: pthread_mutex_init");
  check_thread_api(pthread_mutexattr_destroy(&mta),
		   "create_yices_recursive_lock: pthread_mutexattr_destroy");

  return 0;
}

int32_t try_yices_lock(yices_lock_t* lock){
  int32_t retcode = pthread_mutex_trylock(lock);
  if(retcode){
    if(retcode == EBUSY){
      return 1;
    } else {
      print_error("try_yices_lock", "pthread_mutex_trylock", retcode);
    }
    return -1;
  }
  return retcode;
}


int32_t get_yices_lock(yices_lock_t* lock){
  check_thread_api(pthread_mutex_lock(lock),
		   "get_yices_lock: pthread_mutex_lock");

  return 0;
}

int32_t release_yices_lock(yices_lock_t* lock){
  check_thread_api(pthread_mutex_unlock(lock),
		   "release_yices_lock: pthread_mutex_unlock");

  return 0;
}

void destroy_yices_lock(yices_lock_t* lock){
  check_thread_api(pthread_mutex_destroy(lock),
		   "destroy_yices_lock: pthread_mutex_destroy");
}
