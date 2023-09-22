/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2019 SRI International.
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

//this should go once we are more at home in yices.
#include <stdio.h>
#include <assert.h>
#include <errno.h>
#include <string.h>

#include "yices_locks.h"

static void print_error(const char *caller, const char *syscall, int errnum) {
  char buffer[64];

  strerror_r(errnum, buffer, sizeof(buffer));
  fprintf(stderr, "%s failed: %s returned %d: %s\n", caller, syscall,
	  errnum, buffer);
}

int32_t create_yices_lock(yices_lock_t* lock){
  int32_t retcode;
#ifndef NDEBUG
  pthread_mutexattr_t mta;
  pthread_mutexattr_t *mattr = &mta;
#else
  pthread_mutexattr_t *mattr = NULL;
#endif

#ifndef NDEBUG
  retcode = pthread_mutexattr_init(mattr);
  if(retcode)
    print_error("create_yices_lock", "pthread_mutexattr_init", retcode);
  retcode = pthread_mutexattr_settype(mattr, PTHREAD_MUTEX_ERRORCHECK);
  if(retcode)
    print_error("create_yices_lock", "pthread_mutextattr_settype", retcode);
#endif
  retcode = pthread_mutex_init(lock, mattr);
  if(retcode)
    print_error("create_yices_lock", "pthread_mutex_init", retcode);
  assert(retcode == 0);
  return retcode;
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
  int32_t retcode = pthread_mutex_lock(lock);
  if(retcode){
    print_error("get_yices_lock", "pthread_mutex_lock", retcode);
  }
  assert(retcode == 0);
  return retcode;
}

int32_t release_yices_lock(yices_lock_t* lock){
  int32_t retcode = pthread_mutex_unlock(lock);
  if(retcode){
    print_error("release_yices_lock", "pthread_mutex_unlock", retcode);
  }
  assert(retcode == 0);
  return retcode;
}

void destroy_yices_lock(yices_lock_t* lock){
  int32_t retcode = pthread_mutex_destroy(lock);
  if(retcode){
    print_error("destroy_yices_lock", "pthread_mutex_destroy", retcode);
  }
  assert(retcode == 0);
}
