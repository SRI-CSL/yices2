/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "yices_locks.h"

// we need _WIN32_WINNT as 0x0403 or later

int32_t create_yices_lock(yices_lock_t* lock){
  /* to check the return codes meaning would require knowing what version of windows we are running on :-( */
  InitializeCriticalSectionAndSpinCount(lock, 2000);
  return 0;
}

int32_t create_yices_recursive_lock(yices_lock_t* lock){
  /*
   * Windows critical sections are recursive for the owning thread.
   */
  return create_yices_lock(lock);
}

int32_t try_yices_lock(yices_lock_t* lock){
  if (TryEnterCriticalSection(lock) != 0) {
    return 0;
  }
  return 1;
}


int32_t get_yices_lock(yices_lock_t* lock){
  /* void return type */
  EnterCriticalSection(lock);
  return 0;
}

int32_t release_yices_lock(yices_lock_t* lock){
  /* void return type */
  LeaveCriticalSection(lock);
  return 0;
}

void destroy_yices_lock(yices_lock_t* lock){
  /* void return type */
  DeleteCriticalSection(lock);
}
