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

#include "yices_locks.h"

// we need _WIN32_WINNT as 0x0403 or later

int32_t create_yices_lock(yices_lock_t* lock){
  /* to check the return codes meaning would require knowing what version of windows we are running on :-( */
  InitializeCriticalSectionAndSpinCount(lock, 2000);
  return 0;
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
