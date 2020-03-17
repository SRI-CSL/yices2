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

#ifndef __YICES_LOCKS_H
#define __YICES_LOCKS_H

/*
 * We only need locks in THREAD_SAFE mode.
 *
 */
#ifdef THREAD_SAFE

#include <stdint.h>


#ifdef MINGW
#include <synchapi.h>
typedef CRITICAL_SECTION yices_lock_t;
#else
#include <pthread.h>
typedef pthread_mutex_t yices_lock_t;
#endif


/* returns 0 on success; -1 on failure (and prints an error message) */
extern int32_t create_yices_lock(yices_lock_t* lock);

/* returns 0 on success; 1 if the lock was already taken; -1 on failure (and prints an error message) */
extern int32_t try_yices_lock(yices_lock_t* lock);

/* returns 0 on success; -1 on failure (and prints an error message) */
extern int32_t get_yices_lock(yices_lock_t* lock);

/* returns 0 on success; -1 on failure (and prints an error message) */
extern int32_t release_yices_lock(yices_lock_t* lock);

extern void destroy_yices_lock(yices_lock_t* lock);


#endif

#endif /* __YICES_LOCKS_H */
