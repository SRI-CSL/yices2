/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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

/* returns 0 on success; -1 on failure (and prints an error message) */
extern int32_t create_yices_recursive_lock(yices_lock_t* lock);

/* returns 0 on success; 1 if the lock was already taken; -1 on failure (and prints an error message) */
extern int32_t try_yices_lock(yices_lock_t* lock);

/* returns 0 on success; -1 on failure (and prints an error message) */
extern int32_t get_yices_lock(yices_lock_t* lock);

/* returns 0 on success; -1 on failure (and prints an error message) */
extern int32_t release_yices_lock(yices_lock_t* lock);

extern void destroy_yices_lock(yices_lock_t* lock);


#endif

#endif /* __YICES_LOCKS_H */
