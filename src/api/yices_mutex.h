/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * PROVIDE THE ABILITY TO ENFORCE MUTUAL EXCLUSION 
 */

#ifndef __YICES_MUTEX_H

#include <stdint.h>


/*
 * Attempt to obtain sole access to yice's global data structures.
 * In thread safe mode, calling this function will block all other 
 * yices API routines from accessing the global data structures.
 *
 * It is an error to call this more than once (and will cause deadlock).
 *
 * returns 0 on success; -1 on failure
 *
 */
extern int32_t yices_obtain_mutex(void);

/*
 * Release the claim to sole access to yice's global data structures.
 * 
 * The callee must have already obtained sole access via yices_obtain_mutex();
 *
 * returns 0 on success; -1 on failure
 *
 */
extern int32_t yices_release_mutex(void);


#endif  /* __YICES_MUTEX_H */
