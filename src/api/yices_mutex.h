/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
