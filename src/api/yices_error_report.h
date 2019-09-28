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


#ifndef __YICES_ERROR_REPORT_H
#define __YICES_ERROR_REPORT_H

#include "yices_types.h"

/*
 * Thread Local Errors
 */

/*
 * Thread local initialization.
 *
 * Serves two functions:
 *
 * 1. Per thread initialization of the thread local error_report_t object.
 *    Called automatically by the get_yices_error routine.
 *
 * 2. Global TLS initialization (windows only).
 *    Called in explicitly in yices_init.
 *
 */
extern void init_yices_error(void);

/*
 * Thread local clean up. Called explicitly in yices_exit.
 */
extern void free_yices_error(void);

/*
 * Returns the error report objrct (of the calling thread).
 */
extern error_report_t* get_yices_error(void);

#endif
