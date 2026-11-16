/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
