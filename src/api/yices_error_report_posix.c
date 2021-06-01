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


#include <stdbool.h>
#include <string.h>

#include "yices.h"

#include "mt/thread_macros.h"

/*
 * Thread Local Errors
 *
 * THREAD_SAFE implies that we HAVE_TLS
 *
 */
#ifdef THREAD_SAFE
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL
#endif


/*
 * Thread Local Errors Globals
 */
static YICES_THREAD_LOCAL bool __yices_error_initialized = false;
static YICES_THREAD_LOCAL error_report_t  __yices_error;

void init_yices_error(void){
  if (!__yices_error_initialized) {
    __yices_error_initialized = true;
    memset(&__yices_error, 0, sizeof(error_report_t));
    __yices_error.code = NO_YICES_ERROR;
  }
}


error_report_t* get_yices_error(void){
  init_yices_error();
  return &__yices_error;
}

void free_yices_error(void){
  // nothing to be done
}
