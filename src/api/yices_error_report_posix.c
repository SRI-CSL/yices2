/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
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
    __yices_error.code = YICES_NO_ERROR;
  }
}


error_report_t* get_yices_error(void){
  init_yices_error();
  return &__yices_error;
}

void free_yices_error(void){
  // nothing to be done
}
