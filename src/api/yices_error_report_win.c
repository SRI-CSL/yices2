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

#include <errhandlingapi.h>
#include <processthreadsapi.h>
 
#include <assert.h>
#include <stdbool.h>
#include <string.h>

#include "yices_types.h"
#include "yices_exit_codes.h"
#include "utils/memalloc.h"


/*
 * Thread Local Errors (global data)
 */
static bool   yices_tls_initialized = false;
static DWORD yices_tls_error_index;


// Initializes the thread local error report object.  It is assumed
// that the global TLS system has already been initialized. It returns
// the initialized local object.
static error_report_t* thread_local_init_yices_error_report(void){
  error_report_t* tl_yices_error;
  
  assert(yices_tls_initialized);


  tl_yices_error = TlsGetValue(yices_tls_error_index);

  if(tl_yices_error == 0){

    // This is a consequence of our assumption that the global TLS
    // system has already been initialized.  Since if
    // yices_tls_error_index is a valid index, then the call should not fail.
    assert(GetLastError() == 0);
    // This will leak unless we enforce that exiting threads clean up
    // there own error_report_t. 
    tl_yices_error = safe_malloc(sizeof(error_report_t));
    memset(tl_yices_error, 0, sizeof(error_report_t));
    tl_yices_error->code = YICES_NO_ERROR;
    TlsSetValue(yices_tls_error_index, tl_yices_error);
  }
  return tl_yices_error;
}

static void thread_local_free_yices_error_report(void){
  error_report_t* tl_yices_error = TlsGetValue(yices_tls_error_index);
  safe_free(tl_yices_error);
  TlsSetValue(yices_tls_error_index, NULL);
}


void init_yices_error(void){
  /* 
   * This is called explicitly in yices_init, so if there is a race
   * condition here, then there is a race condition b/w yices_init and
   * a call to the API.  Which is not OUR problem. Just incorrect
   * usage of the API.
   */
  if (!yices_tls_initialized) {
    yices_tls_error_index = TlsAlloc();
    if (yices_tls_error_index == TLS_OUT_OF_INDEXES){
      // this is a bit drastic. discuss.
      exit(YICES_EXIT_TLS_ERROR);
    }
    yices_tls_initialized = true;
    thread_local_init_yices_error_report();
  }
}

void free_yices_error(void){
  if (yices_tls_initialized) {
    thread_local_free_yices_error_report();
    // could check the BOOL value, but what would we do if it failed?
    (void)TlsFree(yices_tls_error_index);
    yices_tls_initialized = false;
  }
}


error_report_t* get_yices_error(void){
  return thread_local_init_yices_error_report();
}


