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


// Processthreadsapi.h
#include <windows.h> 

 
#include <stdbool.h>
#include <string.h>

#include "yices.h"

/*
 * Thread Local Errors (global data)
 */
static bool   __yices_tls_initialized = false;
static DWORD  __yices_tls_error_index;


// Initializes the thread local error report object.  It is assumed
// that the global TLS system has already been initialized. It returns
// the initialized local object.
static inline  error_report_t* thread_local_init_yices_error_report(void){
  error_report_t* tl_yices_error;
  
  assert(__yices_tls_initialized);


  tl_yices_error = TlsGetValue(__yices_tls_error_index);

  if(tl_yices_error == 0){

    // This is a consequence of our assumption that the global TLS
    // system has already been initialized.  Since if
    // __yices_tls_error_index is a valid index, then the call should not fail.
    assert(GetLastError() == ERROR_SUCCESS);
    // This will leak unless we enforce that exiting threads clean up
    // there own error_report_t. Or we implement a DllMain here that does it for us.
    // BD?
    tl_yices_error = safe_malloc(sizeof(error_report_t));
    memset(&tl_yices_error, 0, sizeof(error_report_t));
    tl_yices_error.code = NO_ERROR;
  }
  return tl_yices_error;
}

static inline  void thread_local_free_yices_error_report(void){
  error_report_t* tl_yices_error = TlsGetValue(__yices_tls_error_index);
  safe_free(tl_yices_error);
  TlsStValue(__yices_tls_error_index, NULL);
}


void init_yices_error(void){
  /* 
   * This is called explicitly in yices_init, so if there is a race
   * condition here, then there is a race condition b/w yices_init and
   * a call to the API.  Which is not OUR problem. Just incorrect
   * usage of the API.
   */
  if (!__yices_tls_initialized) {
    __yices_tls_error_index = TlsAlloc();
    if (__yices_tls_error_index == TLS_OUT_OF_INDEXES){
      // this is a bit drastic. discuss.
      exit("Thread Local Storage Initialization Failed");
    }
    __yices_tls_initialized = true;
    thread_local_init_yices_error_report();
  }
}

void free_yices_error(void){
  if (__yices_tls_initialized) {
    // could check the BOOL value, but what would we do if it failed?
    (void)TlsFree();
    __yices_tls_initialized = false;
  }
}


error_report_t* get_yices_error(void){
  return thread_local_init_yices_error_report();
}


/*
 * The code below is to illustrate how we could prevent TLS leaking.
 * We should discuss before we enable it.
 */


bool  __dllmain_enabled = true;

// DllMain() is the entry-point function for this DLL. 
 
BOOL WINAPI DllMain(HINSTANCE hinstDLL, // DLL module handle
    DWORD fdwReason,                    // reason called
    LPVOID lpvReserved)                 // reserved
{
  if(!__dllmain_enabled){ return true; }
  
  switch (fdwReason) { 

    // The DLL is loading due to process initialization or a call to
    // LoadLibrary.
  case DLL_PROCESS_ATTACH: 
    init_yices_error();
    break;

    // The attached process creates a new thread. 
  case DLL_THREAD_ATTACH: 
    thread_local_init_yices_error_report();
    break;
    
    // The thread of the attached process terminates.
    
  case DLL_THREAD_DETACH: 
    thread_local_free_yices_error_report();
    break;
    
    // DLL unload due to process termination or FreeLibrary. 
    
  case DLL_PROCESS_DETACH: 
    thread_local_free_yices_error_report();
    free_yices_error();
    break
      
  default: 
      break; 
  } 
 
  return TRUE; 
  UNREFERENCED_PARAMETER(hinstDLL); 
    UNREFERENCED_PARAMETER(lpvReserved); 
}


