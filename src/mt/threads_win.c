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

// compile with: /MT

#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0500
#endif

#include <windows.h>
#include <process.h>

#include <stdio.h>
#include <errno.h>
#include <string.h>

/* not tested or compiled yet */

void launch_threads(int32_t nthreads, void* extras, size_t extra_sz, const char* test, yices_thread_main_t thread_main, bool verbose){
  int32_t thread;
  char  buff[1024];

  thread_data_t* tdata = (thread_data_t*)calloc(nthreads, sizeof(thread_data_t)); 

  HANDLE* handles = (HANDLE*)calloc(nthreads, sizeof(HANDLE));
  unsigned* tids = (unsigned*)calloc(nthreads, sizeof(unsigned));

  if((tdata == NULL) || (tids == NULL) || (handles == NULL)){
    fprintf(stderr, "Couldn't alloc memory for %d threads\n", nthreads);
    exit(EXIT_FAILURE);
  }
  
  if(verbose){
    printf("%d threads\n", nthreads);
  }

  for(thread = 0; thread < nthreads; thread++){
    snprintf(buff, 1024, "%s_%d.txt", test, thread);
    if(verbose){
      printf("Logging thread %d to %s\n", thread, buff);
    }
    tdata[thread].id = thread;
    if(extras != NULL){
      tdata[thread].extra = (extras + (thread * extra_sz));
    }
    tdata[thread].output = fopen(buff, "w");
    if(tdata[thread].output == NULL){
      fprintf(stderr, "fopen failed: %s\n", strerror(errno));
      exit(EXIT_FAILURE);
    }
    handles[thread]  =  (HANDLE)_beginthreadex( NULL, 0, thread_main, &tdata[thread], 0, &tids[thread]);
    if(handles[thread] == 0){
      fprintf(stderr, "_beginthreadex: %s\n", strerror(errno));
      exit(EXIT_FAILURE);
    }
  }

  if(verbose){
    printf("threads away\n\n");
  }


  for(thread = 0; thread < nthreads; thread++){

    WaitForSingleObject( handles[thread], INFINITE );
    CloseHandle( handles[thread] );
    fclose(tdata[thread].output);
  }

  free(tdata);
  free(handles);
  free(tids);

}

yices_thread_result_t yices_thread_exit(void){
  _endthreadex( 0 );
  return 0;
}
