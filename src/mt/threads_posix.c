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

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>
#include <sys/resource.h>

#include "utils/error.h"

void launch_threads(int32_t nthreads, void* extras, size_t extra_sz, const char* test, yices_thread_main_t thread_main, bool verbose){
  int32_t thread;
  char  buff[1024];

  thread_data_t* tdata = (thread_data_t*)calloc(nthreads, sizeof(thread_data_t)); 

  pthread_t* tids = (pthread_t*)calloc(nthreads, sizeof(pthread_t));
  pthread_attr_t attr;
  size_t stacksize;
  struct rlimit rlp;
  
  if((tdata == NULL) || (tids == NULL)){
    fprintf(stderr, "Couldn't alloc memory for %d threads\n", nthreads);
    exit(EXIT_FAILURE);
  }

  if(verbose){
    printf("%d threads\n", nthreads);
  }

  /* Give child threads the same stack size as the main thread. */
  if (getrlimit(RLIMIT_STACK, &rlp) == -1)
    perror_fatal("launch_threads: getrlimit");
  check_thread_api(pthread_attr_init(&attr),
		   "launch_threads: pthread_attr_init");
  check_thread_api(pthread_attr_getstacksize(&attr, &stacksize),
		   "launch_threads: pthread_attr_getstacksize");
  check_thread_api(pthread_attr_setstacksize(&attr, rlp.rlim_cur),
		   "launch_threads: pthread_attr_setstacksize");
    
  for(thread = 0; thread < nthreads; thread++){
    snprintf(buff, 1024, "/tmp/%s_%d.txt", test, thread);
    if(verbose){
      printf("Logging thread %d to %s\n", thread, buff);
    }
    tdata[thread].id = thread;
    if(extras != NULL){
      tdata[thread].extra = (extras + (thread * extra_sz));
    }
    tdata[thread].output = fopen(buff, "w");
    if(tdata[thread].output == NULL)
      perror_fatal("launch_threads: fopen");

    check_thread_api(pthread_create(&tids[thread], &attr, thread_main,
				    &tdata[thread]),
		     "launch_threads: pthread_create");
  }

  check_thread_api(pthread_attr_destroy(&attr),
		   "launch_threads: pthread_attr_destroy");
    
  
  if(verbose){
    printf("threads away\n\n");
  }


  for(thread = 0; thread < nthreads; thread++){
    check_thread_api(pthread_join(tids[thread], NULL),
		     "launch_threads: pthread_join");
    fclose(tdata[thread].output);
  }

  free(tdata);
  free(tids);

}



yices_thread_result_t yices_thread_exit(void){
  return NULL;
}
