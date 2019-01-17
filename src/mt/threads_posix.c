#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>

void launch_threads(int32_t nthreads, void* extras, size_t extra_sz, const char* test, yices_thread_main_t thread_main, bool verbose){
  int32_t retcode, thread;
  char  buff[1024];

  thread_data_t* tdata = (thread_data_t*)calloc(nthreads, sizeof(thread_data_t)); 

  pthread_t* tids = (pthread_t*)calloc(nthreads, sizeof(pthread_t));
  if((tdata == NULL) || (tids == NULL)){
    fprintf(stderr, "Couldn't alloc memory for %d threads\n", nthreads);
    exit(EXIT_FAILURE);
  }

  if(verbose){
    printf("%d threads\n", nthreads);
  }

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
    if(tdata[thread].output == NULL){
      fprintf(stderr, "fopen failed: %s\n", strerror(errno));
      exit(EXIT_FAILURE);
    }

    retcode =  pthread_create(&tids[thread], NULL, thread_main, &tdata[thread]);
    if(retcode){
      fprintf(stderr, "pthread_create failed: %s\n", strerror(retcode));
      exit(EXIT_FAILURE);
    }
  }

  if(verbose){
    printf("threads away\n\n");
  }


  for(thread = 0; thread < nthreads; thread++){
    retcode = pthread_join(tids[thread], NULL);
    if(retcode){
      fprintf(stderr, "pthread_join failed: %s\n", strerror(retcode));
      exit(EXIT_FAILURE);
    }
    fclose(tdata[thread].output);
  }

  free(tdata);
  free(tids);

}



yices_thread_result_t yices_thread_exit(void){
  return NULL;
}
