#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <pthread.h>

void launch_threads(int nthreads, const char* file_format, yices_thread_main_t thread_main){
  int retcode, thread;
  char  buff[1024];
  FILE**  outfp = (FILE**)calloc(nthreads, sizeof(FILE*));
  pthread_t* tids = (pthread_t*)calloc(nthreads, sizeof(pthread_t));
  if((outfp == NULL) || (tids == NULL)){
    fprintf(stderr, "Couldn't alloc memory for %d threads\n", nthreads);
    return 0;
  }
  printf("%d threads\n", nthreads);

  for(thread = 0; thread < nthreads; thread++){
    snprintf(buff, 1024, file_format, thread);
    printf("Logging thread %d to %s\n", thread, buff);
    outfp[thread] = fopen(buff, "w");
    if(outfp[thread] == NULL){
      fprintf(stderr, "fopen failed: %s\n", strerror(errno));
      exit(EXIT_FAILURE);
    }
    retcode =  pthread_create(&tids[thread], NULL, thread_main, outfp[thread]);
    if(retcode){
      fprintf(stderr, "pthread_create failed: %s\n", strerror(retcode));
      exit(EXIT_FAILURE);
    }
  }

  printf("threads away\n\n");


  for(thread = 0; thread < nthreads; thread++){
    retcode = pthread_join(tids[thread], NULL);
    if(retcode){
      fprintf(stderr, "pthread_join failed: %s\n", strerror(retcode));
      exit(EXIT_FAILURE);
    }
    fclose(outfp[thread]);
  }

  free(outfp);
  free(tids);

}



yices_thread_result_t yices_thread_exit(void){
  return NULL;
}
