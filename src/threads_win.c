// compile with: /MT
#include <windows.h>
#include <process.h>

#include <stdio.h>
#include <errno.h>
#include <string.h>

/* not tested or compiled yet */

void launch_threads(int nthreads, char* file_format, yices_thread_main_t thread_main){
  int retcode, thread;
  char  buff[1024];
  FILE**  outfp = (FILE**)calloc(nthreads, sizeof(FILE*));
  HANDLE* handles = (HANDLE*)calloc(nthreads, sizeof(HANDLE));
  unsigned* tids = (unsigned*)calloc(nthreads, sizeof(unsigned));
  if((outfp == NULL) || (tids == NULL) || (handles == NULL)){
    fprintf(stderr, "Couldn't alloc memory for %d threads\n", nthreads);
    exit(EXIT_FAILURE);
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
    handles[thread]  =  (HANDLE)_beginthreadex( NULL, 0, &thread_main, outfp[thread], 0, &tids[thread]);
    if(handles[thread] == 0){
      fprintf(stderr, "_beginthreadex: %s\n", strerror(errno));
      exit(EXIT_FAILURE);
    }
  }
  
  printf("threads away\n\n");
  
  
  for(thread = 0; thread < nthreads; thread++){

    WaitForSingleObject( handles[thread], INFINITE );
    CloseHandle( handles[thread] );
    fclose(outfp[thread]);
  }
  
  free(outfp);
  free(handles);
  free(tids);

}

yices_thread_result_t yices_thread_exit(void){
  _endthreadex( 0 );
  return 0;
}
