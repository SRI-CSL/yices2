#include <stdio.h>

#include "threads.h"



#ifndef MINGW
#include "threads_posix.c"
#else
#include "threads_win.c"
#endif

void mt_test_usage(int32_t argc, char* argv[]){
  fprintf(stdout, "usage:\n%s <number of threads>\n", argv[0]);
  fprintf(stdout,"\tnumber of threads = 0: single threaded output to stdout\n"
          "\tnumber of threads > 0: each thread logs to a seperate file\n");
}



