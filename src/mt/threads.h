#ifndef __THREADS_H
#define __THREADS_H
#include <stdint.h>
#include <stdbool.h>

/* the thread main */
#ifdef MINGW
#define YICES_THREAD_ATTR  __stdcall
typedef unsigned yices_thread_result_t;
typedef yices_thread_result_t ( YICES_THREAD_ATTR *yices_thread_main_t)(void *);
#else
#define YICES_THREAD_ATTR  
typedef void* yices_thread_result_t;
typedef yices_thread_result_t ( YICES_THREAD_ATTR  *yices_thread_main_t)(void *);
#endif


typedef struct thread_data {
  int32_t id;
  FILE* output;
  void* extra;
} thread_data_t;



/* launches nthreads computing thread_main and logging to a file based on test and the thread index;
   on *nix the file is in /tmp, on windows it is in the cwd;

   extras if not NULL should be of the same length as nthread, and each element is put in the appropriate void* extra
   slot in the thread data.

*/
extern void launch_threads(int32_t nthreads, void* extras, size_t extra_sz, const char* test, yices_thread_main_t thread_main, bool verbose);

/* lets the user know what is needed */
extern void mt_test_usage(int32_t argc, char* argv[]);


extern yices_thread_result_t yices_thread_exit(void);


#endif /* __THREADS_H */

