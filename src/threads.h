#ifndef __THREADS_H
#define __THREADS_H

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


/* launches nthreads computing thread_main and logging to a file based on test and the thread index;
   on *nix the file is in /tmp, on windows it is in the cwd
*/
extern void launch_threads(int nthreads, const char* test, yices_thread_main_t thread_main);

/* lets the user know what is needed */
extern void mt_test_usage(int argc, char* argv[]);


extern yices_thread_result_t yices_thread_exit(void);

#endif /* __THREADS_H */

