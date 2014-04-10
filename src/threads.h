#ifndef __THREADS_H
#define __THREADS_H

/* the thread main */
#ifdef MINGW
typedef unsigned yices_thread_result_t;
typedef yices_thread_result_t ( __stdcall *yices_thread_main_t)(void *);
#else
typedef void* yices_thread_result_t;
typedef yices_thread_result_t (*yices_thread_main_t)(void *);
#endif

 
/* launches nthreads computing thread_main and logging to a file based on file_format filled with the thread index */
extern void launch_threads(int nthreads, const char* file_format, yices_thread_main_t thread_main);

/* lets the user know what is needed */
extern void mt_test_usage(int argc, char* argv[]);


extern yices_thread_result_t yices_thread_exit(void);

#endif /* __THREADS_H */

