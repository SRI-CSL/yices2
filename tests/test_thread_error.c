/*
 * TEST THE THREAD ERROR STUFF
 */

/*
 * Force assert to work even if compiled with debug disabled
 */
#ifdef NDEBUG
# undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

#include "yices.h"

#include "threads.h"
#include "thread_error.h"



yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  set_tl_error(4 * (tdata->id + 1));


  fprintf(output, "Done %d errno = %d.\n", tdata->id, get_tl_error());

  fprintf(stderr, "Done %d errno = %d.\n", tdata->id, get_tl_error());


  return yices_thread_exit();
}




int main(int argc, char* argv[]) {

  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = atoi(argv[1]);

    yices_init();

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else if(nthreads == 0){
      thread_data_t tdata = {0, stdout};
      test_thread(&tdata);
    } else {
      launch_threads(nthreads, "test_api3_mt", test_thread);
    }
    

    yices_exit();
  }

  return 0;
}
