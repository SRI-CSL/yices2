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


void test_tl_error(thread_data_t* tdata, FILE* output){

  #ifdef HAS_TLS

  int32_t count, errno, timewaste, sum;

  for(count = 1; count < 1000; count++){
    errno =  count * (tdata->id + 1);
    set_tl_error(errno);

    fprintf(output, "Done %d errno = %d.\n", tdata->id, get_tl_error());

    
    for(timewaste = 0; timewaste  < 100000; timewaste++){
      sum = timewaste + count;
    }


    if(errno != get_tl_error()){
      fprintf(stderr, "Thread %d errno = %d but get_tl_error() = %d.\n", tdata->id, errno, get_tl_error());
    }
    assert(errno == get_tl_error());
  }
  fprintf(output, "Done %d errno = %d sum = %d.\n", tdata->id, get_tl_error(), sum);


  #else

  fprintf(stderr, "No TLS support. This test could not succeed!\n");


  #endif

}

void test_yices_error(thread_data_t* tdata, FILE* output){

  #ifdef HAS_TLS

  int32_t count, timewaste, sum;

  for(count = 0; count < 1000; count++){
    set_yices_error_code((error_code_t)count);

    fprintf(output, "Done %d error_code = %d.\n", tdata->id, get_yices_error_code());

    for(timewaste = 0; timewaste  < 100000; timewaste++){
      sum = timewaste + count;
    }


    if(count != get_yices_error_code()){
      fprintf(stderr, "Thread %d error_code = %d but get_yices_error_code() = %d.\n", tdata->id, count, get_yices_error_code());
    }
    assert(count == get_yices_error_code());
  }
  fprintf(output, "Done %d error_code = %d sum = %d.\n", tdata->id, get_yices_error_code(), sum);


  #else

  fprintf(stderr, "No TLS support. This test could not succeed!\n");


  #endif

}


yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  FILE* output = tdata->output;

  fprintf(stderr, "%d starting tl test\n", tdata->id);
  test_tl_error(tdata, output);
  fprintf(stderr, "%d starting yices error test\n", tdata->id);
  test_yices_error(tdata, output);
  fprintf(stderr, "%d Done\n", tdata->id);
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
