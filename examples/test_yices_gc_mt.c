#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdlib.h>

#include "yices.h"
#include "mt/threads.h"

// build yices with enable-thread-safety and MODE=debug
// the cd into examples and do:
//gcc  -I../src/ test_yices_gc_mt.c -o test_yices_gc_mt -lyices -pthread ../build/x86_64-pc-linux-gnu-debug/obj/mt/threads.o
//valgrind --tool=helgrind ./test_yices_gc_mt  10
//valgrind ./test_yices_gc_mt  10

yices_thread_result_t YICES_THREAD_ATTR thread_main(void *td) {
  printf("Testing Yices %s (%s, %s)\n", yices_version, yices_build_arch, yices_build_mode);

  context_t *ctx = yices_new_context(NULL);
  type_t bool_type = yices_bool_type();
  term_t term = yices_new_uninterpreted_term(bool_type);
  yices_incref_type(bool_type);
  yices_incref_term(term);

  yices_decref_term(term);
  yices_decref_type(bool_type);
  yices_garbage_collect(NULL, 0, NULL, 0, false);
  yices_free_context(ctx);


  return yices_thread_exit();
}

int main(int argc, char* argv[]){
  if(argc != 2){
    mt_test_usage(argc, argv);
    return 0;
  } else {
    int32_t nthreads = strtol(argv[1], NULL, 10);

    if(nthreads < 0){
      fprintf(stderr, "thread number must be positive!\n");
      exit(EXIT_FAILURE);
    } else {
      yices_init();

      if(nthreads == 0){
        thread_data_t tdata = {0, stdout, NULL};
        thread_main(&tdata);
      } else {
        launch_threads(nthreads, NULL, 0, "thread_main", thread_main, true);
      }

      yices_exit();

    }
  }
  return 0;
}
