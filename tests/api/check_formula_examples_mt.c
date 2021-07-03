#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdlib.h>

#include "yices.h"
#include "mt/threads.h"


//gcc  -I../src/ check_formula_examples_mt.c -o check_formula_examples_mt -lyices -pthread ../build/x86_64-pc-linux-gnu-debug/obj/mt/threads.o
//valgrind --tool=helgrind ./check_formula_examples_mt  10

#define NUM_FORMULAS 3

static term_t new_var(type_t tau, const char *name) {
  term_t t = yices_new_uninterpreted_term(tau);
  yices_set_term_name(t, name);
  return t;
}

static void build_formulas(term_t* formula, uint32_t nformula) {
  type_t bv = yices_bv_type(20);
  term_t x = new_var(bv, "x");
  term_t y = new_var(bv, "y");
  term_t z = new_var(bv, "z");

  // three formulas
  if (nformula >= 3){
    formula[0] = yices_bveq_atom(yices_bvmul(x, y), yices_bvconst_uint32(20, 12289));
    formula[1] = yices_bveq_atom(yices_bvmul(y, z), yices_bvconst_uint32(20, 20031));
    formula[2] = yices_bveq_atom(yices_bvmul(x, z), yices_bvconst_uint32(20, 10227));
  }
}

static void show_formulas(term_t* formula, uint32_t nformula) {
  printf("Formulas:\n  ");
  yices_pp_term_array(stdout, nformula, formula, 100, 120, 2, false);
  fflush(stdout);
}

static void test(term_t* formula, uint32_t nformula, const char *delegate) {
  model_t *model;
  smt_status_t status;
  uint32_t n;


  if (delegate != NULL) {
    printf("\n=== Testing %s ===\n", delegate);
  } else {
    printf("\n=== No delegate ===\n");
  }
  if (! yices_has_delegate(delegate)) {
    printf("Not supported\n");
  } else {
    for (n=1; n<=nformula; n++) {
      show_formulas(formula, n);
      status = yices_check_formulas(formula, n, "QF_BV", &model, delegate);
      switch (status) {
      case STATUS_UNSAT:
        printf("unsat\n");
        break;

      case STATUS_SAT:
        printf("sat\n");
        printf("model:\n  ");
        yices_pp_model(stdout, model, 100, 120, 2);
        yices_free_model(model);
        break;

      default:
        printf("error\n");
        yices_print_error(stdout);
        printf("\n");
      }
      printf("\n");
    }

  }
  fflush(stdout);
}

yices_thread_result_t YICES_THREAD_ATTR thread_main(void *td) {
  
  yices_per_thread_init();

  term_t *formula = (term_t* )calloc(NUM_FORMULAS, sizeof(term_t));

  build_formulas(formula, NUM_FORMULAS);

  printf("Testing Yices %s (%s, %s)\n", yices_version, yices_build_arch, yices_build_mode);

  //thread_data_t* tdata = (thread_data_t *)td;
  //term_t* formula = *((term_t **)tdata->extra);


  show_formulas(formula, NUM_FORMULAS);

  test(formula, NUM_FORMULAS, "cadical");
  test(formula, NUM_FORMULAS, "cryptominisat");
  test(formula, NUM_FORMULAS, "y2sat");
  test(formula, NUM_FORMULAS, NULL);

  free(formula);

  yices_per_thread_exit();

  return yices_thread_exit();
}

int main(int argc, char* argv[]){
  int32_t nthreads;
  if(argc != 2){
    nthreads = 2;
    //mt_test_usage(argc, argv);
  } else {
    nthreads = strtol(argv[1], NULL, 10);
  }

  if(nthreads < 0){
    fprintf(stderr, "thread number must be positive!\n");
    exit(EXIT_FAILURE);
  } else {

    yices_global_init();

    
    
    if(nthreads == 0){
      thread_data_t tdata = {0, stdout, NULL};
      thread_main(&tdata);
    } else {
      //term_t* fp[nthreads];
      //each thread gets their own pointer to the formula array
      //for(int i = 0; i < nthreads; i++){
      // fp[i] = formula;
      //}
      launch_threads(nthreads, NULL, sizeof(term_t*), "thread_main", thread_main, true);
    }
    
    //free(formula);
    yices_global_exit();

   
  }
  
  return 0;
}
