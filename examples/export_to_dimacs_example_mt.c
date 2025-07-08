#include <stdio.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdlib.h>

#include "yices.h"
#include "mt/threads.h"

//gcc  -I../src/ export_to_dimacs_example_mt.c -o export_to_dimacs_mt -lyices -pthread ../build/x86_64-pc-linux-gnu-debug/obj/mt/threads.o
//valgrind --tool=helgrind ./export_to_dimacs_mt  10

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

static void show_formulas(term_t* formula, uint32_t n) {
  printf("Formulas:\n  ");
  yices_pp_term_array(stdout, n, formula, 100, 120, 2, false);
  fflush(stdout);
}

static char *status_to_string(smt_status_t status) {
  switch (status) {
  case YICES_STATUS_SAT: return "sat";
  case YICES_STATUS_UNSAT: return "unsat";
  default: return "bug";
  }
}

static void test(term_t* formula, uint32_t nformula) {
  char filename[40];
  uint32_t n;
  smt_status_t status;
  int32_t code;

  // first round: don't simplify the CNF
  for (n=1; n<=3; n++) {
    show_formulas(formula, n);
    snprintf(filename, 40, "basic%"PRIu32".cnf", n);
    code = yices_export_formulas_to_dimacs(formula, n, filename, false, &status);
    if (code < 0) {
      printf("Export to dimacs failed\n");
      yices_print_error(stdout);
    } else if (code == 0) {
      printf("No dimacs produced: formula solved %s\n", status_to_string(status));
      fflush(stdout);
    } else {
      printf("Successfully exported to file %s\n", filename);
    }
    fflush(stdout);
  }

  // second round: simplify the CNF
  for (n=1; n<=3; n++) {
    show_formulas(formula, n);
    snprintf(filename, 40, "simplified%"PRIu32".cnf", n);
    code = yices_export_formulas_to_dimacs(formula, n, filename, true, &status);
    if (code < 0) {
      printf("Export to dimacs failed\n");
      yices_print_error(stdout);
    } else if (code == 0) {
      printf("No dimacs produced: formula solved %s\n", status_to_string(status));
      fflush(stdout);
    } else {
      printf("Successfully exported to file %s\n", filename);
    }
    fflush(stdout);
  }
}

yices_thread_result_t YICES_THREAD_ATTR thread_main(void *td) {
  printf("Testing Yices %s (%s, %s)\n", yices_version, yices_build_arch, yices_build_mode);
  thread_data_t* tdata = (thread_data_t *)td;
  term_t* formula = *((term_t **)tdata->extra);

  test(formula, NUM_FORMULAS);

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
      term_t *formula = (term_t* )calloc(NUM_FORMULAS, sizeof(term_t));
      yices_init();

      build_formulas(formula, NUM_FORMULAS);

      if(nthreads == 0){
        thread_data_t tdata = {0, stdout, &formula};
        thread_main(&tdata);
      } else {
        term_t* fp[nthreads];
        //each thread gets their own pointer to the formula array
        for(int i = 0; i < nthreads; i++){
          fp[i] = formula;
        }
        launch_threads(nthreads, fp, sizeof(term_t*), "thread_main", thread_main, true);
      }

      free(formula);
      yices_exit();

    }
  }
  return 0;
}
