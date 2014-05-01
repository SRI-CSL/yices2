/*
 * Yices solver for SMT benchmarks
 */

#if defined(CYGWIN) || defined(MINGW)
#ifndef __YICES_DLLSPEC__
#define __YICES_DLLSPEC__ __declspec(dllexport)
#endif
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <signal.h>
#include <inttypes.h>

#include "smt_lexer.h"
#include "smt_parser.h"
#include "smt_term_stack.h"
#include "smt_logic_codes.h"

#include "yices.h"
#include "yices_extensions.h"
#include "yices_exit_codes.h"

#include "threads.h"


/*
 * GLOBAL OBJECTS
 */
static lexer_t lexer;
static parser_t parser;
static tstack_t stack;


/*
 * Conversion of internalization code to an error message
 */
static const char * const code2error[NUM_INTERNALIZATION_ERRORS] = {
  "no error",
  "internal error",
  "type error",
  "formula contains free variables",
  "logic not supported",
  "context does not support UF",
  "context does not support arithmetic",
  "context does not support bitvectors",
  "context does not support function equalities",
  "context does not support quantifiers",
  "context does not support lambdas",
  "not an IDL formula",
  "not an RDL formula",
  "non-linear arithmetic not supported",
  "too many variables for the arithmetic solver",
  "too many atoms for the arithmetic solver",
  "arithmetic solver exception",
  "bitvector solver exception",
};




/*
 * STATISTICS DISABLED: JUST PRINT THE RESULT
 */
static void print_status(smt_status_t status) {
  if (status == STATUS_SAT) {
    printf("sat\n");
  } else if (status == STATUS_UNSAT) {
    printf("unsat\n");
  } else {
    printf("unknown\n");
  }
  fflush(stdout);
}

#if 0
static void print_results(context_t *ctx) {
  smt_status_t resu;

  resu = yices_context_status(ctx);
  print_status(resu);
}
#endif


/*
 * Print the translation code returned by assert
 */
static void print_internalization_code(int32_t code) {
  assert(-NUM_INTERNALIZATION_ERRORS < code && code <= TRIVIALLY_UNSAT);
  if (code == TRIVIALLY_UNSAT) {
    printf("unsat\n");
    //    printf("Assertions simplify to false\n\n");
  } else if (code < 0) {
    printf("unknown\n");
    code = - code;
    if (code <= BVSOLVER_EXCEPTION) {
      printf("Internalization error: %s\n\n", code2error[code]);
    } else {
      printf("%s\n\n", code2error[code]);
    }
  }
  fflush(stdout);
}



/*
 *
 * - parse input file (assumed to be in SMT-LIB format)
 */
static int32_t parse_benchmark(smt_benchmark_t *benchp, char *filename){
  int32_t code;

  if (init_smt_file_lexer(&lexer, filename) < 0) {
    perror(filename);
    return YICES_EXIT_FILE_NOT_FOUND;
  }

  /*
   * Parse and build the formula
   */
  init_smt_tstack(&stack);

  init_parser(&parser, &lexer, &stack);
  init_benchmark(benchp);
  code = parse_smt_benchmark(&parser, benchp); // code < 0 means syntax error, 0 means OK

  delete_parser(&parser);
  close_lexer(&lexer);
  delete_tstack(&stack);

  
  return code;

}

/* determine the logic code of the benchmark */
static int32_t check_logic(smt_benchmark_t *benchp){
  smt_logic_t logic;  
  /*
   * Select architecture based on the benchmark logic
   */
  if (benchp->logic_name != NULL) {
    logic = smt_logic_code(benchp->logic_name);
    if (logic != QF_BV) {
      print_internalization_code(LOGIC_NOT_SUPPORTED);
      return YICES_EXIT_ERROR;
    }
  } else {
    printf("unknown\n");
    printf("No logic specified\n");
    return YICES_EXIT_ERROR;
  }
  return YICES_EXIT_SUCCESS;
}

/*
 * 
 * - solve benchmark
 * - return an exit code (defined in yices_exit_codes.h)
 * - if the exit code is YICES_EXIT_SUCCESS, then the status is stored in *status
 */
static int process_benchmark(smt_benchmark_t *benchp, bool build_model, smt_status_t *status) {
  int32_t code;
  model_t *model = NULL;
  context_t *context = NULL;
  param_t *params = NULL;
  
  /*
   * Initialize the context and set internalization options
   * and global search options
   */
  context = yices_create_context(CTX_ARCH_BV, CTX_MODE_ONECHECK, false, false);
  params = yices_new_param_record();
  yices_set_default_params(context, params); // set parameters for QF_BV

  /*
   * Assert and internalize
   */
  code = yices_assert_formulas(context, benchp->nformulas, benchp->formulas);
  if (code < 0) {
    fprintf(stderr, "Assert formulas failed: ");
    yices_print_error(stderr);
    code = YICES_EXIT_ERROR;
    goto cleanup_context;
  }

  if (code != TRIVIALLY_UNSAT) {
    code = yices_check_context(context, params);
    if (code == STATUS_ERROR) {
      fprintf(stderr, "Check context failed: ");
      yices_print_error(stderr);
      code = YICES_EXIT_ERROR;
      goto cleanup_context;
    }
    //    print_results(context);
    *status = yices_context_status(context);;
    if (build_model && (code == STATUS_SAT || code == STATUS_UNKNOWN)) {
      model = yices_get_model(context, true);
      code = yices_pp_model(stdout, model, 100, UINT32_MAX, 0);
      if (code < 0) {
	fprintf(stderr, "\nPrint model failed: ");
	yices_print_error(stderr);
      }
      yices_free_model(model);
    }
  }

  code = YICES_EXIT_SUCCESS;

  /*
   * Cleanup and return code
   */
 cleanup_context:
  yices_free_context(context);
  yices_free_param_record(params);

  return code;
}

typedef struct thread_extras {
  smt_benchmark_t *benchp;
  bool build_model;
  int32_t code;
  smt_status_t status;
} thread_extras_t;


yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  int32_t id  = tdata->id;
  FILE* output = tdata->output;
  thread_extras_t* extra = (thread_extras_t*)(tdata->extra); 

  if(extra != NULL){
    extra->code = process_benchmark(extra->benchp, extra->build_model, &extra->status);
    fprintf(output, "Thread %d: returned %d\n", id, extra->code);
    fflush(output);
  } else {
    fprintf(output, "Thread %d: no extras, so no work done.\n", id);
    fflush(output);
  }

  return yices_thread_exit();
}

static int32_t spawn_benchmarks(int32_t nthreads, smt_benchmark_t *benchp, bool build_model) {
  thread_extras_t* extras;
  size_t extras_sz;
  int32_t thread;
  int32_t code;
  smt_status_t status;
  bool consensus;

  assert(nthreads > 0);

  extras_sz = nthreads * sizeof(thread_extras_t);
  extras = (thread_extras_t*)safe_malloc(extras_sz);
  memset(extras, 0, extras_sz);

  
  for(thread = 0; thread < nthreads; thread++){
    extras[thread].benchp = benchp;
    extras[thread].build_model =  build_model;
    extras[thread].code = YICES_EXIT_SUCCESS;
    extras[thread].status = STATUS_UNKNOWN;
  }
  
  launch_threads(nthreads, (void *)extras, sizeof(thread_extras_t), "yices_smtcomp_mt", test_thread, false);

  consensus = true;
  code = extras[0].code;
  status = extras[0].status;
  for(thread = 1; thread < nthreads; thread++){
    if (extras[thread].code != code || extras[thread].status != status) {
      consensus = false;
      break;
    }
  }

  if (consensus) {
    print_status(status);
  } else {
    printf("BUG: threads disagree\n");
    fflush(stdout);
  }
  
  safe_free(extras);

  return code;
}

int main(int argc, char *argv[]) {
  char *filename;
  int32_t nthreads;
  int code;
  smt_benchmark_t bench;
  smt_status_t status;

  filename = NULL;
  if (argc >= 3) {
    filename = argv[1];
    nthreads = atoi(argv[2]);
  } else {
    printf("Usage: %s <SMT filename> <number of threads> [build model]\n", argv[0]);
    exit(YICES_EXIT_USAGE);
  }

  yices_init();

  code = parse_benchmark(&bench, filename);
  
  if (code < 0) {
    code = YICES_EXIT_SYNTAX_ERROR;
    goto clean_up;
  }
  
  code = check_logic(&bench);
  
  if (code != YICES_EXIT_SUCCESS){
    goto clean_up_benchmark;
  }


  if(nthreads == 0){
    status = STATUS_UNKNOWN;
    code = process_benchmark(&bench, (argc==4), &status);
    if (code == YICES_EXIT_SUCCESS) {
      print_status(status);
    }
  } else {
    
    code = spawn_benchmarks(nthreads, &bench, (argc==4));

  }
  
 clean_up_benchmark:

  delete_benchmark(&bench);
  
 clean_up:
  
  yices_exit();
  
  return code;
}

