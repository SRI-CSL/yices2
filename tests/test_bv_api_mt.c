/*
 * Use the API to solve two examples
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <yices.h>

#include "threads.h"


/*
 * Utility to print a status
 */
#define NUM_STATUS (STATUS_ERROR+1)

static const char * const status2string[NUM_STATUS] = {
  "idle",
  "searching",
  "unknown",
  "sat",
  "unsat",
  "interrupted",
  "error",
};

static void print_status(FILE* output, smt_status_t status) {
  if (status >= STATUS_IDLE && status <= STATUS_ERROR) {
    fprintf(output, "%s", status2string[status]);
  } else {
    fprintf(output, "Invalid context status\n");
    fprintf(output, "Please report this bug to yices-bugs@csl.sri.com\n");
    fflush(output);
    fprintf(stderr, "Invalid context status\n");
    fprintf(stderr, "Please report this bug to yices-bugs@csl.sri.com\n");
    exit(1);
  }
}


/*
 * Utility: print a bitvector constant
 * - n = number of bits
 * - val = array of bits (each is either 0 or 1)
 */
static void print_bvconst(FILE* output, uint32_t n, int32_t val[]) {
  fprintf(output, "0b");
  while (n > 0) {
    n --;
    assert(val[n] == 0 || val[n] == 1);
    fprintf(output, "%d", (int) val[n]);
  }
}


/*
 * Example 1: satisfiable (cf. bv_test.ys)
 */
static void example1(FILE* output, int32_t id, context_t *ctx) {
  type_t bv4;
  term_t i4, i5, x;
  term_t b;
  term_t assertion[4];
  int32_t code;
  smt_status_t status;
  model_t *model;
  int32_t buffer[4]; // to collect the values in mdoel


  fprintf(output,
	  "\n"
	  "==========================\n"
	  "    Example 1 Thread %d   \n"
	  " based on bv_test.ys      \n"
	  "==========================\n"
	  "\n", (int)id);
  
  /*
   * Create the type (bitvector 4)
   */
  bv4 = yices_bv_type(4);
  
  /*
   * Build three variables i4, i5, and x of type bv4
   */
  i4 = yices_new_uninterpreted_term(bv4);
  i5 = yices_new_uninterpreted_term(bv4);
  x = yices_new_uninterpreted_term(bv4);
  
  /*
   * first assertion: (bv-lt x 0b0011)
   */
  assertion[0] = yices_bvlt_atom(x, yices_bvconst_from_string("0011"));
  
  /*
   * second assertion: (bvlt i4 0b0011)
   */
  b = yices_bvconst_uint32(4, 3);   // b is 0b0011 again
  assertion[1] = yices_bvlt_atom(i4, b);
  
  /*
   * third assertion: (= i5 (bv-add i4 0b0001))
   */
  assertion[2] = yices_eq(i5, yices_bvadd(i4, yices_bvconst_one(4)));
  
  /*
   * fourth assertion: (not (bv-lt i5 0b0011))
   */
  assertion[3] = yices_not(yices_bvlt_atom(i5, b));
  
  
  /*
   * assert the whole thing in ctx
   */
  code = yices_assert_formulas(ctx, 4, assertion);
  if (code < 0) {
    fprintf(output, "Assertion failed with error code = %d\n", (int) yices_get_error_code());
    fprintf(stderr, "Assertion failed with error code = %d\n", (int) yices_get_error_code());
    goto done;
  }
  
  
  /*
   * Optional: chek the context status after the assertions
   */
  status = yices_context_status(ctx);
  fprintf(output, "Status after assertions: ");
  print_status(output, status);
  fprintf(output, "\n");
  
  if (status == STATUS_IDLE) {
    /*
     * Check satisfiability
     */
    fprintf(output, "Checking satisfiability ...\n");
    status = yices_check_context(ctx, NULL);
    fprintf(output, "answer = ");
    print_status(output, status);
    fprintf(output, "\n");
    
    switch (status) {
    case STATUS_SAT:
    case STATUS_UNKNOWN:
      /*
       * Build the model
       */
      model = yices_get_model(ctx, 1); // keep_subst true
      assert(model != NULL);

      /*
       * Check the values of x, i1, i2 in the model
       */
      code = yices_eval_bv_term_in_model(model, x, buffer);
      if (code < 0) {
	fprintf(output, "Eval failed for 'x' with error code = %d\n", (int) yices_get_error_code());
	fprintf(stderr, "Eval failed for 'x' with error code = %d\n", (int) yices_get_error_code());
      } else {
	fprintf(output, "x is ");
	print_bvconst(output, 4, buffer);
	fprintf(output, "\n");
      }

      code = yices_eval_bv_term_in_model(model, i4, buffer);
      if (code < 0) {
	fprintf(output, "Eval failed for 'i4' with error code = %d\n", (int) yices_get_error_code());
 	fprintf(stderr, "Eval failed for 'i4' with error code = %d\n", (int) yices_get_error_code());
      } else {
	fprintf(output, "i4 is ");
	print_bvconst(output, 4, buffer);
	fprintf(output, "\n");
      }

      code = yices_eval_bv_term_in_model(model, i5, buffer);
      if (code < 0) {
	fprintf(output, "Eval failed for 'i5' with error code = %d\n", (int) yices_get_error_code());
	fprintf(stderr, "Eval failed for 'i5' with error code = %d\n", (int) yices_get_error_code());
      } else {
	fprintf(output, "i5 is ");
	print_bvconst(output, 4, buffer);
	fprintf(output, "\n");
      }

      /*
       * You can also evaluate more complicated terms
       */
      b = yices_bvxor(i5, yices_bvxor(i4, b));
      code = yices_eval_bv_term_in_model(model, b, buffer);
      if (code < 0) {
	fprintf(output, "Eval failed for 'i5 xor (i4 xor 0b0011)' with error code = %d\n", (int) yices_get_error_code());
	fprintf(stderr, "Eval failed for 'i5 xor (i4 xor 0b0011)' with error code = %d\n", (int) yices_get_error_code());
      } else {
	fprintf(output, "i5 xor (i4 xor 0b0011) is ");
	print_bvconst(output, 4, buffer);
	fprintf(output, "\n");
      }

      /*
       * Clean up
       */
      yices_free_model(model);
      break;

    default:
      fprintf(output, "No model\n");
      break;
    }
  }

 done:
  /*
   * Remove the assertions so that we can reuse the context
   */
  yices_reset_context(ctx);
}





/*
 * Example 2: based on junghee_lim2.ys
 */

// auxiliary function: build (and a b)
static term_t and2(term_t a, term_t b) {
  term_t aux[2];

  aux[0] = a;
  aux[1] = b;
  return yices_and(2, aux);
}

static void example2(FILE* output,  int32_t id, context_t *ctx) {
  type_t bv32;
  term_t eip1, esp1, esp0;
  term_t tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp22, tmp54, tmp55;
  term_t tmp56, tmp57, tmp58, tmp59, tmp65, tmp66;
  int32_t code;
  smt_status_t status;


  fprintf(output, "\n"
	 "=================================\n"
	 "       Example 2  Thread %d      \n"
         " based on junghee_lim2.ys        \n"
	 "=================================\n"
	  "\n", id);


  bv32 = yices_bv_type(32);
  eip1 = yices_new_uninterpreted_term(bv32);
  tmp0 = yices_bvconst_uint32(32, 7);
  tmp22 = yices_bvconst_uint32(32, 0);
  tmp1 = yices_eq(eip1, tmp0);

  esp1 = yices_new_uninterpreted_term(bv32);
  esp0 = yices_new_uninterpreted_term(bv32);
  tmp2 = yices_bvconst_uint32(32, 4294967292u);
  tmp3 = yices_bvadd(esp0, tmp2);
  tmp4 = yices_eq(esp1, tmp3);

  tmp5 = and2(tmp1, tmp4);

  tmp54 = yices_bvmul(esp1, yices_bvconst_uint32(32, 473028019u));
  tmp55 = yices_bvmul(tmp0, yices_bvconst_uint32(32, 956831788u));
  tmp56 = yices_bvsub(tmp54, tmp55);
  tmp57 = yices_bvmul(esp0, yices_bvconst_uint32(32, 473028019u));
  tmp58 = yices_bvsub(tmp56, tmp57);
  tmp59 = yices_eq(tmp22, tmp58);

  tmp65 = yices_not(tmp59);
  tmp66 = and2(tmp5, tmp65);

  /*
   * Assert tmp66 then check satisfiability
   */
  code = yices_assert_formula(ctx, tmp66);
  if (code < 0) {
    fprintf(output, "Assertion failed with error code = %d\n", (int) yices_get_error_code());
    fprintf(stderr, "Assertion failed with error code = %d\n", (int) yices_get_error_code());
    goto done;
  }

  fprintf(output, "Checking satisfiability ...\n");
  status = yices_check_context(ctx, NULL);
  fprintf(output, "answer = ");
  print_status(output, status);
  fprintf(output, "\n");

  // the expected answer is unsat
  assert(status == STATUS_UNSAT);

 done:
  yices_reset_context(ctx);
}

typedef void (* example_t)(FILE*,  int32_t, context_t *);

typedef struct thread_extras {
  context_t *context;
  example_t example;
} thread_extras_t;


yices_thread_result_t YICES_THREAD_ATTR test_thread(void* arg){
  thread_data_t* tdata = (thread_data_t *)arg;
  int32_t id  = tdata->id;
  FILE* output = tdata->output;
  thread_extras_t* extra = (thread_extras_t*)(tdata->extra); 

  if(extra != NULL){
    extra->example(output, id, extra->context);
  }

  return yices_thread_exit();
}


static int32_t spawn_examples(int32_t nthreads, context_t **ctx) {
  thread_extras_t* extras;
  int32_t thread;

  assert(nthreads > 0);

  extras = (thread_extras_t*)calloc(nthreads, sizeof(thread_extras_t));
  
  for(thread = 0; thread < nthreads; thread++){
    extras[thread].context = ctx[thread];
    extras[thread].example =  (thread % 2 == 0) ? example1 : example2;
  }
  
  launch_threads(nthreads, (void *)extras, sizeof(thread_extras_t), "test_bv_api_mt", test_thread, true);

  free(extras);

  return 0;
}


int main(int argc, char *argv[]) {
  int32_t nthreads;
  int32_t thread;
  
  if (argc == 2) {
    nthreads = atoi(argv[1]);
  } else {
    printf("Usage: %s <number of threads>\n", argv[0]);
    exit(1);
  }
  
  fprintf(stderr, "Testing Yices %s (%s, %s)\n", yices_version,
	  yices_build_arch, yices_build_mode);
  
  yices_init();
  
  
  if(nthreads == 0){
    context_t* ctx[1];
    ctx[0] = yices_new_context();
    
    example1(stdout, 0, ctx[0]);
    example2(stdout, 0, ctx[0]);
    
    yices_free_context(ctx[0]);

  } else {

    context_t** ctx = (context_t**)calloc(nthreads, sizeof(context_t*));

    for(thread = 0; thread < nthreads; thread++){
      ctx[thread] =  yices_new_context();
    }

    spawn_examples(nthreads, ctx);

    for(thread = 0; thread < nthreads; thread++){
      yices_free_context(ctx[thread]);
    }
    free(ctx);
  }
  
  
  yices_exit();
  
  return 0;
}
