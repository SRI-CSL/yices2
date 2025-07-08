#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>

#include "yices.h"

#define DEBUG false

/* the dimension of the board */
#define DIMENSION  9

type_t integer_t = NULL_TYPE;

typedef term_t  board_t[DIMENSION][DIMENSION];

typedef char*  vars_t[DIMENSION][DIMENSION];

typedef int32_t game_t[DIMENSION][DIMENSION];


/* hack for debugging */
static const vars_t vars =
  {

   {"x11", "x12",  "x13", "x14", "x15",  "x16", "x17", "x18", "x19" },
   {"x21", "x22",  "x23", "x24", "x25",  "x26", "x27", "x28", "x29" },
   {"x31", "x32",  "x33", "x34", "x35",  "x36", "x37", "x38", "x39" },

   {"x41", "x42",  "x43", "x44", "x45",  "x46", "x47", "x48", "x49" },
   {"x51", "x52",  "x53", "x54", "x55",  "x56", "x57", "x58", "x59" },
   {"x61", "x62",  "x63", "x64", "x65",  "x66", "x67", "x68", "x69" },

   {"x71", "x72",  "x73", "x74", "x75",  "x76", "x77", "x78", "x79" },
   {"x81", "x82",  "x83", "x84", "x85",  "x86", "x87", "x88", "x89" },
   {"x91", "x92",  "x93", "x94", "x95",  "x96", "x97", "x98", "x99" },


  };


static board_t b;

/* initialize the board */
static bool init_board(void){
  int32_t i;
  int32_t j;

  if(integer_t == NULL_TYPE){
    integer_t = yices_int_type();
    assert(integer_t != NULL_TYPE);
  }

  for(i = 0; i < DIMENSION; i++)
    for(j = 0; j < DIMENSION; j++){
      term_t slot = yices_new_uninterpreted_term(integer_t);

      yices_set_term_name(slot, vars[i][j]);

      if(slot == NULL_TERM){
        return false;
      }
      b[i][j] = slot;
    }

  return true;

}

/* SLOW a yices term asserting x is between 1 and 9 (using < )

real	0m17.724s
user	0m17.708s
sys	    0m0.004s

term_t between_1_and_9(term_t x){
  return yices_and2(yices_arith_leq_atom(yices_int32(1), x), yices_arith_leq_atom(x, yices_int32(9)));
}
 */

/* FAST a yices term asserting x is between 1 and 9 (using logic)

real	0m0.228s
user	0m0.204s
sys	    0m0.012s

 */
term_t between_1_and_9(term_t x){
  int32_t i;
  term_t choices[9];
  for(i = 0; i < DIMENSION; i++){
    choices[i] = yices_arith_eq_atom(yices_int32(i + 1), x);
  }
  return yices_or(9, choices);
}



/* A yices term asserting that all 9 terms are distinct. Not the most elegant but ... */
term_t distinct(term_t t1, term_t t2, term_t t3,
                term_t t4, term_t t5, term_t t6,
                term_t t7, term_t t8, term_t t9){
  term_t dset[9];

  dset[0] = t1;
  dset[1] = t2;
  dset[2] = t3;
  dset[3] = t4;
  dset[4] = t5;
  dset[5] = t6;
  dset[6] = t7;
  dset[7] = t8;
  dset[8] = t9;

  return yices_distinct(9, dset);
}

bool assert_sudoku_rules(context_t *ctx, board_t b){
  int32_t yices_errcode;
  int32_t i;
  int32_t j;

  for(i = 0; i < DIMENSION; i++)
    for(j = 0; j < DIMENSION; j++){
      term_t b_1_9 = between_1_and_9(b[i][j]);
      if(DEBUG){
        yices_pp_term(stdout, b_1_9, 1024, 0, 0);
      }
      yices_errcode = yices_assert_formula(ctx, b_1_9);
      if(yices_errcode != NO_ERROR){
        fprintf(stderr, "assert_sudoku_rules 'between_1_and_9' failed: %s\n", yices_error_string());
        return false;
      }
    }

  for(i = 0; i < DIMENSION; i++){
    /* row i is distinct */
    yices_assert_formula(ctx, distinct(b[i][0], b[i][1], b[i][2],
                                       b[i][3], b[i][4], b[i][5],
                                       b[i][6], b[i][7], b[i][8]));
    /* column i is distinct */
    yices_assert_formula(ctx, distinct(b[0][i], b[1][i], b[2][i],
                                       b[3][i], b[4][i], b[5][i],
                                       b[6][i], b[7][i], b[8][i]));

  }

  /* each 3x3 square is distinct */
  for(i = 0; i < DIMENSION / 3; i++){
    for(j = 0; j < DIMENSION / 3; j++){
      yices_assert_formula(ctx, distinct(b[(3 * i) + 0][(3 * j)], b[(3 * i) + 0][(3 * j) + 1], b[(3 * i) + 0][(3 * j) + 2],
                                         b[(3 * i) + 1][(3 * j)], b[(3 * i) + 1][(3 * j) + 1], b[(3 * i) + 1][(3 * j) + 2],
                                         b[(3 * i) + 2][(3 * j)], b[(3 * i) + 2][(3 * j) + 1], b[(3 * i) + 2][(3 * j) + 2]));
    }
  }
 return true;
}

bool pose_problem(context_t *ctx, board_t b, const game_t g){
  int32_t yices_errcode;
  int32_t i;
  int32_t j;

  for(i = 0; i < DIMENSION; i++){
    for(j = 0; j < DIMENSION; j++){
      int32_t value = g[i][j];
      assert((value >= 0) && (value <= 9));
      if(value > 0){
        yices_errcode = yices_assert_formula(ctx, yices_arith_eq_atom(yices_int32(value), b[i][j]));
        if(yices_errcode != NO_ERROR){
          fprintf(stderr, "pose_problem for row %d column %d failed: %s\n", i, j, yices_error_string());
          return false;
        }
      }
    }
  }

  return true;
}


bool get_solution(context_t *ctx, board_t b,  game_t solution){
  int32_t yices_errcode;
  int32_t i;
  int32_t j;
  int32_t value;
  model_t *model = yices_get_model(ctx, 1);

  if (model == NULL){
        fprintf(stderr, "get_solution failed (yices_get_model returned NULL): %s\n", yices_error_string());
        return false;
  }

  if(DEBUG){
    yices_pp_model(stdout, model, 1024, 0, 0);
  }

  for(i = 0; i < DIMENSION; i++){
    for(j = 0; j < DIMENSION; j++){

      yices_errcode = yices_get_int32_value(model, b[i][j], &value);

      if (yices_errcode != NO_ERROR){
        fprintf(stderr, "get_solution for row %d column %d failed: %s\n", i, j, yices_error_string());
        return false;
      }

      solution[i][j] = value;
      if(DEBUG){ fprintf(stderr, "solution[%d][%d] = %d\n", i, j, value); }

    }
  }

  yices_free_model(model);

  return true;
}

bool check_solution(const game_t game, const game_t solution){
  int32_t i;
  int32_t j;
  int32_t answer;
  int32_t required;

  for(i = 0; i < DIMENSION; i++){
    for(j = 0; j < DIMENSION; j++){
      answer = solution[i][j];
      if (answer <= 0){ return false; }
      if (answer > 9){ return false; }
      required = game[i][j];
      if(required > 0 && required != answer){ return false; }
    }
  }

  return true;
}


const game_t test_game_1 =
  {

   {0, 0, 2,  0, 0, 0,  7, 6, 8 },
   {4, 0, 7,  0, 0, 0,  5, 0, 0 },
   {0, 0, 0,  0, 0, 0,  0, 0, 0 },

   {0, 5, 0,  0, 1, 0,  0, 0, 0 },
   {0, 2, 8,  0, 0, 0,  4, 0, 0 },
   {3, 0, 0,  0, 4, 0,  0, 7, 0 },

   {0, 0, 0,  3, 0, 1,  0, 0, 0 },
   {0, 0, 9,  0, 0, 0,  8, 0, 5 },
   {6, 7, 1,  0, 0, 0,  2, 0, 0 },

  };


void print_solution(FILE* fp, game_t solution){
  int32_t i;
  int32_t j;

  for(i = 0; i < DIMENSION; i++){
    for(j = 0; j < DIMENSION; j++){
      if(j > 0 && (j % 3 == 0)){
        putchar(' ');
      }
      if(i > 0 && i % 3 == 0 && j == 0){
        putchar('\n');
      }
      if( j % 9 == 0){
        putchar('\n');
      }
      putchar(solution[i][j] + 48);
      putchar(' ');
    }
  }
  putchar('\n');
}

int main(int argc, char* argv[]) {

  ctx_config_t *config;

  yices_init();

  if(!init_board()){
    fprintf(stderr, "Initializing board failed: %s\n", yices_error_string());
  }

  config = yices_new_config();

  yices_default_config_for_logic(config, "QF_LRA");


  {
    context_t *ctx;
    smt_status_t status;
    game_t solution;

    ctx = yices_new_context(config);
    yices_free_config(config);


    if(!assert_sudoku_rules(ctx, b)){
      fprintf(stderr, "Asserting Sudoku rules failed: %s\n", yices_error_string());
    }

    if(!pose_problem(ctx, b, test_game_1)){
      fprintf(stderr, "Asserting the initial conditions failed: %s\n", yices_error_string());
    }

    status = yices_check_context(ctx, NULL);

    if(status == YICES_STATUS_SAT){

      if(get_solution(ctx, b,  solution)){

        print_solution(stdout, solution);

        fprintf(stdout, "\nWhich is a solution: %d\n", check_solution(test_game_1,solution));

      }

    } else {


    }


    yices_free_context(ctx);

  }


  fprintf(stdout, "OK\n");

  yices_exit();

  return 0;
}
