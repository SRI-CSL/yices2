/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

#include <stdio.h>
#include <inttypes.h>
#include <string.h>

#include "io/pretty_printer.h"

/*
 * Token to test the pretty printer
 */
#define NATOMS 12
#define NOPENS 10
#define NCLOSES 2

static pp_atomic_token_t atoms[NATOMS];
static pp_open_token_t opens[NOPENS];
static pp_close_token_t closes[NCLOSES];

/*
 * names of the atomic tokens
 */
static char *atom_strings[NATOMS] = {
  "aaa", "bbb", "ccc", "ddd", "eee", "fff",
  "g", "h", "iii", "jjj", "kkk", "lll",
};

/*
 * labels of the open tokens
 */
static char *open_labels[NOPENS] = {
  "f0::", "f1::", "f2::", "f3::", "f4::",
  "g10000", "g2000000", "g3000000000",
  "h400000000000", "h5000000000000000",
};


/*
 * Initialize all the token descriptors
 */
static void init_tokens(void) {
  uint32_t i, n;

  n = NATOMS;
  for (i=0; i<n; i++) {
    atoms[i].bsize = 0;
    atoms[i].size = strlen(atom_strings[i]);
    atoms[i].user_tag = i;
  }

  n = NOPENS;
  for (i=0; i<n; i++) {
    opens[i].bsize = 0;
    opens[i].flags = PP_TOKEN_PAR_MASK;
    opens[i].label_size = strlen(open_labels[i]);
    opens[i].formats = PP_HMT_LAYOUT;
    opens[i].indent = opens[i].label_size + 1;
    opens[i].short_indent = 1;
    opens[i].user_tag = i;
    if (i >= 5){
      opens[i].flags = PP_TOKEN_PAR_MASK|PP_TOKEN_SEP_MASK;
      opens[i].indent ++;
    }
  }

  closes[0].flags = PP_TOKEN_PAR_MASK;
  closes[0].user_tag = 0;

  closes[1].flags = 0;
  closes[1].user_tag = 1;
}


/*
 * Converter functions
 */
static char *get_label(void *aux, pp_open_token_t *tk) {
  assert(tk->user_tag < NOPENS);
  return open_labels[tk->user_tag];
}

static char *get_string(void *aux, pp_atomic_token_t *tk) {
  assert(tk->user_tag < NATOMS);
  return atom_strings[tk->user_tag];
}

static char *get_truncated(void *aux, pp_atomic_token_t *tk, uint32_t n) {
  assert(tk->user_tag < NATOMS);
  return atom_strings[tk->user_tag];
}

static void free_token(void *aux, void *tk) {
}

static pp_token_converter_t converter = {
  NULL,
  get_label,
  get_string,
  get_truncated,
  (free_open_token_fun_t) free_token,
  (free_atomic_token_fun_t) free_token,
  (free_close_token_fun_t) free_token,
};


/*
 * Display
 */
static pp_area_t display = {
  20, 1, 0, false, false,
};



/*
 * Test1: (f0 aaa (h50000 (f2 bbb ccc)) ddd)
 */
static void test1(pp_t *pp) {
  pp_push_token(pp, tag_open(opens + 0)); // f0
  pp_push_token(pp, tag_atomic(atoms + 0)); // aaa
  pp_push_token(pp, tag_open(opens + 9));   // h50000
  pp_push_token(pp, tag_open(opens + 2));   // f2
  pp_push_token(pp, tag_atomic(atoms + 1)); // bbb
  pp_push_token(pp, tag_atomic(atoms + 2)); // ccc
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_atomic(atoms + 3)); // ddd
  pp_push_token(pp, tag_close(closes + 0));
  flush_pp(pp);
}

/*
 * Test 2: (g1000 aaa bbb eee fff g)
 */
static void test2(pp_t *pp) {
  pp_push_token(pp, tag_open(opens + 5));   // g1000
  pp_push_token(pp, tag_atomic(atoms + 0)); // aaa
  pp_push_token(pp, tag_atomic(atoms + 1)); // bbb
  pp_push_token(pp, tag_atomic(atoms + 4)); // eee
  pp_push_token(pp, tag_atomic(atoms + 5)); // fff
  pp_push_token(pp, tag_atomic(atoms + 6)); // g
  pp_push_token(pp, tag_close(closes + 0));
  flush_pp(pp);
}

/*
 * Test 3: (f3 (f2 (f1 (f0 ccc))))
 */
static void test3(pp_t *pp) {
  pp_push_token(pp, tag_open(opens + 3)); // f3
  pp_push_token(pp, tag_open(opens + 2)); // f2
  pp_push_token(pp, tag_open(opens + 1)); // f1
  pp_push_token(pp, tag_open(opens + 0)); // f0
  pp_push_token(pp, tag_atomic(atoms + 2)); // cc
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_close(closes + 0));
  flush_pp(pp);
}


/*
 * Test 4: (f3 (f2 (f1 (f0 ccc)) h))
 */
static void test4(pp_t *pp) {
  pp_push_token(pp, tag_open(opens + 3)); // f3
  pp_push_token(pp, tag_open(opens + 2)); // f2
  pp_push_token(pp, tag_open(opens + 1)); // f1
  pp_push_token(pp, tag_open(opens + 0)); // f0
  pp_push_token(pp, tag_atomic(atoms + 2)); // cc
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_atomic(atoms + 7)); // h
  pp_push_token(pp, tag_close(closes + 0));
  pp_push_token(pp, tag_close(closes + 0));
  flush_pp(pp);
}



/*
 * Global pretty printer
 */
static pp_t pp;

int main() {
  uint32_t w;

  init_tokens();

  printf("\nNo truncate, height = %"PRIu32", width = %"PRIu32"\n",
	 display.height, display.width);
  init_pp(&pp, &converter, stdout, &display, PP_HMODE, 0);
  test1(&pp);
  test2(&pp);
  test3(&pp);
  test4(&pp);
  delete_pp(&pp);

  display.truncate = true;
  for (w = 20; w<50; w++) {
    display.width = w;
    printf("\n\nTruncate, height = %"PRIu32", width = %"PRIu32"\n",
	 display.height, display.width);
    init_pp(&pp, &converter, stdout, &display, PP_HMODE, 0);
    test1(&pp);
    test2(&pp);
    test3(&pp);
    test4(&pp);
    delete_pp(&pp);
  }


  // tests with height = 4
  // initial mode = PP_VMODE
  display.height = 4;

  display.width = 20;
  display.truncate = false;
  printf("\nNo truncate, height = %"PRIu32", width = %"PRIu32"\n",
	 display.height, display.width);
  init_pp(&pp, &converter, stdout, &display, PP_VMODE, 0);
  test1(&pp);
  test2(&pp);
  test3(&pp);
  test4(&pp);
  delete_pp(&pp);

  display.truncate = true;
  for (w = 4; w<50; w++) {
    display.width = w;
    printf("\n\nTruncate, height = %"PRIu32", width = %"PRIu32"\n",
	 display.height, display.width);
    init_pp(&pp, &converter, stdout, &display, PP_VMODE, 0);
    test1(&pp);
    test2(&pp);
    test3(&pp);
    test4(&pp);
    delete_pp(&pp);
  }


  display.truncate = false;
  for (w = 4; w<50; w++) {
    display.width = w;
    printf("\n\nNo truncate, height = %"PRIu32", width = %"PRIu32"\n",
	 display.height, display.width);
    init_pp(&pp, &converter, stdout, &display, PP_VMODE, 0);
    test1(&pp);
    test2(&pp);
    test3(&pp);
    test4(&pp);
    delete_pp(&pp);
  }

  return 0;
}
