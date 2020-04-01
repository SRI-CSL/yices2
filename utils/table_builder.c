/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Build tables for parsing and relatives
 * - the input is a set of triples <state, token, value>
 *   or <state, default, value>, and a global default value d
 * - the set must be deterministic: no triples have the same
 *   state and token.
 *
 * This defines a function f that maps states and tokens to values: 
 * - f(s, t) = v if <s, t, v> is a triple
 * - f(s, t) = v0 if <s, default, v0> is a triple and there's no
 *   triple of the form <s, t, _>
 * - f(s, t) = global default otherwise.
 *         
 * The code builds four tables default, table, val, and check
 * that encode the function in a compact way. 
 * - for every state c, 
 *   default[c] = a default value for state c (or error)
 *   base[c] = an index in array val and check
 * - for an index i, 
 *   val[i] = a value
 *   check[i] = a state
 *
 * The goal is to build the table so that f(s, t) is computed 
 * as follows:
 * let i = base[s] + t;
 * if check[i] = s then return val[i] else return default[s]
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>


/*
 * The specification file must define 
 * NSTATES, NTOKENS, DEFAULT_TOKEN, DEFAULT_VALUE, and triple
 */
// #include "smt2_input_tables.h"
#include "yices_input_tables.h"

/*
 * Descriptor for each state
 */
typedef struct edge_s {
  int token;
  char * val;
} edge_t;

typedef struct {
  char * def; // default value for that state
  int nedges;  // number of edges known
  int size;    // size of array edge
  edge_t *edge;
} state_desc_t;

static state_desc_t state[NSTATES];

/*
 * Initialization
 */
static void init_state_descriptors(void) {
  int i;
  edge_t *tmp;

  for (i=0; i<NSTATES; i++) {
    state[i].def = DEFAULT_VALUE;
    state[i].nedges = 0;
    state[i].size = 2;
    tmp = (edge_t *) malloc(20 * sizeof(edge_t));
    if (tmp == NULL) {
      fprintf(stderr, "Malloc failed; could not allocate descriptors\n");
      abort();
    }
    state[i].edge = tmp;
  }
}

/*
 * Add edge x, val to state i
 */
static void add_edge(int i, int x, char * v) {
  state_desc_t *desc;
  edge_t *e;
  int j, n;

  desc = state + i;

  if (x == DEFAULT_TOKEN) {
    if (strcmp(desc->def, DEFAULT_VALUE) == 0) {
      desc->def = v;
    } else {
      fprintf(stderr, "Error: two default values for state %d\n", i);
      abort();
    }
  } else {
    e = desc->edge;
    for (j=0; j<desc->nedges; j++) {
      if (e[j].token == x) {
	fprintf(stderr, "Error: two values for (state %d, token %d)\n", i, x);
	abort();
      }
    }
    
    if (j >= desc->size) {
      n = desc->size * 2;
      e = (edge_t *) realloc(e, n * sizeof(edge_t));
      if (e == NULL) {
	fprintf(stderr, "Realloc failed; could not allocate descriptors\n");
	abort();
      }
      desc->edge = e;
      desc->size = n;
    }

    e[j].token = x;
    e[j].val = v;
    desc->nedges ++;
  }
}


/*
 * Read all the triples
 */
static void set_descriptors(triple_t *l) {
  while (((int) l->source) >= 0) {
    //    printf("Adding triple %d %d %s\n", l->source, l->token, l->value);
    if (l->source >= NSTATES) {
      fprintf(stderr, "Error: triple state = %d, number of states = %d\n", l->source, NSTATES);
      abort();
    }
    add_edge(l->source, l->token, l->value);
    l ++;
  }
}

/*
 * Print the descriptors
 */
static void print_descriptors(void) {
  int i, j, n;
  edge_t *e;

  for (i=0; i<NSTATES; i++) {
    printf("state %d\n", i);
    n = state[i].nedges;
    e = state[i].edge;
    for (j=0; j<n; j++) {
      printf("  token %d: %s\n", e[j].token, e[j].val);
    }
    printf("  default: %s\n", state[i].def);
  }
}


/*
 * Tables to construct
 */
static char * defval[NSTATES];
static int base[NSTATES];
static int val_size;
static int *check;
static char * *val;


/*
 * Allocate tables check and val, with initial size = 2*NTOKENS
 * Set all defaults in deval
 */
static void init_tables(void) {
  int i, n;

  for (i=0; i<NSTATES; i++) {
    defval[i] = state[i].def;
  }

  n = 2*NTOKENS;
  val_size = n;
  check = (int *) malloc(n * sizeof(int));
  val = (char * *) malloc(n * sizeof(char *));
  if (check == NULL || val == NULL) {
    fprintf(stderr, "Malloc failed: could not allocate check or val table\n");
    abort();
  }

  for (i=0; i<n; i++) {
    check[i] = NSTATES;
    val[i] = DEFAULT_VALUE;
  }
}

/*
 * Extend the tables: make then twice as large
 */
static void extend_tables(void) {
  int i, n;

  n = 2 * val_size;
  check = (int *) realloc(check, n * sizeof(int));
  val = (char * *) realloc(val, n * sizeof(char *));
  if (check == NULL || val == NULL) {
    fprintf(stderr, "Realloc failed: could not extend check or val table\n");
    abort();
  }

  for (i=val_size; i<n; i++) {
    check[i] = NSTATES;
    val[i] = DEFAULT_VALUE;
  }

  val_size = n;
}

/*
 * Check whether setting base[i] = b causes a conflict
 */
static bool base_possible(state_t i, int b) {
  state_desc_t *desc;
  edge_t *e;
  int j, n, k;

  desc = state + i;
  e = desc->edge;
  n = desc->nedges;

  for (j=0; j<n; j++) {
    k = b + e[j].token;
    if (check[k] != NSTATES) {
      return false;
    }
  }
  return true;
}

/*
 * Store data for state i at base b
 */
static void build_state_base(state_t i, int b) {
  state_desc_t *desc;
  edge_t *e;
  int j, n, k;

  desc = state + i;
  e = desc->edge;
  n = desc->nedges;

  base[i] = b;

  for (j=0; j<n; j++) {
    k = b + e[j].token;
    check[k] = i;
    val[k] = e[j].val;
  }
}


/*
 * Store data for state i
 */
static void find_base(state_t i) {
  int b;

  b=0;
  while (! base_possible(i, b)) {
    b ++;
    if (b + NTOKENS > val_size) {
      extend_tables();
    }
  }
  build_state_base(i, b);
}


/*
 * Build the full tables
 */
static void build_tables(void) {
  state_t i;

  init_tables();
  for (i=0; i<NSTATES; i++) {
    find_base(i);
  }
}


/*
 * Print the tables
 */
static void print_tables(void) {
  int i, maxbase, size;

  maxbase = base[0];
  for (i=1; i<NSTATES; i++) {
    if (base[i] > maxbase) {
      maxbase = base[i];
    }
  }
  size = maxbase + NTOKENS;

  printf("/*\n"
	 " * Tables generated by table_builder\n"
	 " * see utils/table_builder.c\n"
	 " */\n\n");

  printf("// Table sizes\n");
  printf("#define NSTATES %d\n", NSTATES);
  printf("#define BSIZE %d\n\n", size);

  printf("// Default values for each state\n");
  printf("static value_t default_value[NSTATES] = {\n");
  for (i=0; i<NSTATES; i++) {
    printf("  %s,\n", defval[i]);
  }
  printf("};\n\n");

  printf("// Base values for each state\n");
  printf("static int base[NSTATES] = {");
  for (i=0; i<NSTATES; i++) {
    if (i % 10 == 0) printf("\n  ");
    printf("%4d,", base[i]);
  }
  printf("\n};\n\n");

  printf("// Check table\n");
  printf("static int check[BSIZE] = {");
  for (i=0; i<size; i++) {
    if (i % 10 == 0) printf("\n  ");
    printf("%4d,", check[i]);
  }
  printf("\n};\n\n");

  printf("// Value table\n");
  printf("static value_t value[BSIZE] = {\n");
  for (i=0; i<size; i++) {
    printf("  %s,\n", val[i]);
  }
  printf("};\n\n");
}


/*
 * Check the tables
 */
static char *get_val(state_t i, token_t t) {
  int k;

  k = base[i] + t;
  if (check[k] == i) {
    return val[k];
  } else {
    return defval[i];
  }
}

static char *get_desc_val(state_t i, token_t t) {
  state_desc_t *desc;
  edge_t *e;
  int j, n;

  desc = state + i;
  e = desc->edge;
  n = desc->nedges;

  for (j=0; j<n; j++) {
    if (e[j].token == t) return e[j].val;
  }

  return desc->def;
}

static void check_tables(void) {
  int i, j, n;
  char *v1, *v2;

  n = 0;
  for (i=0; i<NSTATES; i++) {
    for (j=0; j<NTOKENS; j++) {
      v1 = get_val(i, j);
      v2 = get_desc_val(i, j);
      if (v1 != v2) {
	n ++;
	fprintf(stderr, "Error in tables\n");
	fprintf(stderr, "  get_val(%d, %d) = %s\n", i, j, v1);
	fprintf(stderr, "  get_desc_val(%d, %d) = %s\n", i, j, v2);
      }
    }
  }
  if (n == 0) {
    fprintf(stderr, "Tables appear correct\n");
  }
}

int main(void) {
  init_state_descriptors();
  set_descriptors(triples);  
  print_descriptors();

  build_tables();
  print_tables();
  check_tables();
  return 0;
}
