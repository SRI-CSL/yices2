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
 * Test
 */

#include <stdio.h>
#include <setjmp.h>
#include <inttypes.h>

static void jumper(jmp_buf *env) {
  uint32_t i, j;

  for (i=0; i<10000; i++) {
    for (j=0; j<10000; j++) {
      if (j == i) {
	printf("+");
      }
    }
  }

  printf("\ncalling longjmp\n\n");
  fflush(stdout);
  longjmp(*env, 23);
}


static void catcher(void) {
  jmp_buf env;
  int code;

  printf("calling setjmp\n\n");
  fflush(stdout);
  code = setjmp(env);
  if (code == 0) {
    printf("calling jumper\n\n");
    fflush(stdout);
    jumper(&env);
  } else {
    printf("return from longjmp: code = %d\n", code);
    fflush(stdout);
  }
}

typedef struct {
  jmp_buf *ptr;
} buffer_t;

static buffer_t aux;

static void set_buffer(jmp_buf *b) {
  aux.ptr = b;
}

static void jumper2(void) {
  uint32_t i, j;

  for (i=0; i<10000; i++) {
    for (j=0; j<10000; j++) {
      if (j == i) {
	printf(".");
      }
    }
  }

  printf("\ncalling longjmp\n\n");
  fflush(stdout);
  longjmp(*aux.ptr, 45);
}

static void catcher2(void) {
  jmp_buf env;
  int code;

  printf("initializing buffer\n");
  set_buffer(&env);

  printf("calling setjmp\n\n");
  fflush(stdout);
  code = setjmp(env);
  if (code == 0) {
    printf("calling jumper2\n\n");
    fflush(stdout);
    jumper2();
  } else {
    printf("return from longjmp: code = %d\n", code);
    fflush(stdout);
  }
}


int main(void) {
  catcher();
  catcher2();
  return 0;
}
