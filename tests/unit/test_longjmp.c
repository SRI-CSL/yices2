/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
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


int main() {
  catcher();
  catcher2();
  return 0;
}
