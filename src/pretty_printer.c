/*
 * PRETTY PRINTER
 */

#include <stddef.h>
#include <stdio.h>

#include "pretty_printer.h"

static char *get_label(void *ptr, pp_token_t *tk) {
  return "aaaa";
}

static char *get_string(void *ptr, pp_token_t *tk) {
  return "bbbb";
}

static char *get_truncated(void *ptr, pp_token_t *tk, uint32_t k) {
  return "cccc";
}

static pp_token_converter_t converter = {
  NULL,
  get_label,
  get_string,
  get_truncated,
};

void test_converter(void) {
  pp_token_converter_t *c;

  c = &converter;
  printf("get_label: %s\n", c->get_label(c->user_ptr, NULL));
  printf("get_string: %s\n", c->get_string(c->user_ptr, NULL));
  printf("get_tuncated: %s\n", c->get_truncated(c->user_ptr, NULL, 0));
}
