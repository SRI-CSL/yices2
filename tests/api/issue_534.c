#include <yices.h>
#include <string.h>
#include <stdio.h>

int main(void) {
  yices_init();
  type_t int_type = yices_int_type();
  term_t x = yices_new_uninterpreted_term(int_type);
  term_t y = yices_new_uninterpreted_term(int_type);
  yices_set_term_name(x, "x");
  yices_set_term_name(y, ")");
  term_t formula = yices_arith_eq_atom(x, y);
  char* output = yices_term_to_string(formula, 1000, 1, 0);

  if (output == NULL) {  // Added NULL check
    printf("Error: yices_term_to_string returned NULL\n");
    yices_exit();
    return -1;
  }

  if (strcmp(output, "(= x |)|)") != 0) {
    printf("Expected output: (= x |)|)\n");
    printf("Got output: %s\n", output);
    yices_free_string(output);
    yices_exit();
    return -1;
  }

  yices_free_string(output);
  yices_exit();
  return 0;
}
