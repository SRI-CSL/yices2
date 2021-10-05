#include "yices.h"

int main(void) {
  yices_init();
  type_t bool_type = yices_bool_type();
  for (int i = 0; i < 2500; ++i) {
    term_t t = yices_new_uninterpreted_term(bool_type);
    yices_incref_term(t);
  }
  yices_exit();
  return 0;
}

