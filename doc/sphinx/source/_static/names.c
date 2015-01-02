/*
 * Illustrates the naming functions of Yices.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <yices.h>

/*
 * Retrieve a term with the given name and print it
 */
static void show_term(const char *name) {
  term_t t;

  t = yices_get_term_by_name(name);
  if (t == NULL_TERM) {
    printf("No term of name '%s'\n", name);
  } else {
    printf("The term of name '%s' is ", name);
    yices_pp_term(stdout, t, 20, 4, 23 + strlen(name));
  }
}

/*
 * Show the base name of term t
 */
static void show_name(term_t t) { 
  char *str;
  const char *name;

  str =  yices_term_to_string(t, 100, 1, 0);
  assert(str != NULL);
  name = yices_get_term_name(t);
  if (name == NULL) {
    printf("Term %s has no name\n", str);
  } else {
    printf("Term %s has name '%s'\n", str, name);
  }
  yices_free_string(str);
}

static void test_names(void) {
  type_t tau;
  term_t a, b, c, t;

  /*
   * Create some terms
   */
  tau = yices_bool_type();
  a = yices_new_uninterpreted_term(tau);
  b = yices_new_uninterpreted_term(tau);
  c = yices_or2(a, b);

  /*
   * At this point: a, b, c don't have names
   * So printing them will show something like this:
   *   a: t!3
   *   b: t!4
   *   c: (or t!3 t!4)
   */
  printf("unamed terms:\n");
  printf("  a: ");
  yices_pp_term(stdout, a, 20, 1, 4);
  printf("  b: ");
  yices_pp_term(stdout, b, 20, 1, 4);
  printf("  c: ");
  yices_pp_term(stdout, c, 20, 1, 4);
  printf("\n");

  /*
   * We assign base-names to these terms.
   * Printing will show:
   *   a: a
   *   b: b
   *   c: (or a b)
   */
  yices_set_term_name(a, "a");
  yices_set_term_name(b, "b");
  yices_set_term_name(c, "c");
  printf("named terms:\n");
  printf("  a: ");
  yices_pp_term(stdout, a, 20, 1, 4);
  printf("  b: ");
  yices_pp_term(stdout, b, 20, 1, 4);
  printf("  c: ");
  yices_pp_term(stdout, c, 20, 1, 4);
  printf("\n");

  /*
   * We can get the base name of a term using function
   * yices_get_term_name.
   */
  show_name(a);
  show_name(b);
  show_name(c);

  /*
   * We can get terms using their names
   */
  show_term("a");
  show_term("b");
  show_term("c");

  /*
   * We can assign the name "c" to another term.
   * This hides the current mapping of "c"
   */
  t = yices_iff(a, b);
  yices_set_term_name(t, "c");
  printf("\nAfter remapping name 'c'\n");
  show_term("c");
  // But the base name of c is still "c"
  show_name(c);
  // That's also the base name of t
  show_name(t);
  
  /*
   * We remove the current mapping for name "c"
   * The previous meaning is restored: "c" now refers to (or a b)
   */
  yices_remove_term_name("c");
  printf("\nAfter removing the mapping of 'c'\n");
  show_term("c");
  // t still has "c" as its base name
  show_name(t);

  /*
   * We can fully clear the name of t
   */
  yices_clear_term_name(t);
  printf("\nAfter clearing the name of (= a b)\n");
  show_name(t);

  /*
   * If we clear the names of a and c, this also
   * removes the mapping "a" --> a and "c" --> c from
   * the symbol table.
   *
   * Now c will be printed as 
   *   (or t!3 b)
   *
   * and yices_get_term_by_name("c") returns NULL_TERM
   */
  yices_clear_term_name(a);
  yices_clear_term_name(c);
  printf("\nhalf-named terms:\n");
  printf("  a: ");
  yices_pp_term(stdout, a, 20, 1, 4);
  printf("  b: ");
  yices_pp_term(stdout, b, 20, 1, 4);
  printf("  c: ");
  yices_pp_term(stdout, c, 20, 1, 4);
  printf("\n");

  show_name(a);
  show_name(b);
  show_name(c);

  show_term("a");
  show_term("b");
  show_term("c");  
}

int main(void) {
  yices_init();
  test_names();
  yices_exit();

  return 0;
}
