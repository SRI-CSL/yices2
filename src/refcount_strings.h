/*
 * Strings with reference counter
 */

#ifndef __REFCOUNT_STRINGS
#define __REFCOUNT_STRINGS

#include <stdint.h>
#include <stddef.h>


/*
 * The reference counter is hidden in a header
 */
typedef struct {
  uint32_t ref;  // should be plenty; no check for overflow is implemented.
  char str[0];   // the real size is determined a allocation time.
} string_t;


/*
 * Make a copy of str with ref count 0.
 * - str must be terminated by '0'
 */
extern char *clone_string(const char *str);

/*
 * header of string s
 */
static inline string_t *string_header(const char *s) {
  return (string_t *) (s - offsetof(string_t, str));
}

/*
 * Increment ref counter for string s
 */
static inline void string_incref(char *s) {
  string_header(s)->ref ++;
}

/*
 * Decrement ref counter for s and free the string if the 
 * counter is zero
 */
extern void string_decref(char *s);

#endif
