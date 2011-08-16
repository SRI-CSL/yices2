/*
 * TYPE MACROS
 */

/*
 * This is intended to support SMT LIB2 functions 
 *     (declare-sort <name> <arity>)
 * and (define-sort <name> (<list-of-names>) <sort>)
 * when the arity is non-zero or the list-of-names is non-empty.
 *
 * With these constructs, we create a macro descriptor
 * that consists of a name, an arity, a body, and a finite 
 * array of type variables.
 * - for (declare-sort <name> <arity> )
 *   the macro descriptor is as follows:
 *       name = <name>
 *       arity = <arity>
 *       body = NULL_TYPE
 *       vars = none
 * - for (define-sort <name> (<X1> ... <Xn>) <sort> ),
 *   the macro descriptor is
 *       name = <name>
 *       arity = n
 *       body = <sort>
 *       vars = [<X1> ... <Xn>]
 *
 * We also need to keep track of existing macro applications
 * in a hash table. The hash table contains:
 *     [macro-id, type1, ..., type_n --> type]
 *  where macro-id refers to a macro or arity n.
 */

#ifndef __TYPE_MACROS_H
#define __TYPE_MACROS_H

#include <stdint.h>

#include "symbol_tables.h"
#include "types.h"


/*
 * Macro descriptor
 */
typedef type_macro_s {
  char *name;
  uint32_t arity;
  type_t body;
  type_t vars[0]; // real size = arity unless body = NULL_TYPE
} type_macro_t;





#endif


