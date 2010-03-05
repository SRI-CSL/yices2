/*
 * MODELS
 */

/* 
 * A model is a (partial) map from terms to concrete values.
 *
 * The terms in this map's domain should be uninterpreted constant,
 * functions, or predicates. That should be enough for computing the
 * value of any other term.
 *
 * Added 06/10/2009: A model can also store a substitution table
 * (i.e. a mapping from uninterpreted terms to terms.) This allows us
 * to keep track of the variable substitutions performed during
 * internalization (cf. context.h).
 */


#ifndef __MODELS_H
#define __MODELS_H

#include <stdint.h>

#include "terms.h"
#include "concrete_values.h"
#include "int_hash_map.h"


/*
 * Model structure:
 * - vtbl = table where the concrete values are constructed
 * - map = hash map for storing the map from terms to concrete
 *   values (fixed part of the model)
 * - alias_map = hash map for storing the substitution table
 *   (it's allocated on demand).
 * - terms = term table where all terms are stored
 * - has_alias: flag true if the model is intended to support
 *   the internal substitution table (alias_map). (NOTE: has_alias
 *   is set at construction time and it may be true even if alias_map is NULL).
 */
typedef struct model_s {
  value_table_t vtbl;
  int_hmap_t map;
  int_hmap_t *alias_map;
  term_table_t *terms;
  bool has_alias;
} model_t;



/*
 * Allocate an initialize a model
 * - terms = the attached term table
 * - keep_subst = whether to support alias_map or not
 * - map and vtbl are given default sizes
 * - alias_map is NULL
 */
extern model_t *new_model(term_table_t *terms, bool keep_subst);


/*
 * Delete a model
 */
extern void free_model(model_t *model);


/*
 * Get the internal vtbl
 */
static inline value_table_t *model_get_vtbl(model_t *model) {
  return &model->vtbl;
}

/*
 * Find the value of term t in model
 * - t must be a valid term index (null_term is not allowed here)
 * - return null_value if t is not mapped to anything
 * - return the concrete object mapped to t otherwise
 */
extern value_t model_find_term_value(model_t *model, term_t t);


/*
 * Check whether t is mapped to a term v in the substitution table.
 * - return v if it is
 * - return NULL_TERM otherwise
 */
extern term_t model_find_term_substitution(model_t *model, term_t t);


/*
 * Store the mapping t := v in model
 * - t must be a valid term index (not null_term)
 * - t must not be mapped to anything
 * - v must be a valid object created in model->vtbl.
 *
 * If v is uninterpreted or a function object and it has no name,
 * then t's name is given to v.
 */
extern void model_map_term(model_t *model, term_t t, value_t v);


/*
 * Store the substitution t --> u in the model
 * - t and u must be valid term indices
 * - t must be an uninterpreted term, not mapped to anything
 */
extern void model_add_substitution(model_t *model, term_t t, term_t u);


#endif /* __MODELS_H */
