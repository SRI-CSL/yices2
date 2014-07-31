/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

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

#include "terms/terms.h"
#include "model/concrete_values.h"
#include "utils/int_hash_map.h"

#include "yices_types.h"


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
struct model_s {
  value_table_t vtbl;
  int_hmap_t map;
  int_hmap_t *alias_map;
  term_table_t *terms;
  bool has_alias;
};


/*
 * Initialize model
 * - terms = attached term table
 * - keep_subst = whether to support alias_map or not
 * - map and vtbl are given default sizes
 * - alias_map is NULL
 */
extern void init_model(model_t *model, term_table_t *terms, bool keep_subst);


/*
 * Delete model
 * - free all internal memory
 */
extern void delete_model(model_t *model);


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
 * - model->has_alias must be true
 */
extern term_t model_find_term_substitution(model_t *model, term_t t);


/*
 * Store the mapping t := v in model
 * - t must be a valid term index (not null_term)
 * - t must not be mapped to anything
 * - v must be a valid object created in model->vtbl.
 *
 * If v is a function object and it has no name, then t's name is
 * given to v.
 */
extern void model_map_term(model_t *model, term_t t, value_t v);


/*
 * Store the substitution t --> u in the model
 * - t and u must be valid term indices
 * - t must be an uninterpreted term, not mapped to anything
 * - model->has_alias must be true
 */
extern void model_add_substitution(model_t *model, term_t t, term_t u);


/*
 * Iteration: call f(aux, t) for every term t stored in the model
 * - this includes every t in model->map (term mapped to a value)
 * - if all is  true, then the iterator is also applied  to every t in
 *   the domain of model->alias (term mapped to another term)
 * - f must not have side effects on model
 */
typedef void (*model_iterator_t)(void *aux, term_t t);

extern void model_term_iterate(model_t *model, bool all, void *aux, model_iterator_t f);


/*
 * Term collector: call f(aux, t) for every term t that's stored in the model
 * - if f(aux, t) returns true, add t to vector v
 * - if all is false, only the terms in model->map are considered
 * - if all is true, the terms in model->map and model->alias are considered
 * - f must not have side effects
 *
 * NOTE: v is not reset. All terms collected are added to v
 */
typedef bool (*model_filter_t)(void *aux, term_t t);

extern void model_collect_terms(model_t *model, bool all, void *aux, model_filter_t f, ivector_t *v);


/*
 * Prepare for garbage collection: mark all the terms present in model
 * - all marked terms will be considered as roots on the next call
 *   to term_table_gc
 */
extern void model_gc_mark(model_t *model);


#endif /* __MODELS_H */
