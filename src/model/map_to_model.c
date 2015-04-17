/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * CONVERT A MAPPING TO A MODEL
 */

#include <assert.h>

#include "model/map_to_model.h"
#include "model/term_to_val.h"



/*
 * Build mdl from the mapping [var[i] := map[i]]
 * - mdl must be initialized
 *   every var[i] and map[i] must be a valid term defined in mdl->terms.
 *
 * - var[0 ... n-1] must all be uninterpreted terms
 *   map[0 ... n-1] must all be constant terms (of primitive or tuple type)
 *   map[i]'s type must be a subtype of var[i]'s type
 *
 * - the terms var[i] must be all distinct
 */
void build_model_from_map(model_t *model, uint32_t n, const term_t *var, const term_t *map) {
  term_converter_t convert;
  term_table_t *terms;
  value_table_t *vtbl;
  uint32_t i;
  term_t x, a;
  value_t v;

  terms = model->terms;
  vtbl = &model->vtbl;

  init_term_converter(&convert, terms, vtbl);
  for (i=0; i<n; i++) {
    x = var[i];
    a = map[i];
    assert(term_kind(terms, x) == UNINTERPRETED_TERM &&
	   is_constant_term(terms, a) &&
	   is_subtype(terms->types, term_type(terms, a), term_type(terms, x)));

    /*
     * Convert_term_to_val shouldn't fail since a is a either a
     * constant tuple or an primitive constant.
     */
    v = convert_term_to_val(&convert, a);
    assert(good_object(vtbl, v));

    model_map_term(model, x, v);
  }

  delete_term_converter(&convert);
}


