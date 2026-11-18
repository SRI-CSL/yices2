/*
 * Copyright (c) 2026, SRI International
 * SPDX-License-Identifier: BSD-3-Clause
 */

/*
 * Detect that a problem belongs to a smaller logic than the one
 * declared by (set-logic ...), so that the front end can use the solver
 * architecture of the smaller logic (e.g., QF_LIA instead of QF_NIA).
 */

#ifndef __SMT2_SUBLOGIC_H
#define __SMT2_SUBLOGIC_H

#include <stdint.h>

#include "api/smt_logic_codes.h"
#include "terms/terms.h"


/*
 * Find the smallest quantifier-free logic that contains the formulas a[0 ... n-1]
 * and is a sublogic of the declared logic.
 *
 * - terms = term table that contains the formulas
 * - declared = logic given in (set-logic ...). It must be a supported
 *   quantifier-free logic.
 *
 * The function returns the declared logic when it can't find a smaller
 * logic, when the formulas use constructs that are not analyzed (quantifiers,
 * tuples, lambdas, finite fields, algebraic numbers), or when the formulas
 * need non-linear arithmetic.
 *
 * It returns a different logic only if that logic requires a different
 * solver architecture than the declared logic.
 */
extern smt_logic_t smt2_smallest_sublogic(term_table_t *terms, smt_logic_t declared,
                                          const term_t *a, uint32_t n);

#endif /* __SMT2_SUBLOGIC_H */
