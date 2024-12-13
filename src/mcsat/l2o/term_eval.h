
#include "terms/terms.h"

#ifndef MCSAT_L2O_TERMEVAL_H_
#define MCSAT_L2O_TERMEVAL_H_

typedef struct term_eval_s {
  bool is_double;
  union {
    double cost;
    term_t term;
  };
} term_eval_t;

#endif /* MCSAT_L2O_TERMEVAL_H_ */
