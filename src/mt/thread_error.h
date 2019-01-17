#ifndef __THREAD_ERRORS_H
#define __THREAD_ERRORS_H
#include <stdint.h>

#include "yices_types.h"

extern void set_tl_error(int32_t code);

extern int32_t get_tl_error(void);

extern void set_yices_error_code(error_code_t code);

extern error_code_t get_yices_error_code();


#endif /* __THREAD_ERRORS_H */

