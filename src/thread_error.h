#ifndef __THREAD_ERRORS_H
#define __THREAD_ERRORS_H
#include <stdint.h>

void set_tl_error(int32_t code);


int32_t get_tl_error(void);


#endif /* __THREAD_ERRORS_H */

