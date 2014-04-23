#include <stdbool.h>

#include "thread_error.h"

#ifdef HAS_TLS
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL static
#endif

#include "yices_types.h"



YICES_THREAD_LOCAL int32_t _yices_tl_errno;

YICES_THREAD_LOCAL bool error_initialized = false;
YICES_THREAD_LOCAL error_report_t _yices_error;



void set_tl_error(int32_t code){
  _yices_tl_errno = code;
}


int32_t get_tl_error(void){
  return _yices_tl_errno;
}
