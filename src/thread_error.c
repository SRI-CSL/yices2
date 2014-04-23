#include <stdbool.h>

#include "thread_error.h"

#if HAS_TLS
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL static
#endif

#include "yices_types.h"



YICES_THREAD_LOCAL int32_t _tl_errno;

YICES_THREAD_LOCAL bool error_initialized = false;
YICES_THREAD_LOCAL error_report_t error;



void set_tl_error(int32_t code){
  _tl_errno = code;
}


int32_t get_tl_error(void){
  return _tl_errno;
}
