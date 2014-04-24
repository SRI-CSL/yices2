#include <stdbool.h>

#include "thread_error.h"

#ifdef HAS_TLS
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL static
#endif

#include "yices_types.h"



YICES_THREAD_LOCAL int32_t _yices_tl_errno;

YICES_THREAD_LOCAL bool _yices_error_initialized = false;
YICES_THREAD_LOCAL error_report_t _yices_error;

static inline init_yices_error(void){

  if(!_yices_error_initialized){
    _yices_error_initialized = true;
    memset(&_yices_error, 0, sizeof(error_report_t));
  }

}

static inline error_report_t* get_yices_error(){
  init_yices_error();
  return &_yices_error;
}

void set_yices_error_code(error_code_t code){
  error_report_t* _yices_errorp =  get_yices_error();
  _yices_errorp->code = code;
}

error_code_t get_yices_error_code(){
  error_report_t* _yices_errorp =  get_yices_error();
  return _yices_errorp->code;
}


void set_tl_error(int32_t code){
  _yices_tl_errno = code;
}


int32_t get_tl_error(void){
  return _yices_tl_errno;
}
