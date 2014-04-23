#include "thread_error.h"


__thread  int32_t _tl_errno;


void set_tl_error(int32_t code){

  _tl_errno = 0;

}


int32_t get_tl_error(void){


  return _tl_errno;
}
