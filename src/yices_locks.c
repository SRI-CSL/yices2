
#include "yices_locks.h"


#ifndef MINGW
#include "yices_locks_posix.c"
#else
#include "yices_locks_win.c"
#endif
