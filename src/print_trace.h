#ifndef __PRINT_TRACE_H
#define __PRINT_TRACE_H
#include <stdint.h>

extern void print_trace (void);

#define YICES_ASSERT(X)   {  bool check = (X); if(!check){ print_trace(); assert(check); } }

#endif /* __PRINT_TRACE_H */
