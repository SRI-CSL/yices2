/*
 * Compute memory usage
 *
 * Three implementations:
 * - on Mac OS X: use mach kernel API
 * - on solaris: read /proc/<pid>/psinfo
 * - on other systems: try to get it by 
 *   reading /proc/<pid>/statm
 * - on mingw: nothing implemented. Return 0.0
 */

#include "memsize.h"


#if defined(MACOSX)

/*
 * MACOS IMPLEMENTATION
 */
#include <sys/types.h>

#include <mach/mach.h>
#include <mach/mach_error.h>
#include <mach/vm_region.h>

/*
 * This is intended to give a memory size close to what top reports
 * - scan all the memory regions and don't count all the regions that
 *   have shared_mode == SM_EMPTY
 * - the total virtual memory size is much larger
 */
double mem_size(void) {
  mach_port_t port;
  kern_return_t error;
  mach_msg_type_number_t count;
  vm_region_top_info_data_t top_info;
  vm_address_t address;
  vm_size_t size;
  mach_port_t object_name;
  uint64_t total_size;

  total_size = 0;
  port = mach_task_self();

  address = 0;
  do {
    count = VM_REGION_TOP_INFO_COUNT;
    error = vm_region_64(port, &address, &size, VM_REGION_TOP_INFO,
			 (vm_region_info_t) &top_info, &count, &object_name);

    if (error != KERN_SUCCESS) {
      //      mach_error("vm_region", error);
      goto end;
    }

    // regions with mode == SM_EMPTY are stack guards or similar regions
    // the global shared library segment too has share_mode == SM_EMPTY 
    if (top_info.share_mode != SM_EMPTY) {
      total_size += size;
    }

    address += size;

  } while (address != 0);

  
end:
  return (double) total_size;
}

#elif defined(SOLARIS)

/*
 * SOLARIS IMPLEMENTATION
 */
#include <sys/types.h>
#include <fcntl.h>
#include <procfs.h>
#include <unistd.h>
#include <stdio.h>

double mem_size(void) {
  pid_t pid;
  char buffer[50];
  int f;
  psinfo_t info;
  double size;
  ssize_t code;

  size = 0; // set to a default value
  pid = getpid();
  sprintf(buffer, "/proc/%u/psinfo", (unsigned) pid);
  f = open(buffer, O_RDONLY, 0);
  if (f < 0) goto done;
  code = read(f, &info, sizeof(info));
  if (code == sizeof(info)) {
    // infor.pr_size is the process size in Kb
    size = ((double) info.pr_size) * 1024;
  }
  close(f);
 done:
  return size;
}


#elif ! defined (MINGW) 

/*
 * DEFAULT LINUX IMPLEMENTATION
 *
 * read /proc/<pid>/statm
 * also seem to work on cygwin
 */
#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>

static unsigned long get_pages(void) {
  pid_t pid;
  FILE *proc_file;
  unsigned long pages;
  char buffer[30];

  pid = getpid();
  sprintf(buffer, "/proc/%u/statm", (unsigned) pid);
  proc_file = fopen(buffer, "r");
  if (proc_file == NULL) {
    return 0;
  }

  /*
   * In some versions of glibc, fscanf is declared with attribute
   * warn_unused_result. In such cases, we get a compilation warning,
   * even though the code is safe. I've changed the code a bit to 
   * avoid this warning.
   */
  pages = 0;
  //  fscanf(proc_file, "%lu", &pages); // if this fails, pages will remain 0
  if (fscanf(proc_file, "%lu", &pages) != 1) {
    pages = 0;
  }

  fclose(proc_file);

  return pages;
}

double mem_size(void) { 
  return (double)(getpagesize() * get_pages());
}

#else 

// MINGW: don't know how to implement anything reasonable

double mem_size(void) {
  return 0.0;
}

#endif

