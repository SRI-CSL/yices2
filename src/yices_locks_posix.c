//this should go once we are more at home in yices.
#include <stdio.h>
#include <assert.h>
#include <errno.h>

//I see NDEBUG and DEBUG in the code; which is it?
#ifdef DEBUG
static pthread_mutexattr_t mta;
static pthread_mutexattr_t* mattr = &mta;
#else 
static pthread_mutexattr_t* mattr = NULL;
#endif

 
int create_yices_lock(yices_lock_t* lock){
  int retcode;
#ifdef DEBUG
  retcode = pthread_mutexattr_settype(&mta, PTHREAD_MUTEX_ERRORCHECK);
  if(retcode){
    fprintf(stderr, "create_yices_lock failed: pthread_mutexattr_settype returned %d\n", retcode);
  }
#endif
  retcode = pthread_mutex_init(lock, mattr);
  if(retcode){
    fprintf(stderr, "create_yices_lock failed: pthread_mutex_init returned %d\n", retcode);
  }
  assert(retcode == 0);
  return 0;
}

int try_yices_lock(yices_lock_t* lock){
  int retcode = pthread_mutex_trylock(lock);
  if(retcode){
    if(retcode == EBUSY){
      return 1;
    } else {
      fprintf(stderr, "try_yices_lock failed: pthread_mutex_trylock returned %d\n", retcode);
    }
    return -1;
  }
  return 0;
}


int get_yices_lock(yices_lock_t* lock){
  int retcode = pthread_mutex_lock(lock);
  if(retcode){
    fprintf(stderr, "get_yices_lock failed: pthread_mutex_lock returned %d\n", retcode);
  }
  assert(retcode == 0);
  return 0;
}

int release_yices_lock(yices_lock_t* lock){
  int retcode = pthread_mutex_unlock(lock);
  if(retcode){
    fprintf(stderr, "release_yices_lock failed: pthread_mutex_unlock returned %d\n", retcode);
  }
  assert(retcode == 0);
  return 0;
}

void destroy_yices_lock(yices_lock_t* lock){
  int retcode = pthread_mutex_destroy(lock);
  if(retcode){
    fprintf(stderr, "destroy_yices_lock failed: pthread_mutex_destroy returned %d\n", retcode);
  }
  assert(retcode == 0);
}
