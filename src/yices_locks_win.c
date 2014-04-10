// we need _WIN32_WINNT as 0x0403 or later

int create_yices_lock(yices_lock_t* lock){
  /* to check the return codes meaning would require knowing what version of windows we are running on :-( */
  InitializeCriticalSectionAndSpinCount(lock, 2000);
  return 0;
}

int try_yices_lock(yices_lock_t* lock){
  if (TryEnterCriticalSection(lock) != 0) {
    return 0;
  }
  return 1;
}


int get_yices_lock(yices_lock_t* lock){
  /* void return type */
  EnterCriticalSection(lock);
  return 0;
}

int release_yices_lock(yices_lock_t* lock){
  /* void return type */
  LeaveCriticalSection(lock);
  return 0;
}

void destroy_yices_lock(yices_lock_t* lock){
  /* void return type */
  DeleteCriticalSection(lock);
}
