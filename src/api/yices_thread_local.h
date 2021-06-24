/*
 * Thread Local State
 *
 * THREAD_SAFE implies that we HAVE_TLS
 *
 */
#ifdef THREAD_SAFE
#define YICES_THREAD_LOCAL __thread
#else
#define YICES_THREAD_LOCAL
#endif
