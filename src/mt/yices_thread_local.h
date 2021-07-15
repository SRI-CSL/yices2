/*
 * Thread Local State
 *
 * THREAD_SAFE implies that we HAVE_TLS
 *
 */
#ifdef THREAD_SAFE
/*
 * Generic thread local
 */
#define YICES_THREAD_LOCAL __thread
/*
 * Specific to PER_THREAD_STATE
 */
#ifdef PER_THREAD_STATE
#define YICES_PTS_LOCAL __thread
#else
#define YICES_PTS_LOCAL
#endif
#else
#define YICES_THREAD_LOCAL
#endif


