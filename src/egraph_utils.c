/*
 * UTILITIES: ACCESS TO INTERNAL EGRAPH STRUCTURES
 */

#include "int_hash_map.h"
#include "egraph_utils.h"

/*
 * Allocate and initialize the internal imap
 */
void egraph_alloc_imap(egraph_t *egraph) {
  assert(egraph->imap == NULL);
  egraph->imap = (int_hmap_t *) safe_malloc(sizeof(int_hmap_t));
  init_int_hmap(egraph->imap, 0);
}
