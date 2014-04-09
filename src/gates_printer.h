/*
 * PRINT BOOLEAN GATE STRUCTURES
 */

#ifndef __GATES_PRINTER_H
#define __GATES_PRINTER_H

#include <stdio.h>

#include "gates_hash_table.h"

extern void print_boolgate(FILE *f, boolgate_t *g);
extern void print_boolgate_list(FILE *f, lnkgate_t *list);
extern void print_boolgate_levlist(FILE *f, levlist_t *lv);
extern void print_gate_table_stack(FILE *f, gate_table_t *tbl);
extern void print_gate_table_htbl(FILE *f, gate_table_t *tbl);
extern void print_gate_table(FILE *f, gate_table_t *tbl);

#endif /* __GATES_PRINTER_H */
