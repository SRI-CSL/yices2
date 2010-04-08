/*
 * We combine 32indices with a polarity bit to represent positive 
 * and negative occurrences of a term t. This is used for encoding
 * boolean negation efficiently. If t is a boolean term, then
 * pos_occ(t) means t
 * neg_occ(t) means (not t).
 *
 * We encode the polarity bit as the low-order bit of 32bit signed 
 * integers. Negative numbers are error indicators. This encoding
 * is used in several places. Utility function to manipulate term
 * indices and term occurrences are defined here.
 */

#ifndef __TERM_OCCURRENCES_H
#define __TERM_OCCURRENCES_H

#include <stdint.h>
#include <stdbool.h>
#include <assert.h>




#endif /* __TERM_OCCURRENCES_H */
