/*
 * PRETTY PRINTER
 *
 * This is based on "Pretty Printing", Oppen, 1979.
 *
 * The input to the pretty printer is a sequence of
 * tokens, that contains atomic tokens + block delimiters.
 * - Atomic tokens are strings to be printed. They should not 
 *   contain line breaks or start or end with spaces.
 * - A block is a sequence of tokens of the form 
 *
 *      open_block token .... token close_block 
 *  
 * The open_block specifies how this block should be displayed.
 *
 * We use two types of 'open_blocks':
 * - labeled blocks have a 'label' attribute and 
 *   are printed in one of the following formats:
 *
 *      (label b_1 .... b_n)   Horizontal mode
 *
 *      (label b_1             Vertical mode
 *             b_2
 *             ...
 *             b_n)
 * 
 *      (label b_1 ....        Mixed HV mode
 *             b_k .... b_n)
 *
 *      (label                 Tight Vertical mode
 *        b_1
 *        b_2
 *        ...
 *        b_n)
 *
 *   For the first three modes, the block components b_1 ... b_n
 *   are printed on one line (i.e., if b_i is itself a block,
 *   it's printed in Horizontal mode).
 *   
 * - unlabeled blocks have no label. They are printed as
 *   labeled blocks with empty labels, except in Tight Vertical
 *   mode, where we save one line:
 *
 *     (b_1
 *      b_1
 *      ...
 *      b_n)
 *
 *
 */

#ifndef __PRETTY_PRINTER_H
#define __PRETTY_PRINTER_H

#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

/*
 * Four token types (can be stored in two bits b1 b0)
 * - we must make sure b1 = 0 for ATOMIC/CLOSE
 *   and b1 = 1 for both OPEN types
 */
typedef enum { 
  PP_ATOMIC,
  PP_CLOSE,
  PP_OPEN_LABELED,
  PP_OPEN_UNLABELED,
} pp_token_type_t;


/*
 * Four layout modes
 */
typedef enum {
  PP_HORIZONTAL,
  PP_VERTICAL,
  PP_MIXED_HV,
  PP_TIGHT,
} pp_layout_mode_t;



/*
 * Token descriptor
 * - header: encodes the type + other parameters
 * - size: 
 *   - for an atomic token, this must be 
 *     the number of character required to print it.
 *   - for an open token, this is used to
 *     compute a lower bound on the block width.
 *   - not used for close token (always 0)
 * - label_size: only used for open_labeled tokens
 *   this must be the size of the label.
 * - indent: indentation for use in Tight Vertical mode.
 *   (used only for the open tokens).
 *
 * The pretty printer requires several user-provided functions to
 * convert tokens to string. To help in this conversion, each token
 * has a user_tag, which must be set when the token is created.
 */
typedef struct pp_token_s {
  uint32_t header;
  int32_t size;
  uint16_t label_size;
  uint32_t indent;
  int32_t user_tag;
} pp_token_t;



/*
 * Conversion functions:
 * - get_label(ptr, tk): label of an open-labeled token tk
 * - get_string(ptr, tk): convert atomic token tk to a string.
 * - get_truncated(ptr, tk, n): convert atomic token tk to a 
 *   string of length <= n (where n < tk->size).
 *
 * All conversions take a generic user-provided pointer as first 
 * argument and must return character string (terminated by '\0').
 *
 * For consistency, 
 * - get_label(ptr, tk) should return a string of length equal to tk->label_size
 * - get_string(ptr, tk) should return a string of length equal to tk->size
 */
typedef char *(*get_label_fun_t)(void *ptr, pp_token_t *tk);
typedef char *(*get_string_fun_t)(void *ptr, pp_token_t *tk);
typedef char *(*get_truncated_fun_t)(void *ptr, pp_token_t *tk, uint32_t n);



/*
 * Token converter: include the aux ptr + the conversion
 * functions.
 */
typedef struct pp_token_converter_s {
  void *user_ptr;
  get_label_fun_t get_label;
  get_string_fun_t get_string;
  get_truncated_fun_t get_truncated;
} pp_token_converter_t;



/*
 * Header fields:
 * - two low-order bits contain the token type
 * - one bit encodes whether this is the last atomic token
 *   or last block in the enclosing block.
 * - one bit per format mode
 *
 * When an open token is created, the format bits of a open token
 * indicates which formats are allowed for the block. The pretty
 * printer will then attempt to select an appropriate format among
 * these depending on the block components and size of the print area.
 * In order of preference, the pretty printer will use horizontal mode
 * if possible, then either vert or mixed mode, then tight mode.
 *
 * When an open token is printed, the format bits define the
 * format to use for the correspondin block. There should be only
 * one bit set at that point.
 *
 * Bit masks
 * - 0000011: select the type
 * - 0000100: select the lbit
 * - 1111000: select the format
 * Type encoded in the lowest order bits
 *   00: atomic token
 *   01: close block
 *   10: open labeled block
 *   11: open unlabeeld block
 * Formatting bits: next four bits
 * - 0001000: horizontal mode
 * - 0010000: vertical mode
 * - 0100000: mixed horizontal/vertical mode
 * - 1000000: thight vertical mode
 */
#define PP_TOKEN_TYPE_MASK ((uint32_t) 3)
#define PP_TOKEN_LBIT_MASK ((uint32_t) 4)

#define PP_TOKEN_FORMAT_MASK ((uint32_t) 120)

// select bit1
#define PP_OPEN_MASK  ((uint32_t) 2)

#define PP_HMODE_MASK ((uint32_t) 8)
#define PP_VMODE_MASK ((uint32_t) 16)
#define PP_MMODE_MASK ((uint32_t) 32)
#define PP_TMODE_MASK ((uint32_t) 64)



/*
 * Build the header:
 * - type = token type
 * - lbit = last block indicator (must be either 0b100 or 0b00)
 * - formats = which formats are allowed
 */
static inline uint32_t tk_header(uint32_t type, uint32_t lbit, uint32_t formats) {
  assert((type & ~PP_TOKEN_TYPE_MASK) == 0 &&
	 (lbit & ~PP_TOKEN_LBIT_MASK) == 0 &&
	 (formats & ~PP_TMODE_MASK) == 0);
  return type|lbit|formats;
}


/*
 * Header components
 */
// token type
static inline pp_token_type_t tk_type(pp_token_t *tk) {
  return (pp_token_type_t) (tk->header & PP_TOKEN_TYPE_MASK);
}

static inline bool tk_is_atomic(pp_token_t *tk) {
  return tk_type(tk) == PP_ATOMIC;
}

static inline bool tk_is_close(pp_token_t *tk) {
  return tk_type(tk) == PP_CLOSE;
}

static inline bool tk_is_open_labeled(pp_token_t *tk) {
  return tk_type(tk) == PP_OPEN_LABELED;
}

static inline bool tk_is_open_unlabeled(pp_token_t *tk) {
  return tk_type(tk) == PP_OPEN_UNLABELED;
}

static inline bool tk_is_open(pp_token_t *tk) {
  return (tk->header & PP_OPEN_MASK) != 0;
}

// test the lbit
static inline bool tk_is_last(pp_token_t *tk) {
  return (tk->header & PP_TOKEN_LBIT_MASK) != 0;
}


// format bits
static inline bool tk_has_hmode(pp_token_t *tk) {
  return (tk->header & PP_HMODE_MASK) != 0;
}

static inline bool tk_has_vmode(pp_token_t *tk) {
  return (tk->header & PP_VMODE_MASK) != 0;
}

static inline bool tk_has_mmode(pp_token_t *tk) {
  return (tk->header & PP_HMODE_MASK) != 0;
}

static inline bool tk_has_tmode(pp_token_t *tk) {
  return (tk->header & PP_TMODE_MASK) != 0;
}


#endif /* __PRETTY_PRINTER_H */
