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
 * Two main components process the sequence of tokens:
 * - a scan component assign a formatting mode to each block
 *   (based on the available display area)
 * - a print component formats the blocks and token according
 *   to the specified layout mode.
 */

#ifndef __PRETTY_PRINTER_H
#define __PRETTY_PRINTER_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>


/*
 * TOKENS
 */

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
 *
 * We also add a free_token function called when the token is no longer
 * needed by the pretty printer.
 */
typedef char *(*get_label_fun_t)(void *ptr, pp_token_t *tk);
typedef char *(*get_string_fun_t)(void *ptr, pp_token_t *tk);
typedef char *(*get_truncated_fun_t)(void *ptr, pp_token_t *tk, uint32_t n);
typedef void (*free_token_fun_t)(void *ptr, pp_token_t *tk);


/*
 * Token converter: include the aux ptr + the conversion
 * functions + free token function.
 */
typedef struct pp_token_converter_s {
  void *user_ptr;
  get_label_fun_t get_label;
  get_string_fun_t get_string;
  get_truncated_fun_t get_truncated;
  free_token_fun_t free_token;
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



/*
 * PRINTER
 */

/*
 * The display area is a rectangle characterized by
 * its width, height, and offset as follows:
 * 
 *                  <----------- width ------------->
 *                   _______________________________   
 * <---- offset --->|                               |   |
 *                  |                               |   |
 *                  |                               | Height
 *                  |                               |   |
 *                  |                               |   |
 *                   -------------------------------
 *
 * The printer keeps track of the current cursor location
 * inside the rectangle using its coordinate:
 * - col = column location (0 <= col < with)
 * - line = current line location (0 <= line < height)
 * The top left corner of the rectangle has coordinate (0, 0).
 *
 * In addition, the printer uses a stack to keep the layout mode
 * and the indentation used by current block (indent 0 means left of
 * the rectangle) + a boolean flag to specify whether a separator is
 * needed before the next atom or block is printed.
 *
 * The printer also stores the number of closing parentheses required
 * (which is equal to the the number of blocks currently open) and
 * makes sure there's enough space at the bottom and right hand corner
 * of the rectangle to print all the closing parentheses. We keep
 * track of the reserved area using
 * - last_line = last line currently avaible for printing
 * - reserved_colums = space required for the closing parentheses 
 *   at the end of the last_line.
 *
 * We maintain the invariants:
 *   0 <= line <= last_line < height
 *   0 <= reserved_columns < width
 *   close_pars = width * (heigh - last_line - 1) + reserved_columns
 *   indent <= col < width
 *   line = last_line => col < width - reserved_columns
 *
 * Options for dealing with text that can't fit in the display area:
 * - strict (default):
 *   if an atomic token doesn't fit on the current line: truncate it
 *   if a block doesn't fit: replace it by '...' (and don't print anything
 *   more until we exit from the enclosing block).
 * - relax:
 *   allow atomic token to extend beyoind the right of the rectangle (never
 *   truncate them)
 *   blocks that don't fit are treated as in stric mode (print '...' etc.)
 * - stretch:
 *   In this mode, the current line is always of size 'width' no matter
 *   the indentation level (both atomic tokens and non-atomic blocks may 
 *   extend to the right of the rectangle).
 *
 * We store these options via two flags:
 * - truncate: truncate atomic tokens that don't fit
 * - stretch: strectch the current line beyond the width
 */

/*
 * the mode word contains the format_mode (in its low-order bits)
 * then a single bit to specify whether a separator is required
 */
typedef struct pp_print_mode_s {
  uint32_t mode;
  uint32_t indent;
} pp_print_mode_t;




/*
 * Stack: print modes are stored in data[0 ... top]
 * - size is the total size of the array data
 * - the bottom element data[0] is the initial 
 *   printing mode.
 * - by default this is (horizontal layout, indent = 0, no separator)
 */
typedef struct pp_printer_stack_s {
  pp_print_mode_t *data;
  uint32_t top;
  uint32_t size;
} pp_printer_stack_t;


// default and maximal size of the stack
#define DEF_PP_PRINTER_STACK_SIZE 20
#define MAX_PP_PRINTER_STACK_SIZE (UINT32_MAX/sizeof(pp_print_mode_t))


/*
 * Display area
 */
typedef struct pp_display_area_s {
  // dimension + offset
  uint32_t width;
  uint32_t height;
  uint32_t offset;
  // cursor location
  uint32_t col;
  uint32_t line;
  // space reserved for the closing 
  // parentheses
  uint32_t last_line;
  uint32_t reserved_columns;
} pp_display_area_t;


/*
 * Printer object
 */
typedef struct pp_printer_s {
  /*
   * Main components: area + stack
   */
  pp_display_area_t area;
  pp_printer_stack_t stack;

  /*
   * Options + number of closing parentheses
   */
  uint32_t options;
  uint32_t closing_pars;

  /*
   * Overfull: set when the current line is full
   */
  bool overfull;

  /*
   * Special case for truncation:
   * - if there's room for tk + another element of small size 
   *   but there's not enough space for tk + ellipsis, then 
   *   we can't decide yet whether tk should be truncated or not.
   *   (We need to see the token that follows tk).
   * To deal with this case, we save tk here as a pending token.
   */
  pp_token_t *pending_token;


  /*
   * Token converter + output stream
   */
  pp_token_converter_t converter;
  FILE *stream;

} pp_printer_t;



/*
 * Option flags
 */
#define PP_TRUNCATE_OPTION ((uint32_t) 1)
#define PP_STRETCH_OPTION  ((uint32_t) 2)


/*
 * Minimal width and height
 */
#define PP_MINIMAL_WIDTH  3
#define PP_MIMIMAL_HEIGHT 1


/*
 * Default print area:
 * - 80 columns
 * - infinitely many lines
 * - no offest
 */
#define PP_DEFAULT_WIDTH  80
#define PP_DEFAULT_HEIGHT UINT32_MAX
#define PP_DEFAULT_OFFSET 0



/*
 * PRINTER INTERFACE
 */

/*
 * Initialization:
 * - converter = converter interface (this
 *   is copied into pp_printer->converter).
 * - file = output stream to use (must be an open file)
 *
 * The printer is initialized with default width, height,
 * and offset. The other settings are
 *    horizontal mode, indent = 0
 *    truncate enabled
 *    strech disable
 */
extern void init_pp_printer(pp_printer_t *pp, pp_token_converter_t *converter, FILE *file);


/*
 * Change parameters: 
 * - these functions should be called before anything is printed.
 * - width must be at least PP_MINIMAL_WIDTH
 * - height must be at least PP_MINIMAL_HEIGHT
 * - indent must be less than ??
 */
extern void pp_printer_set_width(pp_printer_t *pp, uint32_t width);
extern void pp_printer_set_height(pp_printer_t *pp, uint32_t height);
extern void pp_printer_set_offset(pp_printer_t *pp, uint32_t offset);
extern void pp_printer_set_mode(pp_printer_t *pp, pp_layout_mode_t mode);
extern void pp_printer_set_indent(pp_printer_t *pp, uint32_t indent);


/*
 * Change options
 */
static inline void pp_printer_enable_truncate(pp_printer_t *pp) {
  pp->options &= ~PP_TRUNCATE_OPTION;
}

static inline void pp_printer_disable_truncate(pp_printer_t *pp) {
  pp->options |= PP_TRUNCATE_OPTION;
}

static inline void pp_printer_enable_stretch(pp_printer_t *pp) {
  pp->options |= PP_STRETCH_OPTION;
}

static inline void pp_printer_disable_stretch(pp_printer_t *pp) {
  pp->options &= ~PP_STRETCH_OPTION;
}



/*
 * Process token tk
 * - if tk is an atomic token:
 *   print a separator if required then print the token
 * - if tk is an open_block token, print a separator if required
 *   , push the new mode + indent specified by tk,
 *   print an opening '(' followed by tk's label if any.
 * - if tk is close_block, restore the previous mode from the stack
 *   (the stack must not be empty).
 *
 * - tk must be understood by pp's converter
 * - for an open_block, tk's size is interpreted as a lower bound
 *   on the block's width. The block is assumed to fit on the
 *   current line if tk's size is no more than the space left on the line.
 */
extern void pp_print_token(pp_printer_t *pp, pp_token_t *tk);


/*
 * Flush the printer: print all the closing parentheses required
 * and pop all the modes from the stack (until we're back to level 0).
 */
extern void flush_pp_printer(pp_printer_t *pp);


/*
 * Delete the printer:
 */
extern void delete_pp_printer(pp_printer_t *pp);


#endif /* __PRETTY_PRINTER_H */
