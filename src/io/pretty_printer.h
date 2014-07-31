/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRETTY PRINTER
 *
 * This is based on "Pretty Printing", Oppen, 1979.
 *
 * The input to the pretty printer is a sequence of
 * tokens, that contains atomic tokens + block delimiters.
 * - Atomic tokens are strings to be printed. They should not
 *   contain line breaks, or start or end with spaces.
 * - A block is a sequence of tokens of the form
 *
 *      open_block token .... token close_block
 *
 * An open-block has the following attributes:
 * - label = string to be printed at the start of the block (may be empty)
 * - whether the block is enclosed by '(' and ')'
 * - whether a space or line break is allowed between the label and the
 *   next text element
 * - a set of possible formats for that block. There are four
 *   choices: horizontal, vertical, mixed, tight.
 * - the indentation for mixed and vertical formats
 * - the (shorter) indentation for the tight format
 *
 * The possible formats are
 *
 *      (label b_1 .... b_n)   Horizontal layout
 *
 *      (label b_1             Vertical layout
 *             b_2
 *             ...
 *             b_n)
 *
 *      (label b_1 ....        Mixed HV layout
 *             b_k .... b_n)
 *
 *      (label                 Tight layout
 *         b_1
 *         b_2
 *         ...
 *         b_n)
 *
 * There are constraints between the selected layout for a block and the
 * allowed layouts for its sub-blocks:
 * - if b is printed horizontally, then all its sub-blocks must also be
 *   printed horizontally
 * - if b is printed in vertical or mixed layouts, then all
 *   its sub-blocks must be printed horizontally
 *
 * As in Oppen's paper the pretty printer consists of two main components
 * - a printer does the actual printing.
 * - a formatter computes the size of each block (or a lower bound that's
 *   larger than the current line width) and feeds that information to
 *   the printer.
 */

#ifndef __PRETTY_PRINTER_H
#define __PRETTY_PRINTER_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>

#include "utils/tagged_pointers.h"
#include "utils/ptr_vectors.h"
#include "utils/ptr_queues.h"


/*
 * LAYOUTS
 */

/*
 * Bit masks to represent a set of layouts
 * (in the low-order bits of an unsigned int).
 * - 0001: horizontal
 * - 0010: mixed horizontal/vertical
 * - 0100: vertical
 * - 1000: tight vertical
 */
#define PP_H_LAYOUT ((uint32_t) 1)
#define PP_M_LAYOUT ((uint32_t) 2)
#define PP_V_LAYOUT ((uint32_t) 4)
#define PP_T_LAYOUT ((uint32_t) 8)


/*
 * Possible combinations of two or three layouts
 */
#define PP_HM_LAYOUT  (PP_H_LAYOUT|PP_M_LAYOUT)
#define PP_HV_LAYOUT  (PP_H_LAYOUT|PP_V_LAYOUT)
#define PP_HT_LAYOUT  (PP_H_LAYOUT|PP_T_LAYOUT)
#define PP_MT_LAYOUT  (PP_M_LAYOUT|PP_T_LAYOUT)
#define PP_VT_LAYOUT  (PP_V_LAYOUT|PP_T_LAYOUT)
#define PP_HMT_LAYOUT (PP_H_LAYOUT|PP_M_LAYOUT|PP_T_LAYOUT)
#define PP_HVT_LAYOUT (PP_H_LAYOUT|PP_V_LAYOUT|PP_T_LAYOUT)


/*
 * DISPLAY AREA
 */

/*
 * The display area is a rectangle characterized by
 * its width, height, and offset as follows:
 *
 *                  <----------- width ------------->
 *                   _______________________________
 * <---- offset --->|                               |   ^
 *                  |                               |   |
 *                  |                               | Height
 *                  |                               |   |
 *                  |                               |   v
 *                   -------------------------------
 *
 *
 * The printer keeps track of the current print line within that area.
 * The start of each line is defined by its indentation (measured from
 * the first column of the rectangle).
 *
 * By default, each line has enough space for (width - indent) characters.
 * There's a 'stretch' option that can be used to make the lines wider.
 * If stretch is true, then each line extends to the right and has
 * space for 'width' characters independent of 'indent'.
 *
 * A 'truncate' flag specifies how to deal with an atomic token that does
 * not fit on the print line (e.g., if the indentation is large):
 * - if 'truncate' is true, the token is truncated (nothing is printed
 * beyond the display area's boundary).
 * - otherwise, the token is printed in full and may extend beyond the
 *   right boundary.
 */
typedef struct pp_area_s {
  uint32_t width;
  uint32_t height;
  uint32_t offset;
  bool stretch;
  bool truncate;
} pp_area_t;


/*
 * Minimal width and height
 */
#define PP_MINIMAL_WIDTH  4
#define PP_MINIMAL_HEIGHT 1

/*
 * Default print area:
 * - 80 columns
 * - infinitely many lines
 * - no offset
 * - stretch disabled
 * - truncate enabled
 */
#define PP_DEFAULT_WIDTH  80
#define PP_DEFAULT_HEIGHT UINT32_MAX
#define PP_DEFAULT_OFFSET 0
#define PP_DEFAULT_STRETCH false
#define PP_DEFAULT_TRUNCATE true



/*
 * TOKENS
 */

/*
 * Token descriptors encode formatting information.  The string label
 * of an open token or the content of an atomic token are not kept in
 * the descriptor. They are obtained via calls to user-provided
 * functions.  To help in this conversion, the descriptors include a
 * 32bit user-tag (which can be anything the conversion functions need
 * to identify the token).
 */

/*
 * Atomic token descriptor
 * - size = size of the token when converted to string
 * - bsize = block size = size of the token + number of closing parentheses
 *   that follow it.
 *
 * Size and user_tag should be set appropriately when the token is created.
 * bsize is computed by the formatter.
 */
typedef struct pp_atomic_token_s {
  uint32_t bsize;
  uint32_t size;
  uint32_t user_tag;
} pp_atomic_token_t;


/*
 * Open block descriptor
 * - bsize = block size = size of the block + number of closing
 *           parentheses that follow it.
 * - csize = maximal block size of the sub-blocks and atoms in that block
 * - fsize = block size of the first sub-block or atom
 *
 * - label_size = size of the label (0 if there's no label)
 * - indent = indentation for VLAYOUT or MLAYOUT
 * - short_indent = indentation for TLAYOUT
 * - formats = allowed formats
 * - flags = whether the block is enclosed with '(' and ')
 *           whether space/break is allowed after the label
 * - user_tag = provided by the user
 *
 * The fields bsize, csize, and fsize are computed by the formatter.
 * All the other components must be set when the token is created.
 */
typedef struct pp_open_token_s {
  uint32_t bsize;
  uint32_t csize;
  uint32_t fsize;
  uint8_t  formats;
  uint8_t  flags;
  uint16_t label_size;
  uint16_t indent;
  uint16_t short_indent;
  uint32_t user_tag;
} pp_open_token_t;


/*
 * bit masks for the flag field:
 *  b0 --> 1 for blocks that require '(' and ')
 *         0 for blocks with no delimiters
 *  b1 --> 1 if space/break is allowed after the label
 *         0 otherwise
 */
#define PP_TOKEN_PAR_MASK ((uint32_t) 0x1)
#define PP_TOKEN_SEP_MASK ((uint32_t) 0x2)

/*
 * Test the format bits
 */
static inline bool tk_has_hlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_H_LAYOUT) != 0;
}

static inline bool tk_has_mlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_M_LAYOUT) != 0;
}

static inline bool tk_has_vlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_V_LAYOUT) != 0;
}

static inline bool tk_has_tlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_T_LAYOUT) != 0;
}

/*
 * Test the flags
 */
static inline bool tk_has_par(pp_open_token_t *tk) {
  return (tk->flags & PP_TOKEN_PAR_MASK) != 0;
}

static inline bool tk_sep_allowed(pp_open_token_t *tk) {
  return (tk->flags & PP_TOKEN_SEP_MASK) != 0;
}


/*
 * Close block descriptor.
 * - we just need to know whether the block ends with ')'
 * - we use the same flags encoding as for open_blocks
 */
typedef struct pp_close_token_s {
  uint32_t flags;
  uint32_t user_tag;
} pp_close_token_t;

/*
 * Check the flag
 */
static inline bool tk_has_close_par(pp_close_token_t *tk) {
  return (tk->flags && PP_TOKEN_PAR_MASK) != 0;
}



/*
 * Large bsize: when we know that a token or block doesn't
 * fit on the line, we can set its bsize field to any large
 * enough number. We use the constant 2^30.
 */
#define PP_MAX_BSIZE ((uint32_t) 1073741824)



/*
 * TAGGED POINTERS
 */

/*
 * Tokens are accessed via tagged (void *) pointers
 * The token type is encoded in the lower 2bits:
 * 00 --> open token
 * 01 --> atomic token
 * 10 --> close token
 * 11 --> separator token
 *
 * A separator is an atomic token that's printed without
 * spaces before or after.
 */
typedef enum {
  PP_TOKEN_OPEN_TAG,
  PP_TOKEN_ATOMIC_TAG,
  PP_TOKEN_CLOSE_TAG,
  PP_TOKEN_SEPARATOR_TAG,
} pp_tk_ptr_tag;

// check the pointer type
static inline bool ptr_has_open_tag(void *p) {
  return ptr_tag(p) == PP_TOKEN_OPEN_TAG;
}

static inline bool ptr_has_atomic_tag(void *p) {
  return ptr_tag(p) == PP_TOKEN_ATOMIC_TAG;
}

static inline bool ptr_has_close_tag(void *p) {
  return ptr_tag(p) == PP_TOKEN_CLOSE_TAG;
}

static inline bool ptr_has_separator_tag(void *p) {
  return ptr_tag(p) == PP_TOKEN_SEPARATOR_TAG;
}

// add a tag to a pointer
static inline void *tag_open(pp_open_token_t *p) {
  return tag_ptr(p, PP_TOKEN_OPEN_TAG);
}

static inline void *tag_atomic(pp_atomic_token_t *p) {
  return tag_ptr(p, PP_TOKEN_ATOMIC_TAG);
}

static inline void *tag_close(void *p) {
  return tag_ptr(p, PP_TOKEN_CLOSE_TAG);
}

static inline void *tag_separator(pp_atomic_token_t *p) {
  return tag_ptr(p, PP_TOKEN_SEPARATOR_TAG);
}

// check and untag
static inline pp_open_token_t *untag_open(void *p) {
  assert(ptr_has_open_tag(p));
  return untag_ptr(p);
}

static inline pp_atomic_token_t *untag_atomic(void *p) {
  assert(ptr_has_atomic_tag(p));
  return untag_ptr(p);
}

static inline void *untag_close(void *p) {
  assert(ptr_has_close_tag(p));
  return untag_ptr(p);
}

static inline pp_atomic_token_t *untag_separator(void *p) {
  assert(ptr_has_separator_tag(p));
  return untag_ptr(p);
}


/*
 * The pretty printer requires several user-provided functions to
 * convert tokens to string. To help in this conversion, each token
 * has a user_tag, which must be set when the token is created.
 *
 * Conversion functions:
 * - get_label(ptr, tk): label of an open-block token tk
 * - get_string(ptr, tk): convert atomic token tk to a string.
 * - get_truncated(ptr, tk, n): convert atomic token tk to a
 *   string of length <= n (where n < tk->size).
 *
 * All the conversions take a generic user-provided pointer as first
 * argument and must return character string (terminated by '\0').
 * For consistency,
 * - get_label(ptr, tk) should return a string of length equal to tk->label_size.
 * - get_string(ptr, tk) should return a string of length equal to tk->size.
 *
 * Free functions: when token tk is consumed, one of the
 * following function is called.
 * - free_open_token(ptr, tk)
 * - free_atomic_token(ptr, tk)
 * - free_close_token(ptr, tk)
 * The first argument 'ptr' is the same user-provided pointer as used
 * by the conversion functions.
 *
 * All functions and the user-provided pointer are stored in a
 * 'pp_token_converter' structure.
 */
typedef char *(*get_label_fun_t)(void *ptr, pp_open_token_t *tk);
typedef char *(*get_string_fun_t)(void *ptr, pp_atomic_token_t *tk);
typedef char *(*get_truncated_fun_t)(void *ptr, pp_atomic_token_t *tk, uint32_t n);

typedef void (*free_open_token_fun_t)(void *ptr, pp_open_token_t *tk);
typedef void (*free_atomic_token_fun_t)(void *ptr, pp_atomic_token_t *tk);
typedef void (*free_close_token_fun_t)(void *ptr, pp_close_token_t *tk);

typedef struct pp_token_converter_s {
  void *user_ptr;
  get_label_fun_t get_label;
  get_string_fun_t get_string;
  get_truncated_fun_t get_truncated;
  free_open_token_fun_t free_open_token;
  free_atomic_token_fun_t free_atomic_token;
  free_close_token_fun_t free_close_token;
} pp_token_converter_t;



/*
 * PRINTER
 */

/*
 * There are three possible print modes:
 * - HMODE: horizontal, with space as separator
 * - VMODE: vertical, with a specified indentation
 * - HVMODE: mix of both.
 *
 * If a new atom 's' is to be printed:
 * - in HMODE: print a space then print s
 * - in VMODE: print a line break, indent, then print s
 * - in HVMODE: check whether s fits on the current line
 *   if yes, print a space then print s
 *   if no, print a line break, indent, print s.
 *
 * There's an immediate correspondence between layouts
 * and print modes:
 * - HLAYOUT --> HMODE
 * - VLAYOUT and TLAYOUT --> VMODE
 */
typedef enum {
  PP_HMODE,
  PP_VMODE,
  PP_HVMODE,
} pp_print_mode_t;


/*
 * A print state keeps track of the current print mode
 * and indentation. States are stored on a stack.
 */
typedef struct pp_state_s {
  pp_print_mode_t mode;
  uint32_t indent; // indent increment
} pp_state_t;


/*
 * Stack:
 * - print states are stored in data[0 ... top]
 * - size is the total size of the array data
 * - the current state is in data[top]
 * - the bottom element data[0] is the initial printing mode.
 * - by default this is (horizontal mode, indent = 0,)
 */
typedef struct pp_stack_s {
  pp_state_t *data;
  uint32_t top;
  uint32_t size;
} pp_stack_t;

// default and maximal size of the stack
#define DEF_PP_STACK_SIZE 20
#define MAX_PP_STACK_SIZE (UINT32_MAX/sizeof(pp_state_t))


/*
 * The printer is attached to an output file, to a converter
 * structure, and to a display area.
 *
 * It keeps track of a current print-line, defined by
 * - line = line number (0 means top of the display area)
 * - col = cursor location
 * - margin = end of the line
 *
 * When we get close to the end of the line, the printer
 * may have to store pending tokens (that fit on the line
 * but can't be printed for sure yet because '...' may be needed).
 * These tokens are stored in a 'pending_token' vector and
 * the printer keeps track of the column where they will be
 * printed if possible in 'pending_col'.
 *
 * The printer also use control parameters:
 * - stack = stack of printer states
 * - mode = current print mode (copied from the stack top)
 * - indent = current indentation
 * - next_margin = margin to use after the following line break
 *               = width of the next line
 * - no_break = true to prevent line break
 * - no_space = true to prevent space
 * - full_line = true if the current line is full
 * - overfull_count = number of open blocks seen since the line has been full
 */
typedef struct printer_s {
  // output file + display area + converter
  FILE *file;
  pp_area_t area;
  pp_token_converter_t conv;

  // control parameters
  pp_stack_t stack;
  pp_print_mode_t mode;
  uint32_t indent;
  uint32_t next_margin;
  bool no_break;
  bool no_space;
  bool full_line;
  uint32_t overfull_count;

  // current print line
  uint32_t line;
  uint32_t col;
  uint32_t margin;

  // if fputc, fputs, or fflush fails, we set print_failed to true
  // and we keep a copy of errno in p->pp_errno
  bool print_failed;
  int pp_errno;

  // pending tokens
  pvector_t pending_tokens;
  uint32_t pending_col;
} printer_t;




/*
 * FORMATTER
 */

/*
 * The formatter looks ahead in the token stream to compute
 * - the bsize of all atomic tokens
 * - the bsize and csize of all open tokens
 *
 * The formatter works as if all the tokens were printed on
 * a single (long) horizontal line (the formatting line).
 * The formatter state includes:
 *
 * 1) A queue of tokens.
 *    - input tokens are added to this queue
 *    - they are removed from the queue when their bsize
 *      is known or as soon as it's known that their bsize is
 *      larger than max_width (= the display area width).
 *
 * 2) A queue of block descriptors. For each block we store:
 *    - a pointer to the corresponding open token descriptor
 *    - the column where the block starts on the formatting line
 *    - the current csize for that block = largest bsize among
 *      its sub-blocks.
 *
 * 3) The formatting line parameters:
 *    - length = size of the line = column where new tokens are added
 *    - no_space = flag that determines whether a space should be
 *                 added before the next token.
 *
 * 4) A optional head_token
 *    - if head_token isn't NULL then it's the start of a block
 *      whose bsize is known to be larger than max_width but
 *      whose fsize and csize fields are not known yet.
 *
 * 5) An optional last_atom
 *    - if last_atom isn't NULL then it's the last atomic token
 *      on the line and that token is followed by nothing or
 *      by closed parentheses
 *    - if last_atom != NULL then atom_col is the start of the
 *      atom on the line
 *
 *
 * Note: we could send tokens to the printer as soon as we know that
 * bsize is larger than the space left on the printer's line, but that
 * complicates the code.
 *
 *
 * The formatting line looks (approximately) like this:
 *
 *                                                             length
 * ______________________________________________________________|__
 *  |Head    |B0            |B1         | .... |B_n   ... atom)))|
 * --------------------------------------------------------------|--
 *  ^        ^              ^                  ^          ^
 * head    col_0         col_1              col_n        atom_col
 *
 *
 * The following invariants hold:
 * 1) head_token->bsize > max_width
 *    head_token->fsize <= head_token->csize <= max_width
 *    head_token->fsize = head_token->csize = 0 if B0 is
 *    the first sub block of the head block.
 *
 * 2) length - col_i <= max_width
 *    token_i->fsize <= token_i->csize <= max_width
 *    token_i->fsize = token_i->csize is 0 if B_i+1 is
 *    the first sub-block of B_i
 *   (or, for i=n, if the last_atom is the first component of B_n).
 */

/*
 * Block descriptor:
 * - col = start of the block on the formatting line
 * - token = attached open_token descriptor
 */
typedef struct pp_block_s {
  uint32_t col;
  pp_open_token_t *token;
} pp_block_t;


/*
 * Queue of block descriptor (same implementation as int_queue
 * and ptr_queue):
 * - data = array elements
 * - size = size of that array
 * - head, tail = array indices between 0 and size-1
 * This forms a list of block descriptors as follows:
 * - head = tail --> the queue is empty
 * - head < tail --> the queue is data[head ... tail-1]
 * - head > tail --> the queue is data[head ... size-1]
 *                   followed by  data[0 ... tail-1]
 */
typedef struct pp_block_queue_s {
  pp_block_t *data;
  uint32_t size;
  uint32_t head;
  uint32_t tail;
} pp_block_queue_t;


// initial size and maximal size of the queue
#define DEF_BLOCK_QUEUE_SIZE 20
#define MAX_BLOCK_QUEUE_SIZE (UINT32_MAX/sizeof(pp_block_t))


/*
 * Formatter structure:
 * - a pointer to the printer
 * - a queue of tokens (stored as tagged pointers)
 *
 * Block queue:
 * - block_queue = the queue itself
 * - queue_size = number of blocks in the queue
 * - nclosed = number of closed blocks in the queue
 * - head_token = pointer to token starting the enclosing
 *   block (or NULL)
 * - head_closed = true if the head block is close
 *
 * Last atom:
 * - pointer to the last atom in the token queue (or NULL)
 * - atom_col = start of that atom on the line
 *
 * Line descriptors:
 * - no_space: flag to prevent ' '
 * - length = the full length of the line
 * - max_width = maximal block width (any block whose bsize
 *   is known to be more than max_width gets assigned
 *   bsize = MAX_BSIZE).
 *
 * Depth counter:
 * - depth = number of open token seen - number of close token seen
 */
typedef struct formatter_s {
  printer_t *printer;
  ptr_queue_t token_queue;

  // block queue, head token, and related variables
  pp_block_queue_t block_queue;
  uint32_t queue_size;
  uint32_t nclosed;
  pp_open_token_t *head_token;
  bool head_closed;

  // last atom
  pp_atomic_token_t *last_atom;
  uint32_t atom_col;

  // control flag, line size, max_width
  bool no_space;
  uint32_t length;
  uint32_t max_width;

  // depth
  uint32_t depth;
} formatter_t;


/*
 * PRETTY PRINTER
 */
typedef struct pp_s {
  printer_t printer;
  formatter_t formatter;
} pp_t;



/*
 * PRETTY-PRINTER INTERFACE
 */

/*
 * Initialization:
 * - converter = converter interface (copied internally).
 * - file = output stream to use (must be an open, writable file)
 * - area = specify display area + truncate + stretch
 * - mode = initial print mode
 * - indent = initial indentation (increment)
 * If area s is NULL then the default area is used:
 * width = 80, height = infinite, offset = 0, don't stretch, truncate.
 */
extern void init_pp(pp_t *pp, pp_token_converter_t *converter, FILE *file,
                    pp_area_t *area, pp_print_mode_t mode, uint32_t indent);


/*
 * Process token tk.
 */
extern void pp_push_token(pp_t *pp, void *tk);


/*
 * Flush the printer: empty the internal queues and print
 * the pending tokens. Reset the line counter to 0.
 */
extern void flush_pp(pp_t *pp);


/*
 * Delete the printer: free memory.
 * (This may call the free_token functions in pp->converter).
 */
extern void delete_pp(pp_t *pp);


/*
 * Check whether the print area is full
 * - if this is true, it's useless to push new tokens
 * - this also return true if pp->printed_failed is true
 *   (i.e., one of fputs, fputc, or fflush returned an error).
 */
extern bool pp_is_full(pp_t *pp);


/*
 * Get the printer depth = number of open blocks
 */
static inline uint32_t pp_depth(pp_t *pp) {
  return pp->formatter.depth;
}


/*
 * Initialize an open token tk and return the tagged pointer tag_open(tk).
 * - formats = allowed formats for that token (PP_??_LAYOUT)
 * - lsize = label size
 * - indent = indentation for V and M layouts
 * - short_indent = indentation for the T layout
 * - flags = combination of PP_TOKEN_PAR_MASK and PP_TOKEN_SEP_MASK
 * - user_tag = whatever the converter needs
 */
extern void *init_open_token(pp_open_token_t *tk, uint32_t formats, uint32_t flags,
                             uint16_t lsize, uint16_t indent, uint16_t short_indent,
                             uint32_t user_tag);


/*
 * Initialize an atomic token tk and return the tagged pointer tag_atomic(tk).
 * - size = token size (when converted to a string)
 * - user_tag = whatever the converter needs
 */
extern void *init_atomic_token(pp_atomic_token_t *tk, uint32_t size, uint32_t user_tag);

/*
 * Same thing got a separator token tk (return tag_separator(tk))
 * - size = token size when converted to string
 * - user_tag = tag for the converter
 */
extern void *init_separator_token(pp_atomic_token_t *tk, uint32_t size, uint32_t user_tag);


/*
 * Initialize a close token tk and return the tagged pointer tag_close(tk).
 * - par: true if the token contains ')'
 * - user_tag: any thing used by the free_close_token in the converter
 */
extern void *init_close_token(pp_close_token_t *tk, bool par, uint32_t user_tag);




#endif /* __PRETTY_PRINTER_H */
