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
 * An open-block has the following attributes:
 * - label = string to be printed at the start of the block (may be empty)
 * - whether the block is enclosed by '(' and ')
 * - whether a space or break is allowed between the label and the next 
 *   text element
 * - a set of possible formats for that block. There are four
 *   choices: horizontal, vertical, mixed, tight
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
 *      (label                 Tight Vertical layout
 *         b_1
 *         b_2
 *         ...
 *         b_n)
 *
 * There are constraints between the selected layout for a block and the
 * allowed layouts for its sublocks:
 * - if b is printed horizontally, then all its subblocks must also be 
 *   printed horizontally
 * - if b is printed in vertical layout or mixed HV layouts, then all
 *   its subblocks must be printed horizontally
 * If b is printed in the tight vertical layout, then there are
 * no constraints on its subblocks.
 *
 * If a line break is not allowed between label and b_1 then Tight Vertical layout will
 * be printed as
 *
 *     (label b_1
 *        ...
 *        b_n)
 *
 * where b_1 may be printed on several lines.
 *
 * As in Oppen's paper the pretty printer consists of two main components
 * - a printer does the actual printing.
 * - a formatter computes the size of blocks, selects a layout for 
 *   each block, and feeds that information to the printer.
 */

#ifndef __PRETTY_PRINTER_H
#define __PRETTY_PRINTER_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <assert.h>

#include "ptr_vectors.h"
#include "ptr_queues.h"


/*
 * LAYOUTS
 */

/*
 * Bit masks to represent a set of layouts
 * (in the low-order bits on an unsigned int).
 * - 0001: horizontal
 * - 0010: vertical
 * - 0100: mixed horizontal/vertical
 * - 1000: thight vertical
 */
#define PP_HLAYOUT_MASK ((uint32_t) 1)
#define PP_VLAYOUT_MASK ((uint32_t) 2)
#define PP_MLAYOUT_MASK ((uint32_t) 4)
#define PP_TLAYOUT_MASK ((uint32_t) 8)





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
 * The printer keeps track of two lines within thar area:
 * - the print line is where text is actually printed
 * - the formatting line is used for deciding how to format
 *   blocks
 * The start of each line is defined by its indentation (measured 
 * from the first column of the rectangle). 
 *
 * By default, each line has enough space for (width - indent) characters. 
 * There's a 'stretch' option that can be used to make the lines wider. If
 * stretch is true, then both the print line and the formatting
 * line have space for (width) characters (i.e., they may stick out 
 * by an extra 'indent' characters from the right of the rectangle).
 *
 * In some cases, an atomic token cannot fit on the print line. The 
 * printer takes an other option that specifies what to do in that case.
 * - if 'truncate' is true, the token is truncated (nothing is printed 
 *   beyond the display area's boundary)
 * - otherwise, atomic tokens are not truncated and may extend beyond the 
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
 * - no offest
 * - strecth disabled
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
 * of an open token or the content of an atomic are not kept in the
 * descriptor. They are obtained via calls to user-provided functions.
 * To help in this conversion, the descriptors include a 32bit user-tag
 * (which can be anything the conversion functions need to identify
 * the token).
 */

/*
 * Atomic token descriptor
 * - size = size of the token when converted to string
 * - bsize = block size = size of the token + number of closing parentheses
 *   that follow it.
 *
 * Size and user_tag should be set appropriately when the token is created.
 * - bsize should be initialied to 0. It is used and updated internally 
 *   by the pretty printer.
 */
typedef struct pp_atomic_token_s {
  uint32_t bsize;
  uint32_t size;
  uint32_t user_tag;
} pp_atomic_token_t;


/*
 * Open block descriptor
 * - bsize = block size = size of the block + number of closing parentheses
 *   taht follow it.
 * - label_size = size of the label (0 if there's no label)
 * - indent = indentation for VLAYOUT or MLAYOUT
 * - short_indent = indentation for TLAYOUT
 * - formats = allowed formats
 * - flags = whether the block is enclosed wih '(' and ')
 *           whether space/break is allowed after the label
 * - user_tag = provided by the user
 *
 * Initially, formats should contain the set of allowed layouts
 * for that block and bsize should be 0. These fields are manipulated
 * internally by the pretty printer. The other fields are not 
 * modified.
 */
typedef struct pp_open_token_s {
  uint32_t bsize;
  uint8_t formats;
  uint8_t flags;
  uint16_t label_size;
  uint16_t indent;
  uint16_t short_indent;
  uint32_t user_tag;
} pp_open_token_t;


/*
 * bit masks for the flag field:
 *  b0 --> 1 for blocks that require '(' and ')
 *         0 for blocks with no delimitors
 *  b1 --> 1 if space/break is allowed after the label
 *         0 otherwise
 */
#define PP_TOKEN_PAR_MASK ((uint32_t) 0x1)
#define PP_TOKEN_SEP_MASK ((uint32_t) 0x2)

/*
 * Test the format bits
 */
static inline bool tk_has_hlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_HLAYOUT_MASK) != 0;
}

static inline bool tk_has_vlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_VLAYOUT_MASK) != 0;
}

static inline bool tk_has_mlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_MLAYOUT_MASK) != 0;
}

static inline bool tk_has_tlayout(pp_open_token_t *tk) {
  return (tk->formats & PP_TLAYOUT_MASK) != 0;
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
 * TAGGED POINTERS
 */

/*
 * Tokens are accessed via tagged (void *) pointers
 * The token type is encoded in the lower 2bits:
 * 00 --> open token
 * 01 --> atomic token
 * 10 --> close token
 */
typedef enum {
  PP_TOKEN_OPEN_TAG,
  PP_TOKEN_ATOMIC_TAG,
  PP_TOKEN_CLOSE_TAG,
} pp_tk_ptr_tag;

#define PTR_TAG_MASK ((size_t) 0x3)

// get the tag of pointer p
static inline uint32_t ptr_tag(void *p) {
  return ((size_t) p) & PTR_TAG_MASK;
}

// untag the pointer
static inline void *untag_ptr(void *p) {
  return (void*)(((size_t) p) & ~PTR_TAG_MASK);
}

// add tag tg to pointer p
static inline void *tag_ptr(void *p, uint32_t tag) {
  assert((tag & ~PTR_TAG_MASK) == 0 && ptr_tag(p) == 0);
  return (void *) (((size_t) p) | (size_t) tag);
}


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
 * All conversions take a generic user-provided pointer as first 
 * argument and must return character string (terminated by '\0').
 *
 * For consistency, 
 * - get_label(ptr, tk) should return a string of length equal to tk->label_size
 * - get_string(ptr, tk) should return a string of length equal to tk->size
 *
 * We also use a free_token functions called when the token is no longer
 * needed by the pretty printer. All functions + the user-provided 
 * pointer are stored in a 'pp_token_converter' structure.
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
 * There's an immediate correspondence between block layouts 
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
 * but can't print for sure yet because '...' may be needed). 
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
 * - overfull_count = number of open blocks seen 
 *    since the line is full.
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

  // pending tokens
  pvector_t pending_tokens;
  uint32_t pending_col;
} printer_t;




/*
 * FORMATTER
 */

/* 
 * The formatter stores a queue of tokens that can't be printed yet.
 * The formatter maintains a provisional layout and computes the size
 * of each tokens. When a new token is added to the queue and doesn't
 * fit in the provisional layout, then a new provisional layout is
 * constructed by chaning the new layout of the outermost open token. 
 *
 * To keep track of the current provisional layout, we use:
 * 1) A queue of block descriptors. For each block we store:
 *    - the corresponding open token
 *    - the column where the block starts on the open line
 *    - the number of closed sub-blocks within that block
 *    We also store the number of closed blocks that are in the queue
 *    (all of them are at the end of the queue).
 *    
 * 2) The description of an open-line, that is, the line where new tokens 
 *    are added in the provisional layout:
 *    - line = its index
 *    - col = where new tokens are added 
 *    - margin = end of that line
 *    - indent = indentation for that line
 *    - no_space = prevent a space before the next token
 *    - no_break = prevent a line break before the next token
 *
 * The open line looks (approximately) like this:
 *
 *   _________________________________________________________
 *  |B0            |B1         | .... |B_n     |              |
 *   ---------------------------------------------------------
 *  ^              ^                  ^        ^              ^
 * col_0         col_1              col_n     col           margin
 *
 * where B0, B1, ..., Bn are n blocks stored in the block queue.
 * - col_i is the start of B_i on the open line
 * - nsub_i is the number of atomic or closed sublocks of B_i that
 *   occur before the start of B_i+1
 *
 * If there are k closed blocks in the queue then these the k blocks
 * on the right of the line: B_{n-k+1} ... B_n, and the last of them
 * is (B_n) is followed by a group of closing parentheses. We keep
 * these closed blocks in the queue to compute the corresponding bsizes
 * (i.e., block size + number of closing parentheses that follow each block).
 *
 * All blocks in the queue, except possibly the first one, are
 * formatted in horizontal mode on the open line. If a new token
 * doesn't fit in the space left (i.e., margin - col) then we try the
 * next possible layout for B0, which removes B0 from the open line.
 * 
 * We also want to compute the bsize field of atomic tokens.
 * For this, we keep 
 * - last_atom = last atomic token on the open line 
 * - atom_col = start of that atom on the line
 * 
 * The pointer last_atom is non-null if the open line ends with an atomic
 * token, possibly followed by a set of closing parentheses, as in
 *  
 *      ------------------------------------
 *                           ... atom
 *      ------------------------------------
 *                                   ^
 *                                  col
 *  or
 *
 *      ---------------------------------------
 *                           ... atom)))
 *      ---------------------------------------
 *                                      ^
 *                                     col
 *
 * Then last_atom points to the token for 'atom_k' and atom_col 
 * is the column index where the 'atom_k' starts. 
 */

/*
 * Block descriptor:
 * - col = start of the block on the open line
 * - nsub = number of subblocks
 * - token = attached open_token 
 */
typedef struct pp_block_s {
  uint32_t col;
  uint32_t nsub;
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
 * - a copy of the display area (must be equal to the printer's area)
 * - a queue of tokens (stored as tagged pointers)
 * - a queue of block descriptors
 * - pointer to the last atom in the token queue (or NULL)
 * - descriptor of the open line
 */
typedef struct formatter_s {
  // printer + display area
  printer_t *printer;
  pp_area_t area;

  // queues  + number of closed blocks in block_queue
  ptr_queue_t token_queue;
  pp_block_queue_t block_queue;
  uint32_t nclosed;

  // last atom and block
  pp_atomic_token_t *last_atom;
  uint32_t atom_col;
  
  // control flags + indentation
  uint32_t indent;
  bool no_break;
  bool no_space;

  // open line
  uint32_t line;
  uint32_t col;
  uint32_t margin;

} formatter_t;



/*
 * PRETTY PRINTER
 */
typedef struct pp_s {
  pp_area_t area;
  printer_t printer;
  formatter_t formatter;
} pp_t;




/*
 * PRINTER INTERFACE
 */

/*
 * Initialization:
 * - converter = converter interface (copied internally).
 * - file = output stream to use (must be an open, writable file)
 * - area = specify display area + truncate + stretch
 *   if its is NULL then the default area is used
 * - mode = initial print mode
 * - indent = initial indentation (increment)
 *
 * mode + indent are the bottom stack element
 */
extern void init_pp(pp_t *pp, pp_token_converter_t *converter, FILE *file,
		    pp_area_t *area, pp_print_mode_t mode, uint32_t indent);

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
extern void pp_push_token(pp_t *pp, void *tk);

/*
 * Flush the printer: print all the closing parentheses required
 * and pop all the modes from the stack (until we're back to level 0).
 */
extern void flush_pp(pp_t *pp);

/*
 * Delete the printer: free memory
 * (This may call the free_token function in pp->converter).
 */
extern void delete_pp(pp_t *pp);


#endif /* __PRETTY_PRINTER_H */
