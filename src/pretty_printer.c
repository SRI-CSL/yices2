/*
 * PRETTY PRINTER
 */

#include <stddef.h>
#include <stdio.h>

#include "memalloc.h"
#include "pretty_printer.h"


/*
 * TOKEN INITIALIZATION
 */

/*
 * Make tk an atomic token of the given size
 * - size must be positive.
 */
void pp_set_atomic_token(pp_token_t *tk, int32_t size, int32_t tag) {
  assert(size > 0);
  tk->header = tk_header(PP_ATOMIC, 0, 0);
  tk->size = size;
  tk->label_size = 0;
  tk->indent = 0;
  tk->user_tag = tag;
}

/*
 * Make tk an open-labeled token:
 * - formats encodes the set of allowed formats for the block that starts with tk
 *   (must be a bitwise or of the four PP_..MODE_MASKs, with at least one bit set).
 * - label_size must be positive
 */
void pp_set_open_labeled_token(pp_token_t *tk, uint32_t formats, 
			       uint16_t label_size, uint16_t indent, int32_t tag) {
  assert(label_size > 0 && (formats & PP_TOKEN_FORMAT_MASK) != 0);
  tk->header = tk_header(PP_OPEN_LABELED, 0, formats);
  tk->size = 0;
  tk->label_size = label_size;
  tk->indent = indent;
  tk->user_tag = tag;
}

/*
 * Make tk an open-unlabeled token:
 * - formats encodes the set of allowed formats for the block that starts with tk
 *   (must be a bitwise or of the four PP_..MODE_MASKs, with at least one bit set).
 */
void pp_set_open_unlabeled_token(pp_token_t *tk, uint32_t formats, 
				 uint16_t indent, int32_t tag) {
  assert((formats & PP_TOKEN_FORMAT_MASK) != 0);
  tk->header = tk_header(PP_OPEN_UNLABELED, 0, formats);
  tk->size = 0;
  tk->label_size = 0;
  tk->indent = indent;
  tk->user_tag = tag;
}

/*
 * Make tk a close token
 */
void pp_set_close_token(pp_token_t *tk) {
  tk->header = tk_header(PP_CLOSE, 0, 0);
  tk->size = 0;
  tk->label_size = 0;
  tk->indent = 0;
  tk->user_tag = 0;
}



/*
 * PRINTER STACK
 */

/*
 * Initialize stack
 * - use the default size (must be positive)
 * - set the bottom stack element to the default settings  
 */
static void init_pp_printer_stack(pp_printer_stack_t *stack) {
  uint32_t n;

  n = DEF_PP_PRINTER_STACK_SIZE;
  assert(0 < n && n < MAX_PP_PRINTER_STACK_SIZE);
  stack->data = (pp_print_mode_t *) safe_malloc(n * sizeof(pp_print_mode_t));
  stack->top = 0;
  stack->size = n;

  stack->data[0].mode = pp_stack_mode(PP_HORIZONTAL, PP_STACK_NOSEP);
  stack->data[0].indent = 0;
}


/*
 * Increase the stack size (by 50%)
 */
static void extend_pp_printer_stack(pp_printer_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_PP_PRINTER_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (pp_print_mode_t *) safe_realloc(stack->data, n * sizeof(pp_print_mode_t));
  stack->size = n;
}


/*
 * Delete the stack
 */
static void delete_pp_printer_stack(pp_printer_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}

/*
 * Push new setting on top of the stack:
 * - layout must be one of the four layout formats
 * - sep must be either PP_STACK_SEP or PP_STACK_NOSEP
 * - indent is the new indentation level
 */
static void pp_printer_stack_push(pp_printer_stack_t *stack, pp_layout_mode_t layout,
				  uint32_t sep, uint32_t indent) {
  uint32_t i;

  i = stack->top + 1;
  if (i == stack->size) {
    extend_pp_printer_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].mode = pp_stack_mode((uint32_t) layout, sep);
  stack->data[i].indent = 0;
  stack->top = i;
}


/*
 * Pop the top element from the stack
 */
static inline void pp_printer_stack_pop(pp_printer_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}




/*
 * Change the top-mode and indent
 */
static void pp_printer_set_top_mode(pp_printer_stack_t *stack, pp_layout_mode_t layout) {
  uint32_t i, m;

  assert((layout & ~PP_STACK_MODE_FORMAT_MASK) == 0);
  i = stack->top;
  m = stack->data[i].mode & ~PP_STACK_MODE_FORMAT_MASK;
  stack->data[i].mode |= m | (uint32_t) layout;
}

static inline void pp_printer_set_top_indent(pp_printer_stack_t *stack, uint32_t indent) {
  stack->data[stack->top].indent = indent;
}




/*
 * PRINTER STRUCTURE
 */

/*
 * Short cuts to the converter functions
 */
static inline char *get_label(pp_printer_t *pp, pp_token_t *tk) {
  return pp->converter.get_label(pp->converter.user_ptr, tk);
}

static inline char *get_string(pp_printer_t *pp, pp_token_t *tk) {
  return pp->converter.get_string(pp->converter.user_ptr, tk);
}

static inline char *get_truncated(pp_printer_t *pp, pp_token_t *tk, uint32_t n) {
  return pp->converter.get_truncated(pp->converter.user_ptr, tk, n);
}

static inline void free_token(pp_printer_t *pp, pp_token_t *tk) {
  pp->converter.free_token(pp->converter.user_ptr, tk);
}


/*
 * Current mode and indentation level.
 */
static inline pp_layout_mode_t pp_layout_mode(pp_printer_t *pp) {
  return pp_stack_layout(pp->stack.data[pp->stack.top].mode);
}

static inline uint32_t pp_indent_level(pp_printer_t *pp) {
  return pp->stack.data[pp->stack.top].indent;
}

/*
 * Test the separation flag
 */
static inline bool pp_need_separator(pp_printer_t *pp) {
  return pp_stack_separate(pp->stack.data[pp->stack.top].mode);
}


/*
 * Initialize area: use default dimensions
 */
static void init_pp_display_area(pp_display_area_t *area) {
  area->width = PP_DEFAULT_WIDTH;
  area->height = PP_DEFAULT_HEIGHT;
  area->offset = PP_DEFAULT_OFFSET;
  area->col = 0;
  area->line = 0;
  area->last_line = area->height - 1;
  area->reserved_columns = 0;
}


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
void init_pp_printer(pp_printer_t *pp, pp_token_converter_t *converter, FILE *file) {
  init_pp_display_area(&pp->area);
  init_pp_printer_stack(&pp->stack);
  pp->options = PP_TRUNCATE_OPTION;
  pp->closing_pars = 0;
  pp->overfull = false;
  pp->pending_token = NULL;
  pp->converter = *converter;
  pp->stream = file;
}


/*
 * Change parameters: 
 * - these functions should be called before anything is printed.
 * - width must be at least PP_MINIMAL_WIDTH
 * - height must be at least PP_MINIMAL_HEIGHT
 * - indent must be less than width
 */
void pp_printer_set_width(pp_printer_t *pp, uint32_t width) {
  assert(pp->area.col == 0 && pp->area.line == 0 &&
	 width >= PP_MINIMAL_WIDTH);
  pp->area.width = width;
}

void pp_printer_set_height(pp_printer_t *pp, uint32_t height) {
  assert(pp->area.col == 0 && pp->area.line == 0 &&
	 height >= PP_MINIMAL_WIDTH);
  pp->area.height = height;
}

void pp_printer_set_offset(pp_printer_t *pp, uint32_t offset) {
  assert(pp->area.col == 0 && pp->area.line == 0);
  pp->area.offset = offset;
}

void pp_printer_set_mode(pp_printer_t *pp, pp_layout_mode_t layout) {
  assert(pp->area.col == 0 && pp->area.line == 0 && pp->stack.top == 0);
  pp_printer_set_top_mode(&pp->stack, layout);
}

void pp_printer_set_indent(pp_printer_t *pp, uint32_t indent) {
  assert(pp->area.col == 0 && pp->area.line == 0 && indent < pp->area.width);
  pp_printer_set_top_indent(&pp->stack, indent);
}


/*
 * Deletion
 */
void delete_pp_printer(pp_printer_t *pp) {
  if (pp->pending_token != NULL) {
    free_token(pp, pp->pending_token);
    pp->pending_token = NULL;
  }

  delete_pp_printer_stack(&pp->stack);
}



/*
 * BASIC PRINT FUNCTIONS
 * - each function prints something then update col and line
 * - TODO: check for IO errors in each function
 */
// print a single character (c must not be a line break)
static void pp_char(pp_printer_t *pp, int c) {
  fputc(c, pp->stream);
  pp->area.col ++;
}

// start a new line then indent
static void pp_newline(pp_printer_t *pp) {
  uint32_t n;

  fputc('\n', pp->stream);
  n = pp->area.offset + pp_indent_level(pp);
  while (n > 0) {
    fputc(' ', pp->stream);
    n --;
  }
  pp->area.line ++;
  pp->area.col = pp_indent_level(pp);
}

// print string s of size n
// the string must not contain line breaks
static void pp_string(pp_printer_t *pp, char *s, uint32_t n) {
  fputs(s, pp->stream);
  pp->area.col += n;
}

// print the first n characters of *s (or the full string if len(s) <= n)
static void pp_prefix(pp_printer_t *pp, char *s, uint32_t n) {
  uint32_t i;

  i = 0;
  while (*s != '\0' && i < n) {
    fputc(*s, pp->stream);
    i ++;
    s ++;
  }
  pp->area.col += i;
}


/*
 * More print functions
 */
static inline void pp_space(pp_printer_t *pp) {
  pp_char(pp, ' ');
}

static inline void pp_open_par(pp_printer_t *pp) {
  pp_char(pp, '(');
}

static inline void pp_close_par(pp_printer_t *pp) {
  pp_char(pp, ')');
}

static inline void pp_ellipsis(pp_printer_t *pp) {
  pp_string(pp, "...", 3);
}

