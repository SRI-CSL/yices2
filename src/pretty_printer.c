/*
 * PRETTY PRINTER
 */

#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "memalloc.h"
#include "pretty_printer.h"


/*
 * PRINTER STACK
 */

/*
 * Initialize stack
 * - use the default size (must be positive)
 * - set the bottom stack element to mode, indent
 */
static void init_pp_stack(pp_stack_t *stack, pp_print_mode_t mode, uint32_t indent) {
  uint32_t n;

  n = DEF_PP_STACK_SIZE;
  assert(0 < n && n < MAX_PP_STACK_SIZE);
  stack->data = (pp_state_t *) safe_malloc(n * sizeof(pp_state_t));
  stack->top = 0;
  stack->size = n;

  stack->data[0].mode = mode;
  stack->data[0].indent = indent;
}


/*
 * Increase the stack size (by 50%)
 */
static void extend_pp_stack(pp_stack_t *stack) {
  uint32_t n;

  n = stack->size + 1;
  n += n>>1;
  if (n >= MAX_PP_STACK_SIZE) {
    out_of_memory();
  }

  stack->data = (pp_state_t *) safe_realloc(stack->data, n * sizeof(pp_state_t));
  stack->size = n;
}


/*
 * Delete the stack
 */
static void delete_pp_stack(pp_stack_t *stack) {
  safe_free(stack->data);
  stack->data = NULL;
}

/*
 * Push new state on top of the stack
 * - mode must not be UMODE
 * - indent is the new indentation level
 */
static void pp_stack_push(pp_stack_t *stack, pp_print_mode_t mode, uint32_t indent) {
  uint32_t i;

  i = stack->top + 1;
  if (i == stack->size) {
    extend_pp_stack(stack);
  }
  assert(i < stack->size);

  stack->data[i].mode = mode;
  stack->data[i].indent = indent;
  stack->top = i;
}


/*
 * Pop the top element from the stack
 */
static inline void pp_stack_pop(pp_stack_t *stack) {
  assert(stack->top > 0);
  stack->top --;
}


/*
 * Get the current print mode and indent
 */
static inline pp_print_mode_t pp_stack_top_mode(pp_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data[stack->top-1].mode;
}

static inline uint32_t pp_stack_top_indent(pp_stack_t *stack) {
  assert(stack->top > 0);
  return stack->data[stack->top-1].indent;
}


/*
 * BASIC PRINT OPERATIONS
 */

/*
 * Initialize the print_line structure:
 * - width = area width (must be the same as in the display structure)
 * - mode = initial print mode (must be the same as in the stack)
 * - indent = initial indentation (must be equal to the offset
 *            in display + indent in the stack)
 * Other fields have default values:
 * - print starts in top-line, left-corner of the display area:
 *   line = 0, col = 0, no_break, no_space
 * - margin = length of the first line = area width
 * - no enclosing parentheses open
 * - no pending token, not overfull
 */
static void init_print_line(print_line_t *pline, FILE *file, 
			    uint32_t width, pp_print_mode_t mode, uint32_t indent) {
  pline->file = file;
  pline->line = 0;
  pline->col = 0;
  pline->margin = width;
  pline->pending_col = 0;
  pline->mode = mode;
  pline->indent = indent;
  pline->no_break = true;
  pline->no_space = true;
  pline->overfull_count = 0;
  init_pvector(&pline->pending_tokens, 0);
}


/*
 * Print a single char (must not be a line break)
 */
static void pp_char(print_line_t *pline, int c) {
  fputc(c, pline->file);
  pline->col ++;
}

static inline void pp_open_par(print_line_t *pline) {
  pp_char(pline, '(');
}

static inline void pp_close_par(print_line_t *pline) {
  pp_char(pline, ')');
}

static inline void pp_space(print_line_t *pline) {
  pp_char(pline, ' ');
}

/*
 * Print a string s of length n
 */
static void pp_string(print_line_t *pline, char *s, uint32_t n) {
  assert(n == strlen(s));
  fputs(s, pline->file);
  pline->col += n;
}

static inline void pp_ellipsis(print_line_t *pline) {
  pp_string(pline, "...", 3);
}

/*
 * Print the first n characters of s (or the full string if s is too short).
 */
static void pp_prefix(print_line_t *pline, char *s, uint32_t n) {
  uint32_t i;

  i = 0;
  while (*s != '\0' && i < n) {
    fputc(*s, pline->file);
    i ++;
    s ++;
  }
  pline->col += n;
}

/*
 * Print a new line then indent
 */
static void pp_newline(print_line_t *pline) {
  uint32_t n;

  fputc('\n', pline->file);
  n = pline->indent;
  while (n > 0) {
    fputc(' ', pline->file);
    n --;
  }
  pline->line ++;
  pline->col = 0;  
}



/*
 * PRINT TOKEN
 */

/*
 * Short cuts to the converter functions
 */
static inline char *get_label(pp_t *pp, pp_open_token_t *tk) {
  return pp->converter.get_label(pp->converter.user_ptr, tk);
}

static inline char *get_string(pp_t *pp, pp_atomic_token_t *tk) {
  return pp->converter.get_string(pp->converter.user_ptr, tk);
}

static inline char *get_truncated(pp_t *pp, pp_atomic_token_t *tk, uint32_t n) {
  return pp->converter.get_truncated(pp->converter.user_ptr, tk, n);
}

static inline void free_open_token(pp_t *pp, pp_open_token_t *tk) {
  pp->converter.free_open_token(pp->converter.user_ptr, tk);
}

static inline void free_atomic_token(pp_t *pp, pp_atomic_token_t *tk) {
  pp->converter.free_atomic_token(pp->converter.user_ptr, tk);
}

static inline void free_close_token(pp_t *pp, pp_close_token_t *tk) {
  pp->converter.free_close_token(pp->converter.user_ptr, tk);
}


/*
 * Free token: use tag to call one of the three functions above
 * - tk must be a tagged pointer
 */
static void free_token(pp_t *pp, void *tk) {
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    free_open_token(pp, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    free_atomic_token(pp, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    free_close_token(pp, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }
}


/*
 * Print a space unless pline->no_space is true
 */
static void print_blank(print_line_t *pline) {
  if (!pline->no_space) {
    pp_space(pline);
  } 
}

/*
 * Print a line break unless pline->no_break is true
 */
static void print_newline(print_line_t *pline) {
  if (!pline->no_space) {
    pp_newline(pline);
  }
}

/*
 * Print atomic token tk
 */
static void print_atomic(pp_t *pp, pp_atomic_token_t *tk) {
  char *s;

  s = get_string(pp, tk);
  pp_string(&pp->pline, s, tk->size);
  free_atomic_token(pp, tk);
}

/*
 * Print atomic token tk truncated to fit in what's left of the 
 * current line. Then print ellipsis.
 */
static void print_atomic_truncated(pp_t *pp, pp_atomic_token_t *tk) {
  char *s;
  uint32_t space;

  assert(pp->pline.col + 3 <= pp->pline.margin);
  space = pp->pline.margin - pp->pline.col;
  if (space > 3) {
    space -= 3;
    s = get_truncated(pp, tk, space);
    pp_prefix(&pp->pline, s, space);
  }
  pp_ellipsis(&pp->pline);
  free_atomic_token(pp, tk);
}


/*
 * Print label of tk
 * prefix with '(' if tk has parentheses
 */
static void print_label(pp_t *pp, pp_open_token_t *tk) {
  char *s;

  if (tk_has_par(tk)) {
    pp_open_par(&pp->pline);
  }
  s = get_label(pp, tk);
  pp_string(&pp->pline, s, tk->label_size);
  free_open_token(pp, tk);
}

/*
 * Print label of tk truncated then print ellipsis
 */
static void print_label_truncated(pp_t *pp, pp_open_token_t *tk) {
  char *s;
  uint32_t space;

  assert(pp->pline.col + 3 <= pp->pline.margin);
  space = pp->pline.margin - pp->pline.col;
  if (space > 4) {
    space -= 4;
    s = get_label(pp, tk);
    if (tk_has_par(tk)) {
      pp_open_par(&pp->pline);
    }
    pp_prefix(&pp->pline, s, space);
  }
  pp_ellipsis(&pp->pline);
  free_open_token(pp, tk);
}

/*
 * Print ')' for close token tk
 */
static void print_close(pp_t *pp, pp_close_token_t *tk) {
  if (tk_has_close_par(tk)) {
    pp_close_par(&pp->pline);
  }
  free_close_token(pp, tk);
}


/*
 * Print all the pending tokens.
 * - the first token must be atomic or open block
 * - pp->pline.pending_col = column where printing should start
 */
static void print_pending(pp_t *pp) {
  pvector_t *v;
  void *tk;
  uint32_t i, n;

  pp->pline.col = pp->pline.pending_col;
  v = &pp->pline.pending_tokens;
  n = v->size;
  assert(n > 0);
  tk = v->data[0];
  // no space before the first token
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    print_label(pp, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    print_atomic(pp, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    print_close(pp, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }

  for (i=1; i<n; i++) {
    tk = v->data[i];
    switch (ptr_tag(tk)) {
    case PP_TOKEN_OPEN_TAG:
      pp_space(&pp->pline);
      print_label(pp, untag_open(tk));
      break;
    case PP_TOKEN_ATOMIC_TAG:
      pp_space(&pp->pline);
      print_atomic(pp, untag_atomic(tk));
      break;
    case PP_TOKEN_CLOSE_TAG:
      print_close(pp, untag_close(tk));
      break;
    default:
      assert(false);
      break;
    }
  }
  pvector_reset(v);
}

/*
 * Print the first pending token truncated with ellipsis
 * - pp->pline.pending_col = column where printing should start
 * Free all tokens and empty the vector.
 */
static void print_pending_truncated(pp_t *pp) {
  pvector_t *v;
  void *tk;
  uint32_t i, n;

  pp->pline.col = pp->pline.pending_col;
  v = &pp->pline.pending_tokens;
  n = v->size;
  assert(n > 0);
  tk = v->data[0];
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    print_label_truncated(pp, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    print_atomic_truncated(pp, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    pp_space(&pp->pline);
    pp_ellipsis(&pp->pline);
    free_close_token(pp, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }
  
  for (i=1; i<n; i++) {
    free_token(pp, v->data[i]);
  }
  pvector_reset(v);
}


/*
 * Print atomic token tk
 */
static void print_atomic_token(pp_t *pp, pp_atomic_token_t *tk) {
  print_line_t *pline;
  uint32_t new_col;

  pline = &pp->pline;
  if (pp->display.truncate) {
    /*
     * In truncate mode, the following invariants hold:
     *   if col + 4 <= margin then 
     *      the pending vector is empty
     *   if col + 4 > margin and col <= margin then
     *      there are pending tokens
     *   if col > margin then the line is full, nothing more 
     *      can be printed on the current line.
     */
    if (pline->col + 4 <= pline->margin) {
      assert(pline->pending_tokens.size == 0);

      print_blank(pline);
      new_col = pline->col + tk->size;
      if (new_col + 4 <= pline->margin) {
	// tk fits and there's room for ' ...' after it
	print_atomic(pp, tk);
      } else if (new_col <= pline->margin) {
	// we can't tell whether tk fits fully yet 
	// because we may need ellipsis after tk.
	pline->pending_col = pline->col;
	pline->col = new_col;
	pvector_push(&pline->pending_tokens, tag_atomic(tk));
      } else {
	// tk does not fit: print it truncated followed by ellipsis
	print_atomic_truncated(pp, tk);
	pline->col ++; // force col > margin
      }

    } else if (pline->col <= pline->margin) {
      assert(pline->pending_tokens.size > 0);

      // add tk to the pending tokens if it fits
      new_col = pline->col + tk->size + (! pline->no_space);
      if (new_col <= pline->margin) {
	pline->col = new_col;
	pvector_push(&pline->pending_tokens, tag_atomic(tk));
      } else {
	// the pending tokens don't fit
	// print what we can + ellipsis
	print_pending_truncated(pp);
	pline->col = pline->margin + 1;
	free_atomic_token(pp, tk);
      }

    } else {
      // the line is full.
      free_atomic_token(pp, tk);
    }

  } else {
    // no truncate
    print_blank(pline);
    print_atomic(pp, tk);
  }
}


/*
 * Print the label and '(' for open block tk
 */
static void print_open_token(pp_t *pp, pp_open_token_t *tk) {
  print_line_t *pline;
  uint32_t new_col;

  pline = &pp->pline;
  if (pp->display.truncate) {
    /*
     * In truncate mode, the following invariants hold:
     *   if col + 4 <= margin then 
     *      the pending vector is empty
     *   if col + 4 > margin and col < margin then
     *      there are pending tokens
     *   if col >= margin then the line is full, nothing more 
     *      can be printed on the current line.
     */
    if (pline->col + 4 <= pline->margin) {
      assert(pline->pending_tokens.size == 0);

      print_blank(pline);
      new_col = pline->col + tk->label_size + tk_has_par(tk);
      if (new_col + 4 <= pline->margin) {
	// tk fits and there's room for ' ...' after it
	print_label(pp, tk);
      } else if (new_col <= pline->margin) {
	// we can't tell whether tk fits yet
	// because we may need ellipsis
	pline->pending_col = pline->col;
	pline->col = new_col;
	pvector_push(&pline->pending_tokens, tag_open(tk));
      } else {
	// tk does not fit: print it truncated
	print_label_truncated(pp, tk);
	pline->col ++; // force col > margin
      }

    } else if (pline->col <= pline->margin) {
      assert(pline->pending_tokens.size > 0);

      // add tk to the pending tokens if it fits
      new_col = pline->col + tk->size + tk_has_par(tk) + (! pline->no_space);
      if (new_col <= pline->margin) {
	pline->col = new_col;
	pvector_push(&pline->pending_tokens, tag_open(tk));
      } else {
	// the pending tokens don't fit
	// print what we can + ellipsis
	print_pending_truncated(pp);
	pline->col = pline->margin + 1;
	free_open_token(pp, tk);
      }

    } else {
      // the line is full
      free_open_token(pp, tk);
    }

  } else {
    // no truncate
    print_blank(pline);
    print_label(pp, tk);
  }
}


/*
 * Print the closing parenthesis of tk
 */
static void print_close_token(pp_t *pp, pp_close_token_t *tk) {
  print_line_t *pline;

  if (tk_has_close_par(tk)) {
    pline = &pp->pline;
    if (pp->display.truncate) {

      if (pline->col + 5 <= pline->margin) {
	// no pending tokens and enough space for ') ...'
	assert(pline->pending_tokens.size == 0);      
	print_close(pp, tk);
      } else if (pline->col + 4 == pline->margin) {
	// no pending tokens, space for 4 more characters
	assert(pline->pending_tokens.size == 0);      
	pline->pending_col = pline->col;
	pline->col ++;
	pvector_push(&pline->pending_tokens, tag_close(tk));
      } else if (pline->col < pline->margin) {
	// pending tokens, enough space for one pending ')' 
	assert(pline->pending_tokens.size > 0);
	pline->col ++;
	pvector_push(&pline->pending_tokens, tag_close(tk));
      } else if (pline->col == pline->margin) {
	// the pending tokens don't fit
	assert(pline->pending_tokens.size > 0);
	print_pending_truncated(pp);
	free_close_token(pp, tk);
	pline->col = pline->margin + 1;
      } else {
	// the line is full
	free_close_token(pp, tk);
      }

    } else {
      // not truncation
      print_close(pp, tk);
    }
  }
}





/*
 * INITIALIZATION
 */

/*
 * Default display area
 */
static pp_display_area_t default_display = {
  PP_DEFAULT_WIDTH,
  PP_DEFAULT_HEIGHT,
  PP_DEFAULT_OFFSET,
  PP_DEFAULT_STRETCH,
  PP_DEFAULT_TRUNCATE,
};

/*
 * Initialization:
 * - converter = converter interface (this
 *   is copied into pp->converter).
 * - file = output stream to use (must be an open file)
 * - display = specify display area + truncate + stretch
 *   if display is NULL then the default is used
 * - mode = initial mode
 * - indent = initial indentation (increment)
 *
 * mode + indent are the bottom stack element
 */
void init_pp(pp_t *pp, pp_token_converter_t *converter, FILE *file,
	     pp_display_area_t *display, pp_print_mode_t mode, uint32_t indent) {
  if (display == NULL) {
    display = &default_display;
  }
  assert(display->width >= PP_MINIMAL_WIDTH &&
	 display->height >= PP_MINIMAL_HEIGHT);

  pp->display = *display;
  init_pp_stack(&pp->stack, mode, indent);
  init_print_line(&pp->pline, file, display->width, 
		  mode, display->offset + indent);
  pp->converter = *converter;
}


/*
 * Deletion
 */
void delete_pp(pp_t *pp) {
  delete_pp_stack(&pp->stack);
}


/*
 * FOR TESTING
 */

/*
 * Process token tk
 */
void pp_push_token(pp_t *pp, void *tk) {
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    print_open_token(pp, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    print_atomic_token(pp, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    print_close_token(pp, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }

  pp->pline.no_space = false;
}


/*
 * Flush the printer.
 */
void flush_pp(pp_t *pp) {
  if (pp->pline.pending_tokens.size > 0) {
    print_pending(pp);
  }
  fputc('\n', pp->pline.file);
  pp->pline.line ++;
  pp->pline.col = 0;
  pp->pline.no_space = true;
  pp->pline.overfull_count = 0;
  fflush(pp->pline.file);
}
