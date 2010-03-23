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
 * - indent is the new indentation increment
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
  return stack->data[stack->top].mode;
}

static inline uint32_t pp_stack_top_indent(pp_stack_t *stack) {
  return stack->data[stack->top].indent;
}




/*
 * PRINT AREA
 */

/*
 * Line width for a given indentation:
 * - in stretch mode, the line width is always equal to the area's width
 * - otherwise we want to preserve the invariant 
 *     line_width + indent == offset + area width.
 * - if this can't be done (i.e., indent is too large) then we return 0.
 */
static uint32_t line_width_for_indent(pp_area_t *area, uint32_t indent) {
  uint32_t width;
  
  width = area->width;
  if (! area->stretch) {
    width += area->offset;
    if (indent < width) {
      width -= indent;
    } else {
      width = 0;
    }
  }

  return width;
} 



/*
 * PRINTER STRUCTURE
 */

/*
 * Initialize the printer p:
 * - file = output stream to use
 * - converter = converter API
 * - area = descriptor of the print area
 * - mode = initial print mode
 * - indent = initial indentation
 */
static void init_printer(printer_t *p, FILE *file, pp_token_converter_t *converter,
			 pp_area_t *area, pp_print_mode_t mode, uint32_t indent) {
  uint32_t next_width;

  p->file = file;
  p->area = *area;      // make an internal copy
  p->conv = *converter; // internal copy too


  // Force HMODE if the print area is too small for the
  // specified mode and indent.
  next_width = line_width_for_indent(area, indent + area->offset);
  if (area->height == 1 || (p->area.truncate && next_width < 4)) {
    mode = PP_HMODE;
    indent = 0;
    next_width = line_width_for_indent(area, area->offset);
    assert(!p->area.truncate || next_width >= 4);
  }

  // control parameters: no break, no space on the first line
  init_pp_stack(&p->stack, mode, indent);
  p->mode = mode;
  p->indent = indent + area->offset;
  p->next_margin = next_width;
  p->no_break = true;
  p->no_space = true;
  p->full_line = false;
  p->overfull_count = 0;

  // print line: initial width = area->width
  p->line = 0;
  p->col = 0;
  p->margin = area->width;

  // pending tokens: empty
  p->pending_col = 0;
  init_pvector(&p->pending_tokens, 0);
}


/*
 * Short cuts to the converter functions
 */
static inline char *get_label(printer_t *p, pp_open_token_t *tk) {
  return p->conv.get_label(p->conv.user_ptr, tk);
}

static inline char *get_string(printer_t *p, pp_atomic_token_t *tk) {
  return p->conv.get_string(p->conv.user_ptr, tk);
}

static inline char *get_truncated(printer_t *p, pp_atomic_token_t *tk, uint32_t n) {
  return p->conv.get_truncated(p->conv.user_ptr, tk, n);
}

static inline void free_open_token(printer_t *p, pp_open_token_t *tk) {
  p->conv.free_open_token(p->conv.user_ptr, tk);
}

static inline void free_atomic_token(printer_t *p, pp_atomic_token_t *tk) {
  p->conv.free_atomic_token(p->conv.user_ptr, tk);
}

static inline void free_close_token(printer_t *p, pp_close_token_t *tk) {
  p->conv.free_close_token(p->conv.user_ptr, tk);
}


/*
 * Free token: use tag to call one of the three functions above
 * - tk must be a tagged pointer
 */
static void free_token(printer_t *p, void *tk) {
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    free_open_token(p, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    free_atomic_token(p, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    free_close_token(p, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }
}


/*
 * Free all memory used by the printer
 * - also call free on all the pending_tokens
 */
static void delete_printer(printer_t *p) {
  pvector_t *v;
  uint32_t i, n;

  delete_pp_stack(&p->stack);
  v = &p->pending_tokens;
  n = v->size;
  for (i=0; i<n; i++) {
    free_token(p, v->data[i]);
  }
  delete_pvector(v);  
}


/*
 * Basic print operations
 */

/*
 * Print a single char (must not be a line break)
 */
static void pp_char(printer_t *p, int c) {
  fputc(c, p->file);
  p->col ++;
}

static inline void pp_open_par(printer_t *p) {
  pp_char(p, '(');
}

static inline void pp_close_par(printer_t *p) {
  pp_char(p, ')');
}

static inline void pp_space(printer_t *p) {
  pp_char(p, ' ');
}


/*
 * Print a string s of length n
 */
static void pp_string(printer_t *p, char *s, uint32_t n) {
  assert(n == strlen(s));
  fputs(s, p->file);
  p->col += n;
}

static inline void pp_ellipsis(printer_t *p) {
  pp_string(p, "...", 3);
}

/*
 * Print the first n characters of s (or the full string if s is too short).
 */
static void pp_prefix(printer_t *p, char *s, uint32_t n) {
  uint32_t i;

  i = 0;
  while (*s != '\0' && i < n) {
    fputc(*s, p->file);
    i ++;
    s ++;
  }
  p->col += n;
}

/*
 * Print a new line then indent
 * - update line, col, and margin
 */
static void pp_newline(printer_t *p) {
  uint32_t n;

  fputc('\n', p->file);
  n = p->indent;
  while (n > 0) {
    fputc(' ', p->file);
    n --;
  }
  p->line ++;
  p->col = 0;
  p->margin = p->next_margin;
}




/*
 * Print a space unless the no_space flag is true
 */
static void print_blank(printer_t *p) {
  if (!p->no_space) {
    pp_space(p);
  } 
}

/*
 * Print atomic token tk
 */
static void print_atomic(printer_t *p, pp_atomic_token_t *tk) {
  char *s;

  s = get_string(p, tk);
  pp_string(p, s, tk->size);
  free_atomic_token(p, tk);
}

/*
 * Print atomic token tk truncated to fit in what's left of the 
 * current line. Then print ellipsis.
 */
static void print_atomic_truncated(printer_t *p, pp_atomic_token_t *tk) {
  char *s;
  uint32_t space;

  assert(p->col + 3 <= p->margin);
  space = p->margin - p->col;
  if (space > 3) {
    space -= 3;
    s = get_truncated(p, tk, space);
    pp_prefix(p, s, space);
  }
  pp_ellipsis(p);
  free_atomic_token(p, tk);
}


/*
 * Print label of tk prefixed with '(' if tk has parentheses
 */
static void print_label(printer_t *p, pp_open_token_t *tk) {
  char *s;

  if (tk_has_par(tk)) {
    pp_open_par(p);
  }
  s = get_label(p, tk);
  pp_string(p, s, tk->label_size);
  free_open_token(p, tk);
}

/*
 * Print label of tk truncated then print ellipsis
 */
static void print_label_truncated(printer_t *p, pp_open_token_t *tk) {
  char *s;
  uint32_t space;

  assert(p->col + 3 <= p->margin);
  space = p->margin - p->col;
  if (space > 3) {
    if (tk_has_par(tk)) {
      pp_open_par(p);
      space --;
    }
    s = get_label(p, tk);
    pp_prefix(p, s, space - 3);
  }
  pp_ellipsis(p);
  free_open_token(p, tk);
}

/*
 * Print ')' for close token tk
 */
static void print_close(printer_t *p, pp_close_token_t *tk) {
  if (tk_has_close_par(tk)) {
    pp_close_par(p);
  }
  free_close_token(p, tk);
}


/*
 * Print all the pending tokens.
 * Free all pending tokens and empty the pending_vector.
 * - p->pending_col = column where printing should start
 */
static void print_pending(printer_t *p) {
  pvector_t *v;
  void *tk;
  uint32_t i, n;

  // restore p->col
  p->col = p->pending_col;
  v = &p->pending_tokens;
  n = v->size;
  assert(n > 0);
  tk = v->data[0];
  // no space before the first token
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    print_label(p, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    print_atomic(p, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    print_close(p, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }

  for (i=1; i<n; i++) {
    tk = v->data[i];
    switch (ptr_tag(tk)) {
    case PP_TOKEN_OPEN_TAG:
      pp_space(p);
      print_label(p, untag_open(tk));
      break;
    case PP_TOKEN_ATOMIC_TAG:
      pp_space(p);
      print_atomic(p, untag_atomic(tk));
      break;
    case PP_TOKEN_CLOSE_TAG:
      print_close(p, untag_close(tk));
      break;
    default:
      assert(false);
      break;
    }
  }
  pvector_reset(v);
}

/*
 * Print the first pending token truncated then print ellipsis.
 * Free all tokens and empty the vector.
 * - p->pending_col = column where printing should start
 */
static void print_pending_truncated(printer_t *p) {
  pvector_t *v;
  void *tk;
  uint32_t i, n;

  p->col = p->pending_col;
  v = &p->pending_tokens;
  n = v->size;
  assert(n > 0);
  tk = v->data[0];
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    print_label_truncated(p, untag_open(tk));
    break;
  case PP_TOKEN_ATOMIC_TAG:
    print_atomic_truncated(p, untag_atomic(tk));
    break;
  case PP_TOKEN_CLOSE_TAG:
    pp_space(p);
    pp_ellipsis(p);
    free_close_token(p, untag_close(tk));
    break;
  default:
    assert(false);
    break;
  }
  
  for (i=1; i<n; i++) {
    free_token(p, v->data[i]);
  }
  pvector_reset(v);
}


/*
 * Printer invariants:
 * 
 * In truncate mode, the following invariants hold:
 * - if col + 4 <= margin then 
 *      the pending vector is empty
 *      full_line is false
 * - if col + 4 > margin and full_line is false then
 *      col <= margin
 *      there are pending tokens
 * - if full_line is true then 
 *      col + 4 > margin
 *      the pending vector is empty
 *   (nothing can be printed)
 */


/*
 * Print atomic token tk
 */
static void print_atomic_token(printer_t *p, pp_atomic_token_t *tk) {
  uint32_t new_col;

  if (p->area.truncate) {
    if (p->col + 4 <= p->margin) {
      /*
       * truncate mode, line not full, nothing pending
       */
      assert(!p->full_line && p->pending_tokens.size == 0);

      print_blank(p);
      new_col = p->col + tk->size;
      if (new_col + 4 <= p->margin) {
	// tk fits and there's room for ' ...' after it
	print_atomic(p, tk);
      } else if (new_col <= p->margin) {
	// we can't tell whether tk fits fully yet 
	// because we may need ellipsis after tk.
	p->pending_col = p->col;
	p->col = new_col;
	pvector_push(&p->pending_tokens, tag_atomic(tk));
      } else {
	// tk does not fit: print it truncated followed by ellipsis
	print_atomic_truncated(p, tk);
	p->full_line = true;
      }

    } else if (!p->full_line) {
      /* 
       * truncate mode, line not full, tokens pending
       */
      assert(p->col <= p->margin && p->pending_tokens.size > 0);

      // add tk to the pending tokens if it fits
      new_col = p->col + tk->size + (! p->no_space);
      if (new_col <= p->margin) {
	p->col = new_col;
	pvector_push(&p->pending_tokens, tag_atomic(tk));
      } else {
	// the pending tokens don't fit
	// print what we can + ellipsis
	print_pending_truncated(p);
	free_atomic_token(p, tk);
	p->full_line = true;
      }

    } else {
      /*
       * truncate mode, line full, nothing pending
       */
      assert(p->pending_tokens.size == 0); 
      free_atomic_token(p, tk);
    }

  } else {
    /*
     * don't truncate
     */
    print_blank(p);
    print_atomic(p, tk);
  }
}


/*
 * Print the label and '(' for open block tk
 */
static void print_open_token(printer_t *p, pp_open_token_t *tk) {
  uint32_t new_col;

  if (p->area.truncate) {
    if (p->col + 4 <= p->margin) {
      /*
       * truncate mode, line not full, nothing pending
       */
      assert(!p->full_line && p->pending_tokens.size == 0);

      print_blank(p);
      new_col = p->col + tk->label_size + tk_has_par(tk);
      if (new_col + 4 <= p->margin) {
	// tk fits and there's room for ' ...' after it
	print_label(p, tk);
      } else if (new_col <= p->margin) {
	// we can't tell whether tk fits yet
	// because we may need ellipsis
	p->pending_col = p->col;
	p->col = new_col;
	pvector_push(&p->pending_tokens, tag_open(tk));
      } else {
	// tk does not fit: print it truncated
	print_label_truncated(p, tk);
	p->full_line = true;;
      }

    } else if (!p->full_line) {
      /*
       * truncate mode, line not full, tokens pending
       */
      assert(p->col <= p->margin && p->pending_tokens.size > 0);

      // add tk to the pending tokens if it fits
      new_col = p->col + tk->bsize + tk_has_par(tk) + (! p->no_space);
      if (new_col <= p->margin) {
	p->col = new_col;
	pvector_push(&p->pending_tokens, tag_open(tk));
      } else {
	// the pending tokens don't fit
	// print what we can + ellipsis
	print_pending_truncated(p);
	free_open_token(p, tk);
	p->full_line = true;
      }

    } else {
      /*
       * truncate mode, line full, nothing pending
       */
      assert(p->pending_tokens.size == 0); 
      free_open_token(p, tk);
    }

  } else {
    /*
     * don't truncate
     */
    print_blank(p);
    print_label(p, tk);
  }
}


/*
 * Check whether tk requires a ')' and if so print it
 */
static void print_close_token(printer_t *p, pp_close_token_t *tk) {
  if (tk_has_close_par(tk)) {
    if (p->area.truncate) {

      if (p->col + 5 <= p->margin) {
	// tuncate mode, no pending tokens and enough space for ') ...'
	assert(!p->full_line && p->pending_tokens.size == 0);
	print_close(p, tk);
      } else if (p->col + 4 == p->margin) {
	// truncate mode, no pending tokens, space for 4 more characters
	assert(!p->full_line && p->pending_tokens.size == 0);
	p->pending_col = p->col;
	p->col ++;
	pvector_push(&p->pending_tokens, tag_close(tk));
      } else if (!p->full_line) {
	// pending tokens, line not full
	assert(p->pending_tokens.size > 0);
	if (p->col < p->margin) {
	  // enough space for one more ')' 
	  p->col ++;
	  pvector_push(&p->pending_tokens, tag_close(tk));
	} else  {
	  // no space for ')'
	  print_pending_truncated(p);
	  free_close_token(p, tk);
	  p->full_line = true;
	}
      } else {
	// the line is full
	assert(p->pending_tokens.size == 0);
	free_close_token(p, tk);
      }

    } else {
      // not truncation
      print_close(p, tk);
    }
  }
}


/*
 * Flush the current line then move to the next line
 * - empty the pending token buffer
 */
static void print_newline(printer_t *p) {
  if (p->pending_tokens.size > 0) {
    print_pending(p);
  }
  
  pp_newline(p);
  assert(!p->area.truncate || p->margin >= 4);
  p->no_space = true;   // prevent space after the new line
  p->full_line = false;
}


/*
 * Print a line break if required and possible
 * - n = size of the next token
 */
static void check_newline(printer_t *p, uint32_t n) {
  if (p->no_break || 
      p->line + 1 == p->area.height || 
      p->overfull_count > 0) {
    // a line break is not allowed
    return;
  }

  switch (p->mode) {
  case PP_HMODE:
    break; // do nothing
    
  case PP_VMODE:
    print_newline(p);
    break;
      
  case PP_HVMODE:
    if (p->col + n + (!p->no_space) > p->margin) {
      // the next token doesn't fit on this line
      print_newline(p);
    }
    break;
  }
}


/*
 * Push the print state specified by open token tk onto
 * the stack.
 * - tk->formats specify the next print mode
 * - tk->indent or tk->short_ident is added to the current 
 *   indentation
 * - if tk->sep is 0 (no sepatator) then no_space and no_break 
 *   are set true
 *
 * The new mode and indentation are chosen according to the 
 * following rules:
 * - if p->line is the last available line or 
 *      p->mode is HMODE or 
 *      tk->formats contains HLAYOUT
 *   then new state := (HMODE, 0)
 * - otherwise, we choose in the following order
 *    (HVMODE, tk->indent)      if tk->formats contains MLAYOUT
 *    (VMODE, tk->indent)       if tk->formats contains VLAYOUT
 *    (VMODE, tk->short_indent) in all other cases
 *
 * If truncate is set, we check before switching that the new indentation
 * will keep the print line wide enough. If it doesn't we use (HMODE,0).
 */
static void printer_push_state(printer_t *p, pp_open_token_t *tk) {
  uint32_t indent_delta, new_width;
  pp_print_mode_t new_mode;

  assert(p->mode == pp_stack_top_mode(&p->stack) && 
	 p->indent >= p->area.offset + pp_stack_top_indent(&p->stack) &&
	 (!p->area.truncate || p->margin >= 4) &&
	 p->line < p->area.height);


  /*
   * If a separator is not allowed by tk then
   * no_space and no_break must both be true.
   *
   * Otherwise
   * - no_space is false
   * - no_break is true in VLAYOUT and MLAYOUT
   *               false in TLAYOUT
   *               irrelevant in HLAYOUT
   *
   * We set no_space to the correct value here
   * and no_break to true. Flag no_break will
   * be changed in TALYOUT if necessary.
   */
  p->no_space = !tk_sep_allowed(tk);
  p->no_break = true; 

  /*
   * New mode and indentation increment
   */
  if (tk_has_hlayout(tk) ||
      p->mode == PP_HMODE || 
      p->line + 1 == p->area.height) {
    new_mode = PP_HMODE;
    indent_delta = 0;
  } else if (tk_has_mlayout(tk)) {
    new_mode = PP_HVMODE;
    indent_delta = tk->indent;
  } else if (tk_has_vlayout(tk)) {
    new_mode = PP_VMODE;
    indent_delta = tk->indent;
  } else {
    // tight layout: no_space and no_break must be equal
    new_mode = PP_VMODE;
    indent_delta = tk->short_indent;
    p->no_break = p->no_space;
  }

  /*
   * Width of the next line
   */
  new_width = line_width_for_indent(&p->area, p->indent + indent_delta);

  /*
   * Check whether the new_width is large enough
   * (it's irrelevant if truncate is disabled).
   */
  if (p->area.truncate && new_width < 4) {
    // too small: force HMODE and correct new_width
    new_mode = PP_HMODE;
    indent_delta = 0;
    new_width = line_width_for_indent(&p->area, p->indent);
    assert(new_width >= 4);
  }
  
  // new mode and indentation are accepted
  pp_stack_push(&p->stack, new_mode, indent_delta);
  p->mode = new_mode;
  p->indent += indent_delta;  
  p->next_margin = new_width;
}


/*
 * Remove the top print state from the stack.
 * Restore the previous indentation and mode
 */
static void printer_pop_state(printer_t *p) {
  uint32_t indent_delta;

  assert(p->mode == pp_stack_top_mode(&p->stack) &&
	 p->indent >= p->area.offset + pp_stack_top_indent(&p->stack) &&
	 (!p->area.truncate || p->margin >= 4) &&
	 p->line < p->area.height);

  indent_delta = pp_stack_top_indent(&p->stack);
  pp_stack_pop(&p->stack);

  // restore the previous indentation 
  assert(indent_delta <= p->indent);
  p->indent -= indent_delta;

  // restore the top mode from the stack
  p->mode = pp_stack_top_mode(&p->stack);

  // adjust the next line width 
  p->next_margin = line_width_for_indent(&p->area, p->indent);
}


/*
 * Process token tk
 */
static void print_token(printer_t *p, void *tk) {
  pp_open_token_t *open;
  pp_atomic_token_t *atom;

  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    open = untag_open(tk);
    check_newline(p, open->bsize);
    print_open_token(p, open);
    if (p->full_line) {
      p->overfull_count ++;
    } else {
      printer_push_state(p, open);
    }
    break;

  case PP_TOKEN_ATOMIC_TAG:
    atom = untag_atomic(tk);
    check_newline(p, atom->bsize);
    print_atomic_token(p, atom);
    p->no_space = false;
    p->no_break = false; // this has no effect in HMODE
    break;

  case PP_TOKEN_CLOSE_TAG:
    print_close_token(p, untag_close(tk));
    // space and break are allowed now
    p->no_space = false;
    p->no_break = false;
    if (p->overfull_count > 0) {
      p->overfull_count --;
    } else {
      printer_pop_state(p);
    }
    break;

  default:
    assert(false);
    break;
  }
}




/*
 * INITIALIZATION
 */

/*
 * Default display area
 */
static pp_area_t default_area = {
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
 * - area = specify display area + truncate + stretch
 *   if area is NULL then the default is used
 * - mode = initial mode
 * - indent = initial indentation (increment)
 *
 * mode + indent are the bottom stack element
 */
void init_pp(pp_t *pp, pp_token_converter_t *converter, FILE *file,
	     pp_area_t *area, pp_print_mode_t mode, uint32_t indent) {

  if (area == NULL) {
    area = &default_area;
  }

  assert(area->width >= PP_MINIMAL_WIDTH &&
	 area->height >= PP_MINIMAL_HEIGHT);

  pp->area = *area;
  init_printer(&pp->printer, file, converter, area, mode, indent);
}


/*
 * Deletion
 */
void delete_pp(pp_t *pp) {
  delete_printer(&pp->printer);
}



/*
 * FOR TESTING
 */

/*
 * Process token tk
 */
void pp_push_token(pp_t *pp, void *tk) {
  print_token(&pp->printer, tk);
}


/*
 * Flush the printer.
 */
void flush_pp(pp_t *pp) {
  printer_t *p;

  p = &pp->printer;
  if (p->pending_tokens.size > 0) {
    print_pending(p);
  }
  fputc('\n', p->file);
  p->no_space = true;
  p->no_break = true;
  p->full_line = false;
  p->overfull_count = 0;
  p->line = 0;
  p->col = 0;
  fflush(p->file);
}
