/*
 * The Yices SMT Solver. Copyright 2014 SRI International.
 *
 * This program may only be used subject to the noncommercial end user
 * license agreement which is downloadable along with this program.
 */

/*
 * PRETTY PRINTER
 */

#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>

#include "utils/memalloc.h"
#include "io/pretty_printer.h"


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
 * Push a new state on top of the stack.
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

  // error codes
  p->print_failed = false;
  p->pp_errno = 0;

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
  case PP_TOKEN_SEPARATOR_TAG:
    free_atomic_token(p, untag_separator(tk));
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
 * Wrappers for fputc, fputs, and fflush to deal with errors
 */
static void pp_fputc(printer_t *p, int c) {
  int x;

  if (! p->print_failed) {
    x = fputc(c, p->file);
    if (x == EOF) {
      p->print_failed = true;
      p->pp_errno = errno;
    }
  }
}

static void pp_fputs(printer_t *p, char *s) {
  int x;

  if (!p->print_failed) {
    x = fputs(s, p->file);
    if (x == EOF) {
      p->print_failed = true;
      p->pp_errno = errno;
    }
  }
}

static void pp_fflush(printer_t *p) {
  int x;

  if (!p->print_failed) {
    x = fflush(p->file);
    if (x == EOF) {
      p->print_failed = true;
      p->pp_errno = errno;
    }
  }
}


/*
 * Print a single char (must not be a line break)
 */
static void pp_char(printer_t *p, int c) {
  pp_fputc(p, c);
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
  pp_fputs(p, s);
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
    pp_fputc(p, *s);
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

  pp_fputc(p, '\n');
  n = p->indent;
  while (n > 0) {
    pp_fputc(p, ' ');
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
  bool space;
  uint32_t i, n;

  // restore p->col
  p->col = p->pending_col;
  v = &p->pending_tokens;
  n = v->size;
  assert(n > 0);
  // no space before the first token
  space = false;
  for (i=0; i<n; i++) {
    tk = v->data[i];
    switch (ptr_tag(tk)) {
    case PP_TOKEN_OPEN_TAG:
      if (space) pp_space(p);
      print_label(p, untag_open(tk));
      space = tk_sep_allowed(untag_open(tk));
      break;
    case PP_TOKEN_ATOMIC_TAG:
      if (space) pp_space(p);
      print_atomic(p, untag_atomic(tk));
      space = true;
      break;
    case PP_TOKEN_CLOSE_TAG:
      print_close(p, untag_close(tk));
      space = true;
      break;
    case PP_TOKEN_SEPARATOR_TAG:
      // no space before or after that token
      print_atomic(p, untag_separator(tk));
      space = false;
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
  case PP_TOKEN_SEPARATOR_TAG:
    print_atomic_truncated(p, untag_separator(tk));
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
 * Print atomic token tk then free it.
 * - it's always freed
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
 * Check whether the block that starts with tk
 * fits horizontally on what's left of the current line.
 * - tk->bsize must contain the block size
 * - this is called after tk's opening parenthesis and
 *   label have been printed.
 */
static bool block_fits_horizontally(printer_t *p, pp_open_token_t *tk) {
  uint32_t h;

  h = tk->label_size + tk_has_par(tk);
  assert(h <= tk->bsize);
  return p->col + (tk->bsize - h) <= p->margin;
}


/*
 * Check whether all subblocks of the block that starts with tk
 * fit horizontally and whether the next component fits on what's
 * left of the current line.
 * - tk->csize must be equal to the maximal bsize of these sub-blocks
 * - tk->fsize must be the block size of the next token
 *
 * This checks whether the M or V layouts are possible for tk.
 * - the first atom or block after the label must be printed on
 *   the current line.
 * - all other blocks must be printed in H layout on a new line
 *   (adjusted for tk's indent).
 * - the new width must be at least 4.
 */
static bool subblocks_fit_horizontally(printer_t *p, pp_open_token_t *tk) {
  uint32_t new_width;

  new_width = line_width_for_indent(&p->area, p->indent + tk->indent);
  return new_width >= 4 && tk->csize <= new_width &&
    p->col + tk->fsize + (!tk_sep_allowed(tk)) <= p->margin;
}


/*
 * Push the print state specified by open token tk onto
 * the stack.
 * - tk->formats specify the next print mode
 * - tk->indent or tk->short_indent is added to the current
 *   indentation
 * - if tk->sep is 0 (no separator) then no_space and no_break
 *   are set true
 *
 * The new mode and indentation are chosen according to the
 * following rules (applied in this order).
 *
 * 1) If p->line is the last available line or
 *       p->mode is HMODE or
 *       p->mode is HVMODE
 *    then new state := (HMODE, 0).
 *
 * 2) If there's only one possible layout in tk-formats, then the
 *    next state is derived from that layout:
 *
 *      HLAYOUT --> new state = (HMODE, 0)
 *      MLAYOUT --> new state = (HVMODE, tk->indent)
 *      VLAYOUT --> new state = (VMODE, tk->indent)
 *      TLAYOUT --> new state = (VMODE, tk->short indent)
 *
 * 3) If HLAYOUT is in tk->formats and the full block fits on the
 *    current line (based on tk->bsize) then new state = (HMODE, 0)
 *
 * 4) If MLAYOUT is in tk->formats and all the sub-blocks fit on one
 *    line (based on tk->csize) then new state = (HVMODE, tk->indent)
 *
 * 5) If VLAYOUT is in tk->formats and all the sub-blocks fit on
 *    one line, then new state = (VMODE, tk->indent)
 *
 * 6) Nothing else works so new state = (VMODE, tk->short_indent)
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
   *               irrelevant in HLAYOUT.
   *
   * We set no_space to the correct value here
   * and no_break to true. The flag no_break will
   * be changed in TLAYOUT if selected.
   */
  p->no_space = !tk_sep_allowed(tk);
  p->no_break = true;

  /*
   * Select new mode and indentation increment
   */
  if (p->mode != PP_VMODE || p->line + 1 == p->area.height) {
    // HMODE is forced, indent_delta must be 0
    new_mode = PP_HMODE;
    indent_delta = 0;

  } else {
    switch (tk->formats) {
    case PP_H_LAYOUT:
      new_mode = PP_HMODE;
      indent_delta = 0;
      break;

    case PP_M_LAYOUT:
      new_mode = PP_HVMODE;
      indent_delta = tk->indent;
      break;

    case PP_V_LAYOUT:
      new_mode = PP_VMODE;
      indent_delta = tk->indent;
      break;

    case PP_T_LAYOUT:
      new_mode = PP_VMODE;
      indent_delta = tk->short_indent;
      p->no_break = p->no_space; // fix no_break
      break;

    default:
      // several layouts are allowed, check what works
      if (tk_has_hlayout(tk) && block_fits_horizontally(p, tk)) {
        new_mode = PP_HMODE;
        indent_delta = 0;
      } else if (tk_has_mlayout(tk) && subblocks_fit_horizontally(p, tk)) {
        new_mode = PP_HVMODE;
        indent_delta = tk->indent;
      } else if (tk_has_vlayout(tk) && subblocks_fit_horizontally(p, tk)) {
        new_mode = PP_VMODE;
        indent_delta = tk->indent;
      } else {
        new_mode = PP_VMODE;
        indent_delta = tk->short_indent;
        p->no_break = p->no_space;
      }
      break;
    }
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
 * - if p is in HVMODE and tk is either an atomic or an open token
 *   then tk->bsize is used to decide whether tk fits on the current line
 */
static void print_token(printer_t *p, void *tk) {
  pp_open_token_t *open;
  pp_atomic_token_t *atom;
  pp_open_token_t copy;

  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    open = untag_open(tk);
    check_newline(p, open->bsize);
    // print_open_token may free the token so we
    // make a local copy first.
    copy = *open;
    print_open_token(p, open);
    if (p->full_line) {
      p->overfull_count ++;
    } else {
      printer_push_state(p, &copy);
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

  case PP_TOKEN_SEPARATOR_TAG:
    atom = untag_separator(tk);
    /*
     * a separator is treated like an atomic token
     * with no space or break allowed before or after
     * the token
     */
    p->no_space = true;
    p->no_break = true;
    print_atomic_token(p, atom);
    p->no_space = true;
    p->no_break = true; // this has no effect in HMODE
    break;
  }

  // for debugging
  fflush(p->file);
}






/*
 * FORMATTER BLOCK QUEUE
 */

/*
 * Initialize the queue
 * - use the default size
 * - the queue is empty
 */
static void init_block_queue(pp_block_queue_t *q) {
  uint32_t n;

  n = DEF_BLOCK_QUEUE_SIZE;
  assert(0 < n && n <= MAX_BLOCK_QUEUE_SIZE);
  q->data = (pp_block_t *) safe_malloc(n * sizeof(pp_block_t));
  q->size = n;
  q->head = 0;
  q->tail = 0;
}


/*
 * Delete the queue
 */
static void delete_block_queue(pp_block_queue_t *q) {
  safe_free(q->data);
  q->data = NULL;
}


/*
 * Make the data array 50% larger
 */
static void extend_block_queue(pp_block_queue_t *q) {
  uint32_t n;

  n = q->size + 1;
  n += n>>1;

  if (n >= MAX_BLOCK_QUEUE_SIZE) {
    out_of_memory();
  }

  q->data = (pp_block_t *) safe_realloc(q->data, n * sizeof(pp_block_t));
  q->size = n;
}


/*
 * Add a new block at the end of the queue:
 * - tk = open token for that block
 * - col = column start for that block
 * - nsub is initialized to 0
 */
static void block_queue_push(pp_block_queue_t *q,
                             pp_open_token_t *tk, uint32_t col) {
  uint32_t i, n, j;

  // q->tail is always available
  i = q->tail;
  assert(i < q->size);
  q->data[i].col = col;
  q->data[i].token = tk;
  i ++;
  q->tail = i;

  if (i == q->size) {
    if (q->head == 0) {
      // full queue stored in data[0 ... size-1]
      extend_block_queue(q);
    } else {
      // wrap around
      q->tail = 0;
    }
  } else if (i == q->head) {
    /*
     * full queue stored in data[0 .. i-1] + data[head .. size -1]
     * make the array larger and shift data[head ... size-1] to
     * the end of the new array
     */
    assert(i < q->size);
    n = q->size;
    extend_block_queue(q);
    j = q->size; // new size
    do {
      n --;
      j --;
      q->data[j] = q->data[n];
    } while (n > i);
    q->head = j;
  }
}


/*
 * Check whether the queue is empty
 */
static inline bool block_queue_is_empty(pp_block_queue_t *q) {
  return q->head == q->tail;
}


/*
 * Descriptors of the first and last element in the queue
 * - the queue must not be empty
 */
static inline pp_block_t *first_block(pp_block_queue_t *q) {
  assert(q->head != q->tail);
  return q->data + q->head;
}

static pp_block_t *last_block(pp_block_queue_t *q) {
  uint32_t i;

  assert(q->head != q->tail);

  i = q->tail;
  if (i == 0) {
    i = q->size;
  }
  assert(i > 0);
  i --;
  return q->data + i;
}



/*
 * Remove the first block
 * - the queue must not be empty
 */
static void pop_first_block(pp_block_queue_t *q) {
  uint32_t h;

  assert(q->head != q->tail);

  h = q->head + 1;
  if (h == q->size) {
    h = 0;
  }
  assert(h < q->size);
  q->head = h;
}


/*
 * Remove that last block
 * - the queue must not be empty
 */
static void pop_last_block(pp_block_queue_t *q) {
  uint32_t t;

  assert(q->head != q->tail);

  t = q->tail;
  if (t == 0) {
    t = q->size;
  }
  assert(t > 0);
  q->tail = t - 1;
}




/*
 * FORMATTER STRUCTURE
 */

/*
 * Initialize the formatter f
 * - printer = attached printer object
 * - the token and block queues are initially empty
 * - the formatting line is empty too
 * - max_width is the area's width in printer
 */
static void init_formatter(formatter_t *f, printer_t *printer) {
  f->printer = printer;
  init_ptr_queue(&f->token_queue, 0); // use default size

  init_block_queue(&f->block_queue);
  f->queue_size = 0;
  f->nclosed = 0;
  f->head_token = NULL;
  f->head_closed = false;

  f->last_atom = NULL;
  f->atom_col = 0;

  // empty line: no space at the beginning
  f->no_space = true;
  f->length = 0;
  f->max_width= printer->area.width;

  f->depth = 0;
}


/*
 * Delete the formatter:
 * - call free_token for every tk in the queue.
 * - the printer should not be deleted before the formatter
 */
static void delete_formatter(formatter_t *f) {
  while (! ptr_queue_is_empty(&f->token_queue)) {
    free_token(f->printer, ptr_queue_pop(&f->token_queue));
  }
  delete_ptr_queue(&f->token_queue);
  delete_block_queue(&f->block_queue);
  f->last_atom = NULL;
}



/*
 * SIZE COMPUTATION
 */

/*
 * Set the bsize of the last atom and all closed blocks and
 * update the fsize and csize field of the enclosing blocks,
 * and remove the closed blocks from the block queue.
 *
 * The queue contains blocks B_0 ... B_n.
 *
 * If the closed blocks are B_k ... B_n with k > 0
 * - the bsizes of B_{k+1} ... B_n and of the last atom are set.
 * - the csize and fsize fields of B_n are updated based on the
 *   last atom's bsize.
 * - the csize and fsize fields of B_i are updated based on
 *   B{i+1} bsize (for i=n-1 to k-1).
 *
 * If k=0 then we also update the lead token based on B_0's bsize.
 */
static void set_bsizes_and_close(formatter_t *f) {
  pp_atomic_token_t *last;
  pp_block_t *b;
  pp_open_token_t *tk;
  uint32_t csize, n;

  // Set bsize of the last atom
  last = f->last_atom;
  csize = 0;
  if (last != NULL) {
    assert(f->atom_col <= f->length);
    csize = f->length - f->atom_col;
    last->bsize = csize;
  }

  /*
   * Set bsize, csize, and fsize of all closed blocks
   * and remove them from the queue.
   */
  assert(f->queue_size >= f->nclosed);
  n = f->nclosed;
  f->queue_size -= n;
  f->nclosed = 0;
  while (n > 0) {
    b = last_block(&f->block_queue);
    tk = b->token;
    // csize is 0 or the bsize of a sub-block or atom of tk
    if (tk->fsize == 0) { // first sub block closed
      tk->fsize = csize;
      tk->csize = csize;
    } else if (tk->csize < csize) {
      tk->csize = csize;
    }

    // compute the bsize of that block
    assert(b->col <= f->length);
    csize = f->length - b->col;
    tk->bsize = csize;
    pop_last_block(&f->block_queue);
    n --;
  }

  if (csize > 0) {
    /*
     * Set the csize and fsize of the head block
     * or of the last (open) block in the queue.
     */
    if (block_queue_is_empty(&f->block_queue)) {
      // all blocks are closed
      // csize = bsize of block B_0 or last_atom
      assert(f->queue_size == 0);
      tk = f->head_token;
      if (tk != NULL) {
        if (tk->fsize == 0) {
          tk->fsize = csize;
          tk->csize = csize;
        } else if (tk->csize < csize) {
          tk->csize = csize;
        }
      }
    } else {
      // update csize and fsize of the last block
      // in the queue
      b = last_block(&f->block_queue);
      tk = b->token;
      if (tk->fsize == 0) {
        tk->fsize = csize;
        tk->csize = csize;
      } else if (tk->csize < csize) {
        tk->csize = csize;
      }
    }
  }
}




/*
 * TOKEN QUEUE
 */

/*
 * Print all tokens from the start of the queue to tk (excluding tk).
 * - tk must be in the token queue
 */
static void flush_tokens(formatter_t *f, void *tk) {
  printer_t *p;
  void *x;

  p = f->printer;
  while (ptr_queue_first(&f->token_queue) != tk) {
    x = ptr_queue_pop(&f->token_queue);
    print_token(p, x);
  }
}


/*
 * Send all the tokens in the token queue to the printer
 */
static void flush_token_queue(formatter_t *f) {
  printer_t *p;
  void *tk;

  p = f->printer;
  while (! ptr_queue_is_empty(&f->token_queue)) {
    tk = ptr_queue_pop(&f->token_queue);
    print_token(p, tk);
  }

  f->last_atom = NULL;
  f->head_token = NULL;
  f->head_closed = false;
}


/*
 * Flush the token queue when the head block is closed
 * - at this point, we know the head block csize and fsize
 *   and bsize so it's ready to print
 */
static void flush_head_block(formatter_t *f) {
  if (f->head_closed) {
    assert(f->head_token != NULL && block_queue_is_empty(&f->block_queue));
    flush_token_queue(f);
  }
}


/*
 * For any block B_i in the queue, we know that the bsize for
 * that block is at least (f->length - B_i->col).
 *
 * If (f->length - B_0->col > f->max_width) then we can set B_0's
 * bsize to infinity (PP_MAX_BSIZE), update the csize of the head
 * token, and remove B_0 from the queue. The head token is ready to be
 * printed at this point (since its csize, bsize and fsize fields are
 * known).
 */
static void flush_wide_blocks(formatter_t *f) {
  pp_block_t *b;
  pp_open_token_t *tk, *head;

  while (!block_queue_is_empty(&f->block_queue)) {
    b = first_block(&f->block_queue);
    assert(b->col <= f->length);
    if (f->length - b->col <= f->max_width) break;
    /*
     * b has bsize > max_width: set its bsize to MAX
     * then remove it from the block queue
     */
    tk = b->token;
    tk->bsize = PP_MAX_BSIZE;
    head = f->head_token;
    if (head != NULL) {
      // update csize and fsize of the head token
      head->csize = PP_MAX_BSIZE;
      if (head->fsize == 0) {
        head->fsize = PP_MAX_BSIZE;
      }
    }
    // print all queued tokens, until tk
    flush_tokens(f, tag_open(tk));

    // tk becomes the head token
    assert(ptr_queue_first(&f->token_queue) == tag_open(tk));
    f->head_token = tk;
    if (f->nclosed == f->queue_size) {
      f->nclosed --;
    }

    pop_first_block(&f->block_queue);
    f->queue_size --;
  }
}



/*
 * Process atomic token tk
 */
static void process_atomic_token(formatter_t *f, pp_atomic_token_t *tk) {
  set_bsizes_and_close(f);
  flush_head_block(f);

  if (!f->no_space) f->length ++;

  f->atom_col = f->length;
  f->last_atom = tk;
  f->length += tk->size;
  f->no_space = false;
}


/*
 * Variant: for a separator token we don't print spaces around the token
 */
static void process_separator_token(formatter_t *f, pp_atomic_token_t *tk) {
  set_bsizes_and_close(f);
  flush_head_block(f);

  f->atom_col = f->length;
  f->last_atom = tk;
  f->length += tk->size;
  f->no_space = true;
}


/*
 * Process open-block token tk
 */
static void process_open_token(formatter_t *f, pp_open_token_t *tk) {
  set_bsizes_and_close(f);
  flush_head_block(f);

  if (!f->no_space) f->length ++;

  // add tk at the end of the  block queue
  tk->csize = 0;
  tk->fsize = 0;
  block_queue_push(&f->block_queue, tk, f->length);
  f->queue_size ++;

  // add optional '(' and token label to the line
  f->length += tk->label_size + tk_has_par(tk);

  // if tk forbids separator: no space
  f->no_space = !tk_sep_allowed(tk);

  // no last atom anymore
  f->last_atom = NULL;
}


/*
 * Process close token tk
 */
static void process_close_token(formatter_t *f, pp_close_token_t *tk) {
  if (tk_has_close_par(tk)) {
    // add ')' to the line
    f->length ++;
  }

  // this may close an open block in the queue
  // or close the head block
  if (f->nclosed < f->queue_size) {
    f->nclosed ++;
  } else if (f->head_token != NULL) {
    assert(f->nclosed == f->queue_size);
    f->head_closed = true;
  }
}


/*
 * Process a new token tk:
 * - add space + token at the end of the line, etc.
 * - then add token at the end of the token queue
 * - then forward tokens to the printer if possible
 */
static void process_token(formatter_t *f, void *tk) {
  switch (ptr_tag(tk)) {
  case PP_TOKEN_OPEN_TAG:
    process_open_token(f, untag_open(tk));
    f->depth ++;
    break;

  case PP_TOKEN_ATOMIC_TAG:
    process_atomic_token(f, untag_atomic(tk));
    break;

  case PP_TOKEN_CLOSE_TAG:
    assert(f->depth > 0);
    f->depth --;
    process_close_token(f, untag_close(tk));
    break;

  case PP_TOKEN_SEPARATOR_TAG:
    process_separator_token(f, untag_separator(tk));
    break;
  }

  // add tk to the queue
  ptr_queue_push(&f->token_queue, tk);

  // forward what we can to the printer
  flush_wide_blocks(f);
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

  init_printer(&pp->printer, file, converter, area, mode, indent);
  init_formatter(&pp->formatter, &pp->printer);
}


/*
 * Deletion
 */
void delete_pp(pp_t *pp) {
  delete_formatter(&pp->formatter);
  delete_printer(&pp->printer);
}



/*
 * Process token tk
 */
void pp_push_token(pp_t *pp, void *tk) {
  process_token(&pp->formatter, tk);
}


/*
 * Flush: process all tokens in the formatter's queue.
 * Then print a new line.
 */
void flush_pp(pp_t *pp) {
  printer_t *p;

  // empty the formatter's queues
  set_bsizes_and_close(&pp->formatter);
  flush_token_queue(&pp->formatter);

  // empty the printer
  p = &pp->printer;
  if (p->pending_tokens.size > 0) {
    print_pending(p);
  }

  pp->formatter.depth = 0;

  // start a new line
  pp_fputc(p, '\n');
  p->no_space = true;
  p->no_break = true;
  p->full_line = false;
  p->overfull_count = 0;
  p->line = 0;
  p->col = 0;
  p->margin = p->next_margin;
  pp_fflush(p);
}


/*
 * Check whether the printer is full (more precisely,
 * check whether we can't print anything more)
 */
bool pp_is_full(pp_t *pp) {
  printer_t *p;

  p = &pp->printer;
  return p->print_failed || (p->full_line && p->line + 1 == p->area.height);
}


/*
 * UTILITIES TO CONSTRUCT TOKENS
 */

/*
 * Initialize an open token tk and return the tagged pointer tag_open(tk).
 * - formats = allowed formats for that token (PP_??_LAYOUT)
 * - flags = whether '(' and space are required
 * - lsize = label size
 * - indent = indentation for V and M layouts
 * - short_indent = indentation for the T layout
 * - user_tag = whatever the converter needs
 */
void *init_open_token(pp_open_token_t *tk, uint32_t formats, uint32_t flags,
                      uint16_t lsize, uint16_t indent, uint16_t short_indent,
                      uint32_t user_tag) {
  // formats must fit in the lower 4 bits
  // and at least one of these bits must be set
  assert((formats & ~((uint32_t) 15)) == 0 && formats != 0);

  tk->formats = formats;
  tk->flags = flags;
  tk->label_size = lsize;
  tk->indent = indent;
  tk->short_indent = short_indent;
  tk->user_tag = user_tag;

  return tag_open(tk);
}


/*
 * Initialize an atomic token tk and return the tagged pointer tag_atomic(tk).
 * - size = token size (when converted to a string)
 * - user_tag = whatever the converter needs
 */
void *init_atomic_token(pp_atomic_token_t *tk, uint32_t size, uint32_t user_tag) {
  tk->size = size;
  tk->user_tag = user_tag;

  return tag_atomic(tk);
}


/*
 * Initialize an atomic token tk and return the tagged pointer tag_separator(tk).
 * - size = token size (when converted to a string)
 * - user_tag = whatever the converter needs
 */
void *init_separator_token(pp_atomic_token_t *tk, uint32_t size, uint32_t user_tag) {
  tk->size = size;
  tk->user_tag = user_tag;

  return tag_separator(tk);
}


/*
 * Initialize a close token tk and return the tagged pointer tag_close(tk).
 * - par: true if the token contains ')'
 * - user_tag: any thing used by the free_close_token in the converter
 */
void *init_close_token(pp_close_token_t *tk, bool par, uint32_t user_tag) {
  tk->flags = (par * PP_TOKEN_PAR_MASK);
  tk->user_tag = user_tag;

  return tag_close(tk);
}


