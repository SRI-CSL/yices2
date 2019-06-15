#! /bin/sh
# Copyright 2012 SRI International
# See LICENSE for other credits and copying information

# Look for global variables.
#
# Call it on all of the object files on the command line.
# It produces no output, and exits successfully,
# if no new globals have appeared; otherwise it prints error messages
# and exits unsuccessfully.

status=0
symbols=$(nm -o "$@" |
c++filt |
sed '
  # Tidy up the list and remove all symbols we do not care about.
  / [DBdb] /!d
  s/^build\///
  s/^x86_64-pc-linux-gnu-debug\///
  s/^x86_64-apple-darwin10.8.0-release\///
  s/^x86_64-apple-darwin10.8.0-debug\///
  s/^obj\///
  s/\.o: */ /
  s/\.obj: */ /
  s/ [0-9a-fA-F][0-9a-fA-F]* [DBdb] / /


  #disregard the object files that are not part of the library

  /frontend/d
  /^yices_smtcomp /d
  /^yices_sat /d
  /^yices_main /d
  /^smt2_lexer /d
  /^smt_lexer /d
  /^yices_reval /d

  # not doing mcsat this time
  /^mcsat.* /d

  #disregard the build generated global constants
   /^api\/yices_version /d

  # assumming the big structs are all constant
  /^solvers\/\w*\/\w* /d


  # This is the whitelist, in the form of a bunch of sed "d" commands.
  # It cares about both the names and the object files that define
  # them.  The above commands have stripped any leading src/ and/or
  # .o or .obj extension.

  /^bvpoly_buffers _seed$/d
  /^int_array_sort _seed$/d
  /^int_array_sort2 _seed$/d
  /^large_bvsets _seed$/d
  /^sat_solver _seed$/d
  /^power_products _seed$/d
  /^ptr_array_sort _seed$/d
  /^ptr_array_sort2 _seed$/d
  # these are protected by locks or are TLS
  /^api\/yices_api \w*_list$/d
  /^api\/yices_api \w*_list_lock$/d
  /^api\/yices_api \w*root_terms$/d
  /^api\/yices_api \w*root_types$/d
  /^api\/yices_api __yices_error$/d
  /^api\/yices_api __yices_error_initialized$/d

  /^api\/yices_api ctx_option_names$/d

  #static const char * const ..._names[...]
  /^api\/context_config \w*_names$/d
  /^api\/search_parameters branching_modes$/d
  /^api\/search_parameters param_key_names$/d
  /^api\/smt_logic_codes \w*_names$/d

  # should be local to init_solvers
  /^context\/context null_ctrl$/d
  /^context\/context null_smt$/d
  /^solvers\/egraph\/egraph_printer \w*2\w*$/d
  /^io\/term_printer \w*2\w*$/d
  /^io\/type_printer \w*2\w*$/d
  /^exists_forall\/ef_client \w*2\w*$/d
  /^parser_utils\/term_stack_error \w*2\w*$/d
  /^solvers\/cdcl\/smt_core_printer \w*2\w*$/d
  /^solvers\/cdcl\/gates_printer \w*2\w*$/d
  /^solvers\/simplex\/dsolver_printer \w*2\w*$/d

  # these look dead
  /^solvers\/egraph\/egraph_printer name$/d
  /^solvers\/egraph\/egraph_printer name_size$/d

  # constant
  /^mt\/yices_locks mattr$/d


  /^io\/yices_pp nonstandard_block/d
  /^io\/yices_pp standard_block/d

  /^parser_utils\/term_stack2 check/d
  /^parser_utils\/term_stack2 eval/d
  /^io\/yices_pp open_desc/d

  #handled by the global lock
  /^utils\/memalloc __out_of_mem_callback/d

  #not used by the API(???)
  /^utils\/timeout saved_handler/d
  /^utils\/timeout the_timeout/d


  /^terms\/neorationals string_buffer$/d
  /^terms\/neorationals string_buffer_length$/d
  /^terms\/neorationals string_buffer_lock$/d
')

if [ -n "$symbols" ]; then
    status=1
    echo '*** New global variables introduced:'
    set fnord $symbols
    shift
    while [ $# -gt 0 ]; do
        printf '  %s\t%s\n' "$1" "$2"
        shift 2
    done
fi
exit $status
