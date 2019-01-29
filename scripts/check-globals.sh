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

  #constant array of strings
  /^api\/yices_api ctx_option_names$/d


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
