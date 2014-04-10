#! /bin/sh
# Copyright 2012 SRI International
# See LICENSE for other credits and copying information

# Due to the multi-listener architecture of stegotorus, nearly all
# global variables are bugs.  This program enforces a white-list of
# global variables (in stegotorus itself) that are known to be okay.
# It's called from the Makefile with all of stegotorus's object files
# on the command line.  It produces no output, and exits successfully,
# if no new globals have appeared; otherwise it prints error messages
# and exits unsuccessfully.

status=0
symbols=$(nm -o "$@" |
c++filt |
sed '
  # Tidy up the list and remove all symbols we do not care about.
  / [DBdb] /!d
  s/^build\///
  s/^x86_64-apple-darwin10.8.0-release\///
  s/^x86_64-apple-darwin10.8.0-debug\///
  s/^obj\///
  s/\.o: */ /
  s/\.obj: */ /
  s/ [0-9a-fA-F][0-9a-fA-F]* [DBdb] / /


  #disregard the object files that are not part of the library

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


')

if [ -n "$symbols" ]; then
    status=1
    echo '*** New global variables introduced:'
    set fnord $symbols
    shift
    while [ $# -gt 0 ]; do
        printf '  %s.o\t%s\n' "$1" "$2"
        shift 2
    done
fi
exit $status
