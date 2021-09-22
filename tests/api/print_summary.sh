#!/bin/bash

#
#  This file is part of the Yices SMT Solver.
#  Copyright (C) SRI International.
#
#  Yices is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  Yices is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with Yices.  If not, see <http://www.gnu.org/licenses/>.
#

#
# Print summary of a set of tests
#
# Usage: print_summary.sh <logfile>
#
# The logfile is expected to contain one line per test of the form
#   <status> <testname>
# <status> is either PASS, or FAIL, or SKP
# <testname> is the test (binary name)
#

if test $# != 1; then
   echo "Usage: $0 <logfile>"
   exit
fi

logfile=$1

#
# Output colors
#
red=
green=
black=
if test -t 1 ; then
  red=`tput setaf 1`
  green=`tput setaf 2`
  yellow=`tput setaf 3`
  black=`tput sgr0`
fi

#
# Total number of tests
#
total=`cat $logfile | wc -l`
passed=`grep -c PASS $logfile`
skipped=`grep -c SKIP $logfile`
failed=`grep -c FAIL $logfile`

if [ $failed -eq 0 ]; then
  echo -n $green
  echo "Total:" $total
  echo "Pass: " $passed
  echo "Skip: " $skipped
  echo "Fail: " $failed
  echo -n $black
else
  echo -n $red
  echo "Total:" $total
  echo "Pass: " $passed
  echo "Skip: " $skipped
  echo "Fail: " $failed
  echo -n $black
fi
