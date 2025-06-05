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
# Run one test 
#
# Usage: run_test.sh <binary>
#
# The binary is expected to take no arguments and to terminate with exit code 0
# if the test passes or with exit code 1 if the code is to be skipped.
# (For example, a test that needs mcsat can check whether yices_has_mcsat() is
# false before doing anything then call exit(1)).
# Any other exit code is interpreted as an error.
# 

if test $# != 1; then
   echo "Usage: $0 <binary>"
   exit
fi

# Make sure fatal errors go to stderr
export LIBC_FATAL_STDERR_=1

#
# System-dependent configuration
#
os_name=`uname 2>/dev/null` || os_name=unknown

case "$os_name" in
  *Darwin* )
     mktemp_cmd="/usr/bin/mktemp -t out"
  ;;

  * )
     mktemp_cmd=mktemp
  ;;

esac

#
# The test
#
test=$1

if [[ -z "$TIME_LIMIT" ]];
then
  TIME_LIMIT=60
fi


#
# We try bash's builtin time command
#
TIMEFORMAT="%U"

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
# Temp files for output
#
outfile=`$mktemp_cmd` || { echo "Can't create temp file" ; exit 1 ; }
timefile=`$mktemp_cmd` || { echo "Can't create temp file" ; exit 1 ; }

#
# Run the test and report result
#
shortname=`basename $test`
strippedname=` echo $test | sed -e 'sX../../XX' `
echo $strippedname

ulimit -S -t $TIME_LIMIT &> /dev/null
ulimit -H -t $((1+$TIME_LIMIT)) &> /dev/null
(time $test >& $outfile ) >& $timefile
exitcode=$?
thetime=`cat $timefile`

case $exitcode in
    0) 
	echo -n $green
	echo PASS [$thetime s]
	echo -n $black
	echo PASS $shortname >> tests.log
	;;

    1)
	echo -n $yellow
	echo SKIP
	echo -n $black
	echo SKIP $shortname >> tests.log
	;;

    *)
	echo -n $red
	echo FAIL
	echo -n $black
	cp $outfile ${shortname}.log
	echo FAIL $shortname >> tests.log
	;;

esac

# Propagate the test's exit code
exit $exitcode
