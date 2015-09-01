#!/bin/bash

#
# The Yices SMT Solver. Copyright 2014 SRI International.
#
# This program may only be used subject to the noncommercial end user
# license agreement which is downloadable along with this program.
#

#
# Run regression tests
#
# Usage: check.sh <test-dir> <bin-dir>
#
# tests-dir contains test files in the SMT1, SMT2, or Yices input language
# bin-dir contains the Yices binaries for each of these languages
#
# For each test file, the expected resuts is stored in file.gold
# and command-line options are stored in file.options.
#
# This scripts calls the appropriate binary on each test file, passing it
# the command-line options if any, then check whether the output matches
# what's expected.
#

if test $# != 2 ; then
   echo "Usage: $0 <test-directory> <bin-directory>"
   exit
fi

regress_dir=$1
bin_dir=$2

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
# We try bash's builtin time command
#
TIMEFORMAT="%U"


#
# The temp file for output
#
outfile=`$mktemp_cmd` || { echo "Can't create temp file" ; exit 1 ; }
timefile=`$mktemp_cmd` || { echo "Can't create temp file" ; exit 1 ; }

fail=0
pass=0

if [[ -z "$REGRESS_FILTER" ]];
then
	REGRESS_FILTER="." 
fi

for file in `find "$regress_dir" -name '*.smt' -or -name '*.smt2' -or -name '*.ys' | grep $REGRESS_FILTER | sort`; do

    echo -n $file

    # Get the binary based on the filename
    filename=`basename "$file"`

    case $filename in
        *.smt2)
            binary=yices_smt2
            ;;
        *.smt)
            binary=yices_smtcomp
            ;;
        *.ys)
            binary=yices_main
            ;; 
        *)
            echo FAIL: unknown extension for $filename
            fail=`expr $fail + 1`
            continue
    esac

    # Get the options
    if [ -e "$file.options" ]
    then
        options=`cat $file.options`
        echo " [ $options ]"
    else
        options=
        echo
    fi


    # Get the expected result
    if [ -e "$file.gold" ]
    then
        gold=$file.gold
    else
        echo FAIL: missing file: $file.gold
        fail=`expr $fail + 1`
        continue
    fi

    # Run the binary
    (time  ./$bin_dir/$binary $options ./$file >& $outfile ) >&  $timefile
    thetime=`cat $timefile`

    # Do the diff
    diff -w $outfile $gold > /dev/null
  
    if [ $? -eq 0 ] 
    then
    	echo PASS [${thetime} s]
        pass=`expr $pass + 1`
    else
    	echo FAIL
        fail=`expr $fail + 1`
    fi
    
done

rm $outfile
rm $timefile

echo Pass: $pass
echo Fail: $fail

if [ $fail -eq 0 ]
then
    exit 0
else
    exit 1
fi
