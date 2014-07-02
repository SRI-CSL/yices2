#!/bin/sh

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

#
# System-dependent configuration
# - the script uses mktemp and time
#
os_name=`uname 2>/dev/null` || os_name=unknown

mktemp_cmd=mktemp

#
# We try the builtin time command
#
time_cmd=time

case "$os_name" in
  *Darwin* )
     mktemp_cmd="mktemp -t out"
  ;;

esac

#
# The temp file for output
#
outfile=`$mktemp_cmd` || { echo "Can't create temp file" ; exit 1 ; }
timefile=`$mktemp_cmd` || { echo "Can't create temp file" ; exit 1 ; }

fail=0
pass=0

for file in `find "$regress_dir" -name '*.smt' -or -name '*.smt2' -or -name '*.ys'` ; do

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
    $time_cmd -f "%U" -o $timefile $bin_dir/$binary $options $file > $outfile 2>&1 
    thetime=`cat $timefile`

    # Do the diff
    diff $outfile $gold > /dev/null
  
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
