#!/bin/bash

REGRESS_DIR=$1
BIN_DIR=$2

FAIL=0

# The temp file for output
OUTFILE=`mktemp`

for file in `find $REGRESS_DIR -name '*.smt' -or -name '*.smt2'`;
do

    echo -n $file

    # Get the options
    if [ -e "$file.options" ]
    then
        OPTIONS=`cat $file.options`
        echo " [ $OPTIONS ]"
    else
        OPTIONS=
        echo
    fi

    # Get the expected result
    if [ -e "$file.gold" ]
    then
        GOLD=$file.gold
    else
        echo Missing extpeced result
        let FAIL=$FAIL+1
        continue 
    fi    

    # Get the binary based on the filename
    filename=$(basename "$file")
    extension="${filename##*.}"    
    case "$extension" in
        smt2)
            BINARY=yices_smt2
            ;;
        smt)
            BINARY=yices_smt
            ;;
        ys)
            BINARY=yices
            ;; 
        *)
            echo unknown extension
            let FAIL=$FAIL+1
    esac
    
    # Run the binary
    $BIN_DIR/$BINARY $OPTIONS $file > $OUTFILE

    # Do the diff
    diff $OUTFILE $GOLD
  
    if [ $? -eq 0 ];
    then
        let PASS=$PASS+1
    else
        let FAIL=$FAIL+1
    fi
    
done;

rm $OUTFILE

echo Pass: $PASS
echo Fail: $FAIL

if [ $FAIL -eq 0 ];
then
    exit 0
else
    exit -1
fi
