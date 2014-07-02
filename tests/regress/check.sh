#!/bin/bash

REGRESS_DIR=$1
BIN_DIR=$2

FAIL=0

# The temp file for output
OUTFILE=`mktemp`
TIMEFILE=`mktemp`

for file in `find $REGRESS_DIR -name '*.smt' -or -name '*.smt2' -or -name '*.ys'`;
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
        echo Missing expected result
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
            BINARY=yices_smtcomp
            ;;
        ys)
            BINARY=yices_main
            ;; 
        *)
            echo unknown extension
            let FAIL=$FAIL+1
            continue
    esac
        
    # Run the binary
    /usr/bin/time -f "%U" -o $TIMEFILE $BIN_DIR/$BINARY $OPTIONS $file >& $OUTFILE
	TIME=`cat $TIMEFILE`

    # Do the diff
    diff $OUTFILE $GOLD
  
    if [ $? -eq 0 ];
    then
    	echo PASS [${TIME}s]
        let PASS=$PASS+1
    else
    	echo FAIL
        let FAIL=$FAIL+1
    fi
    
done;

rm $OUTFILE
rm $TIMEFILE

echo Pass: $PASS
echo Fail: $FAIL

if [ $FAIL -eq 0 ];
then
    exit 0
else
    exit -1
fi
