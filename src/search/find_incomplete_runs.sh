#!/bin/bash
#
# Recursively looks at all of the files in an RDB and prints a message
# if any of the result files are incomplete.
#

BASE=$1

CHECKED=0
for FILE in `ls $1`
do
    test -d $BASE/$FILE && {
	./find_incomplete_runs.sh $BASE/$FILE
    } || {
	if ! (echo $FILE | grep KEY >& /dev/null)
	then
	    let CHECKED=$CHECKED+1
	    if ! (cat $BASE/$FILE | grep "#end" >& /dev/null)
	    then
		echo "Incomplete: $BASE/$FILE"
	    fi
	fi
    }
done

echo "Checked $CHECKED files."
