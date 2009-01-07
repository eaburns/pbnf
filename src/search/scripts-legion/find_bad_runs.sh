#!/bin/bash
#
# Recursively looks at all of the files in an RDB and prints a message
# if any of the result files are incomplete.
#

BASE=$1

for FILE in `ls $1`
do
    test -d $BASE/$FILE && {
	./find_bad_runs.sh $BASE/$FILE
    } || {
	if ! (echo $FILE | grep KEY >& /dev/null)
	then
	    if (cat $BASE/$FILE | grep "\"\"" >& /dev/null)
	    then
		echo "Bad Run: $BASE/$FILE"
		rm ${BASE}/${FILE}
	    fi
	fi
    }
done
