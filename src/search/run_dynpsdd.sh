#!/bin/bash

board="$1"
runs=25

echo -e "# $(date)"
echo -e "# $(uname -n -o -m -r)"
echo -e "# Board: $board"
printf "# %-15s %-15s %-15s %-15s\n" \
    "time (sec)" "threads" "weight" "nblocks/thread"

for ((h=1; h < 9; h++))
do
    for ((w=1; w < 6; w++))
    do
	for ((r=1; r < 10; r++))
	do
	    sum=0
	    for ((i=0; i < $runs; i++))
	    do
		t=`(/usr/bin/time -f%ereal ./search dynpsdd-$h-$r-1.$w \
		    < $board) 2>&1 | grep "real" | awk -Fr '{ print $1 }'`
		sum=$(echo "scale=5; $sum + $t" | bc)
	    done
	    t=$(echo "scale=5; $sum / $runs" | bc)
	    printf "  %-15.4f %-15d %-15.2f %-15d\n" $t $h "1.$w" $r
	done
    done
done
