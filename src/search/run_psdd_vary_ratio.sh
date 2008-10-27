#!/bin/bash

threads=$1
board="grid/jordan_unit_four-way_1200x2000_2"

echo -e "# PSDD With $threads threads"
echo -e "# Board: $board"
printf "# %-20s %-20s %-20s\n" "time (sec)" "weight" "nblocks/thread"

for ((w=1; w < 6; w++))
do
    for ((r=1; r < 10; r++))
    do
	t=`(/usr/bin/time -f%ereal ./search dynpsdd-$threads-$r-1.$w \
	    < $board) 2>&1 | grep "real" | awk -Fr '{ print $1 }'`
	printf "  %-20.4f %-20.1f %-20d\n" $t "1.$w" $r

    done
done
