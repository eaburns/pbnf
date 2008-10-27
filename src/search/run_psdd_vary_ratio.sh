#!/bin/bash

threads=$1
board="grid/jordan_unit_four-way_500x500_2"

echo -e "# PSDD With $threads threads"
echo -e "# Board: $board"
echo -e "# weight\tnblocks/thread\t\ttime (seconds)"
for ((j=1; j < 6; j++))
do
    for ((i=1; i < 10; i++))
    do
	printf "  1.%d\t\t%2d\t\t\t" $j $i
	(/usr/bin/time -f%ereal ./search dynpsdd-$threads-$i-1.$j \
	    < $board) 2>&1 | grep "real" | awk -Fr '{ print $1 }'
    done
done
