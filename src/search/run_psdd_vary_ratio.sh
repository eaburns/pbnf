#!/bin/bash

LIMIT=20
threads=$1

echo -e "# PSDD With $threads threads"
echo -e "# nblocks/thread\t\ttime (seconds)"
for ((i=1; i < LIMIT; i++))
do
    printf "  %2d\t\t\t\t" $i
    (/usr/bin/time -f%ereal ./search psdd-$threads-$i \
	< grid/jordan_unit_four-way_1200x2000_1) 2>&1 \
	| grep "real" | awk -Fr '{ print $1 }'
done
