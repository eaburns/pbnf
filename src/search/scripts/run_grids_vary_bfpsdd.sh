#!/bin/bash

for min in 1 5 10 50
do
    for nblocks in 100 625 1600 2500
    do
	for (( threads=1; threads <= 8; threads++ ))
	do
	    ./scripts/run_grids.sh \
		-t $threads \
		-n $nblocks \
		-m $min \
		$@ \
		bfpsdd
	done
    done
done
