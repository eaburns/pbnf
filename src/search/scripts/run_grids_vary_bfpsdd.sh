#!/bin/bash

for min in 1 50 64 100 150 200 250
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
