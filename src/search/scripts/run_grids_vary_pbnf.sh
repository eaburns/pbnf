#!/bin/bash

for min in 5 10 30 60 80 120 180 200 256
do
    for nblocks in 625 1600 2500 6400
    do
	for (( threads=1; threads <= 8; threads++ ))
	do
	    ./scripts/run_grids.sh \
		-m $min \
		-t $threads \
		-n $nblocks \
                $@ \
		pbnf
	done
    done
done
