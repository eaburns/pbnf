#!/bin/bash

for wt in 1.1 1.5 2.0 2.2
do
    for nblocks in 100 625 1600 2500 6400 10000
    do
	for (( threads=1; threads <= 10; threads++ ))
	do
	    ./scripts/run_grids.sh dynpsdd \
		-t $threads \
		-n $nblocks \
		-w $wt \
                $@
	done
    done
done
