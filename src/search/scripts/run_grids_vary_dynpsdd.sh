#!/bin/bash

for wt in 1.1 1.5 2.2
do
    for nblocks in 10 100 625
    do
	for (( threads=1; threads <= 8; threads++ ))
	do
	    ./scripts/run_grids.sh dynpsdd \
		-t $threads \
		-n $nblocks \
		-w $wt \
                $@
	done
    done
done
