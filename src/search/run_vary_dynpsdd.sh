#!/bin/bash

for wt in 1.1 1.5 2.0 2.2
do
    for nblocks in 1 2 4 8 10
    do
	for (( threads=1; threads <= 10; threads++ ))
	do
	    ./run_grids.sh dynpsdd \
		-t $threads \
		-n $nblocks \
		-w $wt
	done
    done
done
