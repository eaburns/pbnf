#!/bin/bash

for wt in 1.10 1.20 1.30 1.40 1.50 1.60 1.70 1.80 1.90 2.00
do
    for (( nblocks=1; nblocks <= 15; nblocks++ ))
    do
	for (( threads=1; threads <= 15; threads++ ))
	do
	    ./run_grids.sh dynpsdd \
		-t $threads \
		-n $nblocks \
		-w $wt
	done
    done
done
