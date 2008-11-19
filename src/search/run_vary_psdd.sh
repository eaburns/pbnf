#!/bin/bash

for nblocks in 1 2 4 8 10
do
    for (( threads=1; threads <= 10; threads++ ))
    do
	./run_grids.sh psdd \
	    -t $threads \
	    -n $nblocks
	done
done
