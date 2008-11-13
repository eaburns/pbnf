#!/bin/bash

for nblocks in 1 5 10 15 20
do
    for (( threads=1; threads <= 10; threads++ ))
    do
	./run_grids.sh psdd \
	    -t $threads \
	    -n $nblocks
	done
done
