#!/bin/bash

for nblocks in 100 625 1600 2500 6400 10000
do
    for (( threads=1; threads <= 10; threads++ ))
    do
	./scripts/run_grids.sh bfpsdd \
	    -t $threads \
	    -n $nblocks \
            $@
	done
done
