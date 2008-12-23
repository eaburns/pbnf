#!/bin/bash

for nblocks in 100 2500 6400 10000
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_grids.sh psdd \
	    -t $threads \
	    -n $nblocks \
            $@
    done
done
