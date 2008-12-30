#!/bin/bash

for nblocks in 10 100 625
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_grids.sh \
	    -t $threads \
	    -n $nblocks \
            $@ \
	    bfpsdd
	done
done
