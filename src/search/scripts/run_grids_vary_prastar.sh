#!/bin/bash

for nblocks in 625 1600 2500 6400
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_grids.sh \
	    -t $threads \
	    -n $nblocks \
            $@ \
	    prastar
    done
done
