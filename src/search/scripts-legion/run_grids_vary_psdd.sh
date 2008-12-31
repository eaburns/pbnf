#!/bin/bash

for nblocks in 100 2500 6400 10000
do
    for threads in 1 2 4 8 16 32
    do
	./scripts-legion/run_grids.sh \
	    -t $threads \
	    -n $nblocks \
            $@ \
	    psdd
    done
done
