#!/bin/bash

for nblocks in 10 100 625
do
    for threads in 1 2 4 8 16 32
    do
	./scripts-legion/run_grids.sh \
	    -t $threads \
	    -n $nblocks \
            $@ \
	    bfpsdd
	done
done
