#!/bin/bash

for nblocks in 2 10 40 100
do
    for (( threads=1; threads <= 10; threads++ ))
    do
	./scripts/run_grids.sh bfpsdd \
	    -t $threads \
	    -n $nblocks \
            $@
	done
done
