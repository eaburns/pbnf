#!/bin/bash

for nblocks in 2 4 8 10
do
    for (( threads=1; threads <= 10; threads++ ))
    do
	./run_grids.sh bfpsdd \
	    -t $threads \
	    -n $nblocks \
            $@
	done
done
