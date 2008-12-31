#!/bin/bash

for wt in 1.1 1.5 2.2
do
    for nblocks in 10 100 625
    do
	for threads in 1 2 4 8 16 32
	do
	    ./scripts-legion/run_grids.sh \
		-t $threads \
		-n $nblocks \
		-w $wt \
                $@ \
		dynpsdd
	done
    done
done
