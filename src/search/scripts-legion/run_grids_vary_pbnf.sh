#!/bin/bash

for min in 5 10 30 60 80
do
    for nblocks in 100 2500 6400 10000
    do
	for threads in 1 2 4 8 16 32
	do
	    ./scripts-legion/run_grids.sh \
		-m $min \
		-t $threads \
		-n $nblocks \
                $@ \
		pbnf
	done
    done
done
