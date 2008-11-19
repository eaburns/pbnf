#!/bin/bash

for min in 5 10 30 60 80
do
    for nblocks in 1 5 10 15 20
    do
	for (( threads=1; threads <= 10; threads++ ))
	    ./run_grids.sh pbnf \
		-m $min \
		-t $threads \
		-n $nblocks
	done
    done
done
