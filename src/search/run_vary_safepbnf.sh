#!/bin/bash

for min in 5 15 25 30
do
    for nblocks in 1 2 4 5 6 8 10 12 15 20
    do
	for (( threads=1; threads <= 15; threads++ ))
	do
	    ./run_grids.sh safepbnf \
		-m $min \
		-t $threads \
		-n $nblocks
	done
    done
done
