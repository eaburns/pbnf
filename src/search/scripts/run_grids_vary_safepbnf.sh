#!/bin/bash

for min in 5 10 30 60 80 100 120 180
#for min in 10 30 60 80
do
    for nblocks in 100 625 1600 2500 6400 10000
    do
	for (( threads=1; threads <= 10; threads++ ))
	do
	    ./scripts/run_grids.sh safepbnf \
		-m $min \
		-t $threads \
		-n $nblocks \
                $@
	done
    done
done
