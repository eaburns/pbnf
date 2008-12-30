#!/bin/bash

for min in 5 60 100 120 180
#for min in 10 30 60 80
do
    for nblocks in 100 625 1600 2500 6400 10000
    do
	for (( threads=1; threads <= 8; threads++ ))
	do
	    ./scripts/run_grids.sh \
		-m $min \
		-t $threads \
		-n $nblocks \
                $@ \
		safepbnf
	done
    done
done
