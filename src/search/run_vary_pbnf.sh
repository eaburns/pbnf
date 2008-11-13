#!/bin/bash

for alg in "safe" ""
do
    for min in 1 10 20 50
    do
	for nblocks in 1 5 10 15 20
	do
	    for (( threads=1; threads <= 10; threads++ ))
	    do
		./run_grids.sh ${alg}pbnf \
		    -m $min \
		    -t $threads \
		    -n $nblocks
	    done
	done
    done
done
