#!/bin/bash

for (( threads=1; threads <= 10; threads++ ))
do
	./run_grids.sh multiastar \
	    -t $threads \
            $@
done
