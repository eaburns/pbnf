#!/bin/bash

for (( threads=1; threads <= 10; threads++ ))
do
	./scripts/run_grids.sh prastar \
	    -t $threads \
            $@
done
