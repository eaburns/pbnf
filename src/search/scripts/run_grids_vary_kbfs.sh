#!/bin/bash

for (( threads=1; threads <= 8; threads++ ))
do
	./scripts/run_grids.sh \
	    -t $threads \
            $@ \
	    kbfs
done
