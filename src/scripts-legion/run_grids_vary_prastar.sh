#!/bin/bash

for threads in 1 2 4 8 16 32
do
	./scripts/run_grids.sh \
	    -t $threads \
            $@ \
	    prastar
done
