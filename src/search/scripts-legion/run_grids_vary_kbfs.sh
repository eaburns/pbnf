#!/bin/bash

for threads in 1 2 4 8 16 32
do
	./scripts-legion/run_grids.sh \
	    -t $threads \
            $@ \
	    kbfs
done
