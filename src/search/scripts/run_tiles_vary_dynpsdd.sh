#!/bin/bash

for wt in 1.1 1.5 2.0 2.2
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_tiles.sh dynpsdd -t $threads -w $wt $@
    done
done
