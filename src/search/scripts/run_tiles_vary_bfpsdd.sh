#!/bin/bash

for min in 1 64
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_tiles.sh bfpsdd -t $threads -m $min $@
    done
done
