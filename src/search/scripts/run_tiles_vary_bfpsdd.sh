#!/bin/bash

for min in 1 5 10 50
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_tiles.sh bfpsdd -t $threads -m $min $@
    done
done
