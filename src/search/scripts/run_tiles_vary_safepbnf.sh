#!/bin/bash

for min in 64
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_tiles.sh safepbnf -m $min -t $threads $@
    done
done
