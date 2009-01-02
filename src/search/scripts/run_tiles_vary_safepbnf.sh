#!/bin/bash

for min in 5 10 30 60 80 100 120 180
do
    for (( threads=1; threads <= 8; threads++ ))
    do
	./scripts/run_tiles.sh safepbnf -m $min -t $threads $@
    done
done
