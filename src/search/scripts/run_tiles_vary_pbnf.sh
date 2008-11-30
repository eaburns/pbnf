#!/bin/bash

for min in 5 10 30 60 80
do
    for (( threads=1; threads <= 10; threads++ ))
    do
        ./scripts/run_tiles.sh pbnf -m $min -t $threads $@
    done
done
