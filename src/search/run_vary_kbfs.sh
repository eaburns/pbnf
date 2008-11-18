#!/bin/bash

for (( threads=1; threads <= 10; threads++ ))
do
	./run_grids.sh kbfs \
	    -t $threads
done
