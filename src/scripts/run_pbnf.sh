#!/bin/bash

bin=./search.bin
runs=5
board="$1"

# Use A* to find the optimal cost so that we can make sure that we
# never find a suboptimal solution
true_cost=$($bin astar < $board 2>&1 | grep "cost" | cut -d\  -f2)

echo -e "# $(date)"
echo -e "# $(uname -n -o -m -r)"
echo -e "# Board: $board"
echo -e "# Cost: $true_cost"
echo -e "# Average over $runs runs"
printf "# %-15s %-15s %-15s\n" \
    "time (sec)" "threads" "nblocks/thread"

for ((h=1; h < 9; h++))
do
    for ((r=1; r < 10; r++))
    do
	sum=0
	for ((i=0; i < $runs; i++))
	do
	    output=$(/usr/bin/time -f%ereal $bin pbnf-$h-$r < $board 2>&1)
	    t=$(echo $output | cut -d\  -f15 | sed -n "s/real//p")
	    cost=$(echo $output | cut -d\  -f12)
	    if [[ cost -ne $true_cost ]]
	    then
		echo "-------------------- Bad cost $cost --------------------"
		echo $output
		exit 1
	    fi
	    sum=$(echo "scale=5; $sum + $t" | bc)
	done
	t=$(echo "scale=5; $sum / $runs" | bc)
	printf "  %-15.4f %-15d %-15d\n" $t $h $r
    done
done
