#!/bin/bash

# settable by command-line args
THREADS=1
NBLOCKS=1
WEIGHT=1.0
PROB=0.25
WIDTH=2000
HEIGHT=1200
ALGORITHM=""

# constants
RDB_GET_PATH="/home/rai/eaburns/src/ocaml/rdb/rdb_get_path.unix_unknown"
GRID_SEARCH="./search.bin"
DATA_ROOT="/home/rai/group/data/grid_instances"
RUNS_ROOT="data"
OBSTACLES="uniform"
COSTS="Unit"
MOVES="Four-way"

USES_THREADS="kbfs pastar psdd dynpsdd pbnf multiastar"
USES_WEIGHT="dynpsdd"
USES_NBLOCKS="psdd dynpsdd pbnf"

if [ "$#" -eq 0 ]
then   # Script needs at least one command-line argument.
    echo -e "Usage:"
    echo -e "\
 run_grid.sh \
[-d <dimensions>] \
[-n <nblocks/thread>] \
[-p <prob>] \n        \
[-t <threads>] \
[-w <weight>] \
<algorithm>"
    exit 1
fi  

#
# Parse arugments
#
set -- `getopt "d:n:p:t:w:" "$@"`
while [ ! -z "$1" ]
do
    case "$1" in
	-a) ALGORITHM=$2 ; shift ;;
	-d) WIDTH=$(echo $2 | cut -dx -f1) ;
	    HEIGHT=$(echo $2 | cut -dx -f2) ;;
	-n) NBLOCKS=$2 ; shift ;;
	-p) PROB=$2 ; shift ;;
	-t) THREADS=$2 ; shift ;;
	-w) WEIGHT=$2 ; shift ;;
	*) break ;;
    esac
    shift
done

if [ -z "$2" ]
then
    echo "You must specify an algorithm"
    exit 1
fi
ALGORITHM=$2


#
# Test if the algorithm is on the given list
#
function alg_on_list {
    while [ ! -z "$1" ]
    do
	if [[ $ALGORITHM == $1 ]]
	then
	    return 0
	fi

	shift
    done

    return 1
}


#
# Get the list of paths for 
#
function paths ()
{
    ARGS=""
    ARGS+="obstacles=$OBSTACLES "
    ARGS+="costs=$COSTS "
    ARGS+="moves=$MOVES "
    ARGS+="prob=$PROB "
    ARGS+="width=$WIDTH "
    ARGS+="height=$HEIGHT "

    ARGS+="num=*"
    $RDB_GET_PATH $DATA_ROOT $ARGS | grep path | sed -n "s/path:\ //p"
}


#
# Get the path of the run-file for the given instance number
#
function run_file ()
{
    ARGS=""
    ARGS+="type=run "
    ARGS+="alg=$ALGORITHM "

    if alg_on_list $USES_THREADS
    then
	ARGS+="threads=$THREADS "
    fi

    if alg_on_list $USES_NBLOCKS
    then
	ARGS+="nblocks-per-thread=$NBLOCKS "
    fi

    if alg_on_list $USES_WEIGHT
    then 
	ARGS+="wt=$WEIGHT "
    fi

    ARGS+="obstacles=$OBSTACLES "
    ARGS+="costs=$COSTS "
    ARGS+="moves=$MOVES "
    ARGS+="prob=$PROB "
    ARGS+="width=$WIDTH "
    ARGS+="height=$HEIGHT "

    ARGS+="num=$1"
    $RDB_GET_PATH $RUNS_ROOT $ARGS | grep path | sed -n "s/path:\ //p"
}


#
# Get the full name of the search algorithm (possibly including
# threads, nblocks/thread, and weights).
#
function full_algo_name ()
{
    FULL_NAME="$1"

    if alg_on_list $USES_THREADS
    then
	FULL_NAME+="-$THREADS"
    fi

    if alg_on_list $USES_NBLOCKS
    then
	FULL_NAME+="-$NBLOCKS"
    fi

    if alg_on_list $USES_WEIGHT
    then
	FULL_NAME+="-$WEIGHT"
    fi

    echo $FULL_NAME
}


#
# Run all of the given instances
#
for INSTANCE in `ls $(paths)`
do
    NUM=$(basename $INSTANCE)
    if [[ $NUM == "KEY=num" ]]
    then
	continue
    fi

    OUT=$(run_file $NUM)
    FULL_NAME=$(full_algo_name $ALGORITHM)

    echo "Algorithm: $FULL_NAME"
    echo "Instance: $INSTANCE"
    echo "Output: $OUT"
    echo

    #
    # Header
    #
    (echo -e "#start data file format 4"
	echo -e "#pair  \"wall start date\"\t\"$(date)\""
	echo -e "#pair  \"wall start time\"\t\"NULL\""
	echo -e "#pair  \"machine id\"\t\"$(hostname -f)-$(uname -m)-$(uname -s)-$(uname -r)\""
	echo -e "#pair  \"alg\"\t\"$ALGORITHM\""

	if alg_on_list $USES_THREADS
	then
	    echo -e "#pair  \"threads\"\t\"$THREADS\""
	fi

	if alg_on_list $USES_NBLOCKS
	then
	    echo -e "#pair  \"nblocks-per-thread\"\t\"$NBLOCKS\""
	fi

	if alg_on_list $USES_WEIGHT
	then 
	    echo -e "#pair  \"wt\"\t\"$WEIGHT\""
	fi

#    echo -e "#pair  \"type\"\t\"instances\""
	echo -e "#pair  \"obstacles\"\t\"$OBSTACLES\""
	echo -e "#pair  \"costs\"\t\"$COSTS\""
	echo -e "#pair  \"moves\"\t\"$MOVES\""
	echo -e "#pair  \"prob\"\t\"$PROB\""
	echo -e "#pair  \"width\"\t\"$WIDTH\""
	echo -e "#pair  \"height\"\t\"$HEIGHT\""
	echo -e "#pair  \"num\"\t\"$NUM\"") > $OUT


    #
    # Preform the search
    #
    OUTPUT=$($GRID_SEARCH $FULL_NAME < $INSTANCE)
    SOL_COST=$(echo $OUTPUT | sed -n "s/.*cost: \([0-9.]\+\).*/\1/p")
    SOL_LENGTH=$(echo $OUTPUT | sed -n "s/.*length: \([0-9.]\+\).*/\1/p")
    WALL_TIME=$(echo $OUTPUT | sed -n "s/.*wall_time: \([0-9.]\+\).*/\1/p")
    CPU_TIME=$(echo $OUTPUT | sed -n "s/.*CPU_time: \([0-9.]\+\).*/\1/p")
    GENERATED=$(echo $OUTPUT | sed -n "s/.*generated: \([0-9.]\+\).*/\1/p")
    EXPANDED=$(echo $OUTPUT | sed -n "s/.*expanded: \([0-9.]\+\).*/\1/p")

    #
    # The data column
    #
    echo -e "#cols  \"sol cost\"\t\"sol length\"\t\"nodes expanded\"\t\"nodes generated\"\t\"wall time\"" >> $OUT
    echo -e "$SOL_COST\t$SOL_LENGTH\t$EXPANDED\t$GENERATED\t$WALL_TIME" >> $OUT

    #
    # The footer
    #
    (echo -e "#pair  \"final sol cost\"\t\"$SOL_COST\""
	echo -e "#pair  \"final sol length\"\t\"$SOL_LENGTH\""
	echo -e "#pair  \"total raw cpu time\"\t\"$CPU_TIME\""
	echo -e "#pair  \"total wall time\"\t\"$WALL_TIME\""
	echo -e "#pair  \"total nodes expanded\"\t\"$EXPANDED\""
	echo -e "#pair  \"total nodes generated\"\t\"$GENERATED\""
	echo -e "#pair  \"wall finish time\"\t\"NULL\""
	echo -e "#pair  \"wall finish date\"\t\"$(date)\""
	echo -e "#end data file format 4") >> $OUT

done

exit 0
