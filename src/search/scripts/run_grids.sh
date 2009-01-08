#!/bin/bash

# settable by command-line args
THREADS=1
NBLOCKS=1
WEIGHT=1.0
PROB=0.35
WIDTH=2000
HEIGHT=1200
ALGORITHM=""

# constants
if [[ $(uname -m) == "sun4v" ]]; then
	RDB_GET_PATH="/home/rai/eaburns/src/ocaml/rdb/rdb_get_path.SunOS"
	GRID_SEARCH="./grid_search.sun4v.bin"
	RUNS_ROOT="/home/rai/eaburns/data/legion/grid"
else
	RDB_GET_PATH="/home/rai/eaburns/src/ocaml/rdb/rdb_get_path.unix_unknown"
	GRID_SEARCH="./grid_search.x86_64.bin"
	RUNS_ROOT="/home/rai/eaburns/data/grid"
fi
DATA_ROOT="/home/rai/group/data/grid_instances"
OBSTACLES="uniform"
COSTS="Unit"
MOVES="Four-way"

USES_THREADS="kbfs pastar psdd dynpsdd pbnf safepbnf multiastar bfpsdd prastar"
USES_WEIGHT="dynpsdd"
USES_NBLOCKS="psdd dynpsdd pbnf safepbnf bfpsdd prastar"
USES_MIN_EXPANSIONS="safepbnf pbnf bfpsdd"

if [ "$#" -eq 0 ]
then   # Script needs at least one command-line argument.
    echo -e "Usage:"
    echo -e "\
 run_grid.sh \
[-d <dimensions>] \
[-p <prob>] \
[-c <costs>] \
[-v <moves>] \
[-o <obstacles>] \
[-n <nblocks>] \
[-t <threads>] \
[-w <weight>] \
[-m <min_expansions>] \
<algorithm>"
    exit 1
fi  

#
# Parse arugments
#
set -- `getopt "o:c:d:m:n:p:t:w:v:" "$@"`
while [ ! -z "$1" ]
do
    case "$1" in
	-d) WIDTH=$(echo $2 | cut -dx -f1) ;
	    HEIGHT=$(echo $2 | cut -dx -f2) ;;
	-m) MIN_EXPANSIONS=$2 ; shift ;;
	-v) MOVES=$2 ; shift ;;
	-n) NBLOCKS=$2 ; shift ;;
	-p) PROB=$2 ; shift ;;
	-p) PROB=$2 ; shift ;;
	-c) COSTS=$2 ; shift ;;
	-o) OBSTACLES=$2 ; shift ;;
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

    ARGS="${ARGS}obstacles=$OBSTACLES "

    # This is Jordan's fault.
    if [[ "$OBSTACLES" == "lines" ]]
    then
	ARGS="${ARGS}:type=instance "
    fi

    ARGS="${ARGS}costs=$COSTS "
    ARGS="${ARGS}moves=$MOVES "
    ARGS="${ARGS}prob=$PROB "
    ARGS="${ARGS}width=$WIDTH "
    ARGS="${ARGS}height=$HEIGHT "

    ARGS="${ARGS}num=*"
    $RDB_GET_PATH $DATA_ROOT $ARGS | grep path | sed -n "s/path:\ //p"
}


#
# Get the path of the run-file for the given instance number
#
function run_file ()
{
    ARGS=""
    ARGS="${ARGS}type=run "
    ARGS="${ARGS}alg=$ALGORITHM "

    if alg_on_list $USES_MIN_EXPANSIONS
    then
	ARGS="${ARGS}min-expansions=$MIN_EXPANSIONS "
    fi

    if alg_on_list $USES_THREADS
    then
	ARGS="${ARGS}threads=$THREADS "
    fi

    if alg_on_list $USES_NBLOCKS
    then
	ARGS="${ARGS}nblocks=$NBLOCKS "
    fi

    if alg_on_list $USES_WEIGHT
    then 
	ARGS="${ARGS}wt=$WEIGHT "
    fi

    ARGS="${ARGS}obstacles=$OBSTACLES "
    ARGS="${ARGS}costs=$COSTS "
    ARGS="${ARGS}moves=$MOVES "
    ARGS="${ARGS}prob=$PROB "
    ARGS="${ARGS}width=$WIDTH "
    ARGS="${ARGS}height=$HEIGHT "

    ARGS="${ARGS}num=$1"
    $RDB_GET_PATH $RUNS_ROOT $ARGS | grep path | sed -n "s/path:\ //p"
}


#
# Get the full name of the search algorithm (possibly including
# threads, nblocks, and weights).
#
function full_algo_name ()
{
    FULL_NAME="$1"

    if alg_on_list $USES_MIN_EXPANSIONS
    then
	FULL_NAME="${FULL_NAME}-$MIN_EXPANSIONS"
    fi
	
    if alg_on_list $USES_THREADS
    then
	FULL_NAME="${FULL_NAME}-$THREADS"
    fi

    if alg_on_list $USES_NBLOCKS
    then
	FULL_NAME="${FULL_NAME}-$NBLOCKS"
    fi

    if alg_on_list $USES_WEIGHT
    then
	FULL_NAME="${FULL_NAME}-$WEIGHT"
    fi

    echo $FULL_NAME
}

#
# Sleep if there are users on the machine.
#
function wait_for_free_machine ()
{
    while `which true`
    do

    PRINTED=0
    USERS=$(w -h | grep -v ${USER} | wc -l)
    if [[ $USERS -eq 0 ]]
    then
        return
    fi

    while [[ $USERS -gt 0 ]]
    do
	if [[ $PRINTED -eq 0 ]]
	then
	    PRINTED=1
	    echo "Sleeping because the machine is in use"
	fi
	sleep 5
	USERS=$(w -h | grep -v ${USER} | wc -l)
    done

    PRINTED_LOAD=0
    INT_LOAD=$(w | head -n 1 | sed -n "s/.* load average: \([0-9.]*\),.*/\1 * 100/p" | bc | cut -d. -f 1)
    LOAD=$(w | head -n 1 | sed -n "s/.* load average: \([0-9.]*\),.*/\1/p")
    echo $LOAD
    while [[ $INT_LOAD -gt 5 ]]
    do
	if [[ $PRINTED_LOAD -eq 0 ]]
	then
	    PRINTED_LOAD=1
	    echo "Sleeping because the machine load is $LOAD"
	fi
        sleep 30
        INT_LOAD=$(w | head -n 1 | sed -n "s/.* load average: \([0-9.]*\),.*/\1 * 100/p" | bc | cut -d. -f 1)
    done

    done

    LOAD=$(w | head -n 1 | sed -n "s/.* load average: \([0-9.]*\),.*/\1/p")
    if [[ $PRINTED -eq 1 ]]
    then
	echo "Resuming with load $LOAD"
    fi
}

# user/group +rwx
umask 0002

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

    test -e $OUT && {
	echo "Skipping $OUT"
	continue
    }

    echo "Algorithm: $FULL_NAME"
    echo "Instance: $INSTANCE"
    echo "Output: $OUT"
    echo

    wait_for_free_machine

    #
    # Header
    #
    (echo -e "#start data file format 4"
	echo -e "#pair  \"wall start date\"\t\"$(date)\""
	echo -e "#pair  \"wall start time\"\t\"NULL\""
	echo -e "#pair  \"machine id\"\t\"$(hostname)-$(uname -m)-$(uname -s)-$(uname -r)\""
	echo -e "#pair  \"alg\"\t\"$ALGORITHM\""

	if alg_on_list $USES_MIN_EXPANSIONS
	then
	    echo -e "#pair  \"min-expansions\"\t\"$MIN_EXPANSIONS\""
	fi

	if alg_on_list $USES_THREADS
	then
	    echo -e "#pair  \"threads\"\t\"$THREADS\""
	fi

	if alg_on_list $USES_NBLOCKS
	then
	    echo -e "#pair  \"nblocks\"\t\"$NBLOCKS\""
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
    OUTPUT=$($GRID_SEARCH $FULL_NAME < $INSTANCE 2>&1)
    if [[ $? -ne "0" ]]; then
	echo "Run failed:"
        echo "failed: $OUT" >> ~/aborted.log
	echo $OUTPUT
	rm $OUT
	continue
    fi
    if [[ $(echo $OUTPUT | sed -n "s/.*cost: \(infinity\).*/\1/p") == "infinity" ]]; then
	SOL_COST="infinity"
    else
	    SOL_COST=$(echo $OUTPUT | sed -n "s/.*cost: \([0-9][0-9.]*\).*/\1/p")
    fi

    if [[ $(echo $OUTPUT | sed -n "s/.*length: \(infinity\).*/\1/p") == "infinity" ]]; then
	    SOL_LENGTH="infinity"
    else
	    SOL_LENGTH=$(echo $OUTPUT | sed -n "s/.*length: \([0-9][0-9.]*\).*/\1/p")
    fi

    if [[ $(echo $OUTPUT | sed -n "s/.*wall_time: \(infinity\).*/\1/p") == "infinity" ]]; then
	    WALL_TIME="infinity"
    else
	    WALL_TIME=$(echo $OUTPUT | sed -n "s/.*wall_time: \([0-9][0-9.]*\).*/\1/p")
    fi

    if [[ $(echo $OUTPUT | sed -n "s/.*CPU_time: \(infinity\).*/\1/p") == "infinity" ]]; then
	    CPU_TIME="infinity"
    else
	    CPU_TIME=$(echo $OUTPUT | sed -n "s/.*CPU_time: \([0-9][0-9.]*\).*/\1/p")
    fi

    if [[ $(echo $OUTPUT | sed -n "s/.*generated: \(infinity\).*/\1/p") == "infinity" ]]; then
	    GENERATED="infinity"
    else
	    GENERATED=$(echo $OUTPUT | sed -n "s/.*generated: \([0-9][0-9.]*\).*/\1/p")
    fi

    if [[ $(echo $OUTPUT | sed -n "s/.*expanded: \(infinity\).*/\1/p") == "infinity" ]]; then
	    EXPANDED="infinity"
    else
	    EXPANDED=$(echo $OUTPUT | sed -n "s/.*expanded: \([0-9][0-9.]*\).*/\1/p")
    fi

    if (echo $OUTPUT | grep "bad_alloc" >& /dev/null)
    then
	echo "Run Aborted"
        echo "aborted: $OUT" >> ~/aborted.log
	SOL_COST="infinity"
	SOL_LENGTH="infinity"
	WALL_TIME="infinity"
	CPU_TIME="infinity"
	GENERATED="infinity"
	EXPANDED="infinity"
    elif !(echo $OUTPUT | grep "No Solution" >& /dev/null)
    then
	#
	# The data column
	#
	echo -e "#cols  \"sol cost\"\t\"sol length\"\t\"nodes expanded\"\t\"nodes generated\"\t\"wall time\"" >> $OUT
	echo -e "$SOL_COST\t$SOL_LENGTH\t$EXPANDED\t$GENERATED\t$WALL_TIME" >> $OUT
    elif (echo $OUTPUT | grep "\"\"" >& /dev/null)
    then
	echo "BAD RUN, output:"
        echo "bad: $OUT" >> ~/aborted.log
	echo $OUTPUT
	exit
    fi

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
	echo -e "#pair  \"wall finish date\"\t\"$(date)\"") >> $OUT

    if (echo $OUTPUT | grep "expansions-per-nblock:" >& /dev/null)
    then
	EXP_PER_NBLOCK=$(echo $OUTPUT | sed -n "s/.*expansions-per-nblock: \([0-9.]\+\|infinity\).*/\1/p")
	echo -e "#pair  \"exp_per_nblock\"\t\"$EXP_PER_NBLOCK\"" >> $OUT
    fi
    echo -e "#end data file format 4" >> $OUT


    # Put the file in the AI group
    chgrp ai $OUT
done

exit 0
