#!/bin/bash
#
# Generate plots from an RDB.
#

GEN_PLOT=/home/rai/eaburns/src/ocaml/ps_plot/gen_plot.unix_unknown

# Some y keys.
#
# -ykey wall_ttime -ylabel time-seconds
# -ykey raw_exp -ylabel total-expansions



#
# Grid World
#
if $(`which false`)
then
MOVES=Four-way
COSTS=Unit
WIDTH=2000
HEIGHT=1200
PROB=25
$GEN_PLOT \
    -root /home/rai/eaburns/data/grid.old type=run \
    obstacles=uniform \
    moves=$MOVES \
    costs=$COSTS \
    width=$WIDTH \
    height=$HEIGHT \
    prob=0.$PROB \
    -xkey threads \
    -ykey wall_ttime -ylabel time-seconds \
    -title time-$COSTS-$MOVES-$WIDTH-$HEIGHT-0$PROB \
    -astar \
    -namedalg safepbnf safepbnf-80min-625nblocks "min-expansions=80 nblocks=625" \
    -namedalg bfpsdd bfpsdd-10nblocks "nblocks=100" \
    -alg kbfs ""
fi


#
# Sliding Tiles
#
if $(`which false`)
then
COLS=4
ROWS=3
$GEN_PLOT \
    -root /home/rai/eaburns/data/tiles type=run \
    model=random \
    cols=$COLS \
    rows=$ROWS \
    -xkey threads \
    -ykey wall_ttime -ylabel time-seconds \
    -title time-$COLS-$ROWS \
    -namedalg safepbnf safepbnf-80min "min-expansions=80" \
    -alg bfpsdd ""
fi

#
# Legion unit grid four-way runs
#
if $(`which true`)
then
MOVES=Four-way
COSTS=Unit
WIDTH=2000
HEIGHT=1200
PROB=35
$GEN_PLOT \
    -root /home/rai/eaburns/data/legion/grid type=run \
    obstacles=uniform \
    moves=$MOVES \
    costs=$COSTS \
    width=$WIDTH \
    height=$HEIGHT \
    prob=0.$PROB \
    -xkey threads \
    -ykey wall_ttime -ylabel time-seconds \
    -title time-$COSTS-$MOVES-$WIDTH-$HEIGHT-0$PROB \
    -astar \
    -namedalg safepbnf safepbnf-60min-2500nblocks "min-expansions=60 nblocks=2500" \
    -namedalg bfpsdd bfpsdd-50min-2500nblocks "min-expansions=50 nblocks=2500"
fi
