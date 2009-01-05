#!/bin/bash

# 15GB virtual memory limit
ulimit -v 15000000

./scripts/run_tiles_vary_bfpsdd.sh $@
./scripts/run_tiles_vary_safepbnf.sh $@
./scripts/run_tiles_vary_pbnf.sh $@
./scripts/run_tiles_vary_pastar.sh $@
./scripts/run_tiles_vary_kbfs.sh $@
./scripts/run_tiles_vary_prastar.sh $@

# use IDPSDD, there is no way PSDD can do a tiles puzzle well.
#./scripts/run_tiles_vary_psdd.sh $@
#./scripts/run_tiles_vary_idpsdd.sh $@

# this is *way* slow on tiles
#./scripts/run_tiles_vary_dynpsdd.sh $@

#./scripts/run_tiles_vary_multiastar $@
