#!/bin/bash

# 15GB virtual memory limit
ulimit -v 15000000

./scripts/run_grids_vary_bfpsdd.sh $@
./scripts/run_grids_vary_safepbnf.sh $@
./scripts/run_grids_vary_prastar.sh $@
./scripts/run_grids_vary_pastar.sh $@
./scripts/run_grids_vary_pbnf.sh $@
./scripts/run_grids_vary_kbfs.sh $@
#./scripts/run_grids_vary_psdd.sh $@
#./scripts/run_grids_vary_dynpsdd.sh $@
#./scripts/run_grids_vary_multiastar $@
