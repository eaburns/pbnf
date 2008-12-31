#!/bin/bash

# 5GB virtual memory limit
ulimit -v 5000000

./scripts-legion/run_grids_vary_bfpsdd.sh $@
./scripts-legion/run_grids_vary_safepbnf.sh $@
./scripts-legion/run_grids_vary_pastar.sh $@
./scripts-legion/run_grids_vary_pbnf.sh $@
./scripts-legion/run_grids_vary_kbfs.sh $@
./scripts-legion/run_grids_vary_psdd.sh $@
./scripts-legion/run_grids_vary_dynpsdd.sh $@
#./scripts-legion/run_grids_vary_multiastar $@
