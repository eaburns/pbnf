#!/bin/bash

./scripts/run_grids_vary_bfpsdd.sh $@
./scripts/run_grids_vary_safepbnf.sh $@
./scripts/run_grids_vary_pbnf.sh $@
./scripts/run_grids_vary_safepbnf2.sh $@
./scripts/run_grids_vary_pbnf2.sh $@
./scripts/run_grids_vary_dynpsdd.sh $@
./scripts/run_grids_vary_psdd.sh $@
./scripts/run_grids_vary_kbfs.sh $@
./scripts/run_grids_vary_multiastar $@
./scripts/run_grids_vary_pastar.sh $@
