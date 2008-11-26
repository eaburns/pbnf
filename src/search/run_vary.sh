#!/bin/bash

./run_grid_vary_bfpsdd.sh $@
./run_grid_vary_safepbnf.sh $@
./run_grid_vary_pbnf.sh $@
./run_grid_vary_dynpsdd.sh $@
./run_grid_vary_psdd.sh $@
./run_grid_vary_kbfs.sh $@
./run_grid_vary_multiastar $@
./run_grid_vary_pastar.sh $@
