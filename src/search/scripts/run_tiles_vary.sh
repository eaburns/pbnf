#!/bin/bash

./scripts/run_tiles_vary_bfpsdd.sh $@
./scripts/run_tiles_vary_safepbnf.sh $@
./scripts/run_tiles_vary_pbnf.sh $@
./scripts/run_tiles_vary_dynpsdd.sh $@
./scripts/run_tiles_vary_psdd.sh $@
./scripts/run_tiles_vary_kbfs.sh $@
./scripts/run_tiles_vary_multiastar $@
./scripts/run_tiles_vary_pastar.sh $@
