#!/bin/bash

./run_vary_bfpsdd.sh $@
./run_vary_safepbnf.sh $@
./run_vary_pbnf.sh $@
./run_vary_dynpsdd.sh $@
./run_vary_psdd.sh $@
./run_vary_kbfs.sh $@
./run_vary_multiastar $@
./run_vary_pastar.sh $@
