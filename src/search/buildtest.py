#!/usr/bin/python
# buildtest.py
#
# Tests important algorithms after build.
#
# Seth Lemons
# October 31, 2008

import timeit

nthreads = "2"
nbperthread = "5"
weight = "1.1"
costbound = "100"

algs = ["astar",
        #"idastar",
        #"bfs",
        #"costbounddfs-"+costbound,
        "kbfs-"+nthreads,
        #"psdd-"+nthreads+"-"+nbperthread,
        "dynpsdd-"+nthreads+"-"+nbperthread+"-"+weight,
        "pbnf-"+nthreads+"-"+nbperthread]

for alg in algs:
    print alg
    t = timeit.Timer('print Popen(["./search", alg], stdout=PIPE, stdin=infile).stdout.read()', 'from __main__ import alg; from subprocess import Popen,PIPE; infile = open("grid/jordan_unit_four-way_1200x2000_2")')
    print "%0.3f seconds\n\n" % t.timeit(number=1)
    
