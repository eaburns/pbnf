#!/usr/bin/python
# buildtest.py
#
# Tests important algorithms after build.
#
# Seth Lemons
# October 31, 2008

import timeit, sys

if len(sys.argv) > 1 and sys.argv[1] == "--help":
    print "buildtest.py [nthreads] [nbperthread] [weight] [costbound]"
    exit(0)

if len(sys.argv) > 1:
    nthreads = str(sys.argv[1])
else:
    nthreads = "2"
if len(sys.argv) > 2:
    nbperthread = str(sys.argv[2])
else:
    nbperthread = "5"
if len(sys.argv) > 3:
    weight = str(sys.argv[3])
else:
    weight = "1.1"
if len(sys.argv) > 4:
    costbound = str(sys.argv[4])
else:
    costbound = "100"

algs = ["astar",
        #"idastar",
        #"bfs",
        #"costbounddfs-"+costbound,
        "kbfs-"+nthreads,
        "pastar-"+nthreads,
        #"psdd-"+nthreads+"-"+nbperthread,
        "dynpsdd-"+nthreads+"-"+nbperthread+"-"+weight,
        "pbnf-"+nthreads+"-"+nbperthread]

for alg in algs:
    print alg
    t = timeit.Timer('print Popen(["./search", alg], stdout=PIPE, stdin=infile).stdout.read()', 'from __main__ import alg; from subprocess import Popen,PIPE; infile = open("grid/jordan_unit_four-way_1200x2000_2")')
    print "%0.3f seconds\n\n" % t.timeit(number=1)
    
