#!/usr/bin/python
# random_gen.py
#
# Prints a series of unique, solvable, randomly generated sliding tiles boards 
# of given size until killed.
#
# sna4 March 2009


import random, sys, time

def usage():
    print "usage: gen_random.py [size]"
    print "\tprints unique, solvable, randomly generated sliding tiles boards"
    print "\t\tof given size until killed"
    print "\tBEWARE: program will hang if no more unique boards for given"
    print "\t\tsize are possible"
    sys.exit(1)

def is_solvable(dir):
    size = len(dir)
    revOrd = 0
    for i in range(size - 1):
        for j in range(i + 1, size): 
            if dir[i] > dir[j] and dir[j] != 0:
                revOrd+=1;
    if revOrd % 2 == 0:
        #print revOrd
        return True

def gen_board(ignore, size):
    board = range(size)
    r = random.Random()
    r.seed(time.time())

    while board in ignore or not is_solvable(board):
        #make a new one
        for i in range(size):
            j = r.randint(i, size-1)
            board[i], board[j] = board[j], board[i]
            
    return board

if __name__ == '__main__':
    if "--help" in sys.argv:
        usage()
    else:
        if len(sys.argv) > 1:
            size = int(sys.argv[1])
        else:
            usage()

        ignore = [range(size)]
        
        i=0
        while True:
            try:
                i+=1
                board = gen_board(ignore, size)
                print i, " ".join([str(x) for x in board])
                ignore += [board]
            except IOError:
                sys.exit(0)
