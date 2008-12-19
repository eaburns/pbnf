#!/usr/bin/python
# make_tiles.py
#
# Takes a series of single-line tiles boards in the format produced by gen.c
# and converts them to our format.
#
# sna4 December 2008

import sys, fileinput, math, os

def usage():
    print "usage: make_tiles.py [MAX]"
    print "provide tile boards on stdin in the following format:"
    print "\t[num] [tile1, tile2...]"
    print "assumes board is square or one off from being square"
    print "ignores the first line, since gen.c gives a pre-solved board first"
    sys.exit(1)

width, height, n = None, None, None
dir, model, executable = "boards", "random", "/home/rai/eaburns/src/ocaml/rdb/rdb_get_path.unix_unknown"

def switch_representation(tiles):
    other = [0]*len(tiles)
    tiles = [int(tile) for tile in tiles]
    for tile in tiles:
        other[tile] = str(tiles.index(tile))
    return other

def make_board(in_data):
    global width, height, n
    in_data = in_data.split()
    num = in_data[0]
    tiles = in_data[1:]
    if n == None:
        n = len(tiles)
        height = math.sqrt(n)
        if height != int(height):
            height = int(height)
            width = height+1
        else:
            height = int(height)
            width = height
        width, height = str(width), str(height)
    tiles = "\n".join(tiles)
    path = os.popen(executable+" "+dir+" model="+model+" rows="+height+" cols="+width+" num="+num, "r").readline()
    print path
#    outfile = open(path, "w")
#    outfile.write(width+" "+height+"\n")
#    outfile.write("starting positions for each tile:\n")
#    outfile.write(tiles+"\n")
#    outfile.write("goal positions:\n")
#    outfile.write("\n".join([str(x) for x in range(n)]))
#    outfile.close()

if __name__ == '__main__':
    if "--help" in sys.argv:
        usage()
    else:
        if len(sys.argv) > 1:
            max = int(sys.argv[1])
            sys.argv = sys.argv[:0]
        else:
            max = sys.maxint/2
        made = 0
        for line in fileinput.input():
            made += 1
            if made > max:
                sys.exit(0)
            make_board(line)
