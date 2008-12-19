#!/usr/bin/python
# make_tiles.py
#
# Takes a series of single-line tiles boards in the format produced by gen.c
# and converts them to our format.
#
# sna4 December 2008

import sys, fileinput, math

def usage():
    print "usage: make_tiles.py [MAX]"
    print "provide tile boards on stdin in the following format:"
    print "\t[num] [tile1, tile2...]"
    print "assumes board is square or one off from being square"
    sys.exit(1)

width, height, n = None, None, None

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
        width = math.sqrt(n)
        if width != int(width):
            width = int(width)
            height = width+1
        else:
            width = int(width)
            height = width
        width, height = str(width), str(height)
    tiles = "\n".join(switch_representation(tiles))
    outfile = open("board"+num+".tile", "w")
    outfile.write(width+" "+height+"\n")
    outfile.write("starting positions for each tile:\n")
    outfile.write(tiles+"\n")
    outfile.write("goal positions:\n")
    outfile.write("\n".join([str(x) for x in range(n)]))
    outfile.close()

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
