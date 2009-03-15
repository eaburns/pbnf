#!/usr/bin/python
# make_tiles.py
#
# Takes a series of single-line tiles boards in the format produced by gen.c
# and converts them to our format.
#
# sna4 December 2008

import sys, shutil, fileinput, math, os, subprocess, hashlib

def usage():
    print "usage: make_tiles.py [-t] [MAX] [skip]"
    print "-t test whether A* can solve boards and keep only solvable ones"
    print "provide tile boards on stdin in the following format:"
    print "\t[num] [tile1, tile2...]"
    print "assumes board is square or one off from being square"
    print "ignores the first line, since gen.c gives a pre-solved board first"
    sys.exit(1)

width, height, n = None, None, None
dir, model, executable = "boards", "random", "/home/rai/eaburns/src/ocaml/rdb/rdb_get_path.unix_unknown"
search_exec = "/home/rai/eaburns/src/cpp-search/src/tiles_search.x86_64.bin"
#search_exec = "../src/tiles_search.x86_64"
ulimit = "ulimit -v 15000000"

#search_exec = "../src/tiles_search.i386"

def switch_rep(tiles):
    other = [0]*len(tiles)
    tiles = [int(tile) for tile in tiles]
    for tile in tiles:
        other[tile] = str(tiles.index(tile))
    return other

def make_board(in_data, test):
    global width, height, n
    m = hashlib.md5()
    m.update(in_data[in_data.index(" ")+1:-1])
    in_data = in_data.split()
    num = in_data[0]
    tiles = switch_rep(in_data[1:])
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
    path = num+"_"+width+"x"+height+".tile"
    #path=os.popen(executable+" "+dir+" model="+model+" rows="+height+" cols="+width+" num="+num, "r").readline().split()[1]
    outfile = open(path, "w")
    outfile.write(width+" "+height+"\n")
    outfile.write("starting positions for each tile:\n")
    outfile.write(tiles+"\n")
    outfile.write("goal positions:\n")
    outfile.write("\n".join([str(x) for x in range(n)]))
    outfile.close()
    
    new_path = m.hexdigest()+".tile"

    if test:
        #run A* to see if the board is solvable
        results = subprocess.Popen(ulimit+"; "+search_exec+" astar <"+path, shell=True, stdout=subprocess.PIPE, executable="/bin/bash").stdout.readlines()
        is_output = len(results) > 0
        shutil.move(path, new_path)
        path = new_path
        if is_output:
            finished = "cost" in results[0]
            solved = not "No Solution" in results[0]
        else:
            finished = False
        #if not, delete the board and return false
        if not finished:
            if is_output and not solved:
                print results
                #print ", ".join(in_data)
                print "no solution!"
                #sys.exit(0)
                #os.remove(path)
            else:
                print "failed to finish"
            os.remove(path)
            #sys.exit(1)
            return False
        else:
            cost = results[0].split()[1]
            gen = results[-1].split()[1]
            print "finished with cost", cost, "generated", gen
            #os.remove(path)
    
    return True

if __name__ == '__main__':
    if "--help" in sys.argv:
        usage()
    else:
        if "-t" in sys.argv:
            test = True
            sys.argv.remove("-t")
        else:
            test = False
        if len(sys.argv) > 1:
            max = int(sys.argv[1])
        else:
            max = sys.maxint-2
        if len(sys.argv) > 2:
            skip = int(sys.argv[2])
        else:
            skip = 0
        
        sys.argv = []
        made = 0
        for line in fileinput.input():
            if skip > 0:
                skip = skip-1
                continue
            made += 1
            if made > max:
                sys.exit(0)
            if not make_board(line, test):
                made -= 1
