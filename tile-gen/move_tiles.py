#!/usr/bin/python
# move_tiles.py
#
# Moves all .tile files in the current directory to a file named based on
# their MD5 values.
#
# sna4 March 2009

import sys, shutil, os, hashlib

def usage():
    print "This program moves all .tile files in the current directory to"
    print "\ta file named based on their MD5 values."
    print "usage: move_tiles.py"

if __name__ == '__main__':
    if "--help" in sys.argv:
        usage()
    else:
        for file in os.listdir("."):
            if file.endswith(".tile"):
                m = hashlib.md5()
                m.update(open(file).read())
                shutil.move(file, m.hexdigest()+".tile")
