#!/bin/bash
#
# Adds the contents of FILE_HEADER to the top of each .cpp, .c and .h
# file.
#
# This should be called whenever we create a non-version-controlled
# release (with 'hg archive').
#

for FILE in `find . -name \*.cpp; find . -name \*.h; find . -name \*.cpp`
do
    cat FILE_HEADER ${FILE} > ${FILE}~
    mv ${FILE}~ ${FILE}
done
