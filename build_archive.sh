#!/bin/bash
#
# This script creates a non-version-controlled release.
#

# Use a directory based on the current date
DIR=pbnf-`date +%d-%m-%Y`
test -d $DIR && {
    echo "Directory ${DIR} already exists"
    exit 1
}

# Make the archive.
hg archive ${DIR}

# Add file header comments.
cd ${DIR}
for FILE in `find . -name \*.cpp; find . -name \*.h; find . -name \*.cpp`
do
    cat FILE_HEADER ${FILE} > ${FILE}~
    mv ${FILE}~ ${FILE}
done

# Remove the FILE_HEADER template.
rm FILE_HEADER

# Remove this script.
rm build_archive.sh
