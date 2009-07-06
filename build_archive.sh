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

echo "Making the archive"
hg archive ${DIR}

echo "Adding file header comments"
cd ${DIR}
for FILE in `find . -name \*.cpp; find . -name \*.h; find . -name \*.cpp`
do
    cat FILE_HEADER ${FILE} > ${FILE}~
    mv ${FILE}~ ${FILE}
done

echo "Removing the FILE_HEADER template from the archive"
rm FILE_HEADER

echo "Remove this script from the archive"
rm build_archive.sh

echo "tar/bz2 the archive"
cd ..
tar -cjf ${DIR}.tar.bz2 ${DIR}

echo "Removing the archive directory."
rm -fr ${DIR}
