#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

#build and install libpoly (Dejan when will this be a ubuntu package?)
git clone https://github.com/SRI-CSL/libpoly.git
cd libpoly/build
cmake ..
make
sudo make install

#now build yices
cd ../..
autoconf
./configure --enable-mcsat

make MODE=gcov 

#this is needed for yices2 to find libpoly.so.0. /usr/local/lib not searched by default?
export LD_LIBRARY_PATH=/usr/local/lib/:${LD_LIBRARY_PATH}

make MODE=gcov check


RETURN="$?"


if [ "${RETURN}" != "0" ]; then
    echo "Building and checking yices2 failed!"
    exit 1
fi
