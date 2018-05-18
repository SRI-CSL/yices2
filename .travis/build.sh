#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

# Build and install libpoly
pushd .
git clone https://github.com/SRI-CSL/libpoly.git
cd libpoly/build
cmake ..
make
sudo make install
popd

#Build Yices
autoconf
./configure --enable-mcsat

# This is needed for yices2 to find libpoly.so.0. /usr/local/lib not searched by default?
export LD_LIBRARY_PATH=/usr/local/lib/:${LD_LIBRARY_PATH}

make MODE=gcov 
make MODE=gcov check

RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Building and checking yices2 failed!"
    exit 1
fi
