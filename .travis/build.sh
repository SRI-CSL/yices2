#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

#build and install libpoly (dejan when will this be a ubuntu package?)
git clone https://github.com/SRI-CSL/libpoly.git
cd libpoly/build
cmake ..
make
sudo make install


autoconf
./configure --enable-mcsat
make check
RETURN="$?"


if [ "${RETURN}" != "0" ]; then
    echo "Building and checking yices2 failed!"
    exit 1
fi
