#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

#build and install libpoly (Dejan when will this be a ubuntu package?)
git clone https://github.com/SRI-CSL/libpoly.git
cd libpoly/build
cmake ..
make
sudo make install

#magic for solving mystery
sudo updatedb
locate libpoly.so.0
sudo ldconfig -n /usr/local/lib/
ls -la  /usr/local/lib/

#now build yices
cd ../..
autoconf
./configure --enable-mcsat

make MODE=gcov 

#these do not solve the mystery
which yices-smt
ldd /usr/local/bin/yices-smt

#FIXME: this is needed for yices2 to find libpoly.so.0. Seems like there
#should be a better way, no? Dejan?
export LD_LIBRARY_PATH=/usr/local/lib/:${LD_LIBRARY_PATH}

yices-smt --version


make MODE=gcov check


RETURN="$?"


if [ "${RETURN}" != "0" ]; then
    echo "Building and checking yices2 failed!"
    exit 1
fi
