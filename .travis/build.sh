#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

# Build and install libpoly
pushd .
git clone https://github.com/SRI-CSL/libpoly.git
mkdir -p libpoly/build
cd libpoly/build
cmake ..
make
sudo make install
popd

# Build and install CUDD
pushd .
git clone https://github.com/ivmai/cudd.git
cd cudd
git checkout tags/cudd-3.0.0
autoreconf -fi
./configure --enable-shared
make
sudo make install
popd

# Build yices
autoconf
CFLAGS='-Werror' ./configure $CONFIGURE_FLAGS

# This is needed for yices2 to find libpoly.so.0. /usr/local/lib not searched by default?
export LD_LIBRARY_PATH=/usr/local/lib/:${LD_LIBRARY_PATH}

# Build Yices2
make MODE=$BUILD_TYPE

# Add valgrind if asked
if [[ $ENABLE_VALGRIND == ON ]]; then
  COMMAND_PREFIX="valgrind -q"
fi

# Run checking
make MODE=$BUILD_TYPE check

RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Building and checking yices2 failed!"
    exit 1
fi
