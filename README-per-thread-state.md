# Yices 2  Per Thread  (Global) State Branch


## Building

Build via:

```
autoconf
./configure --enable-thread-safety  CFLAGS=-DPER_THREAD_STATE
make
sudo make install
```

## Example

There is a simple, hopefully illustrative example [here](https://github.com/SRI-CSL/yices2/blob/per-thread-state/tests/api/check_formula_examples_mt.c)
that can be compiled by 
```
make check-api
```

## Use

Any application that uses the *per-thread-state* configuration must also be compiled
with the 
```
CFLAGS=-DPER_THREAD_STATE
```
incantation, in order to get the correct definitions from `yices.h`.
