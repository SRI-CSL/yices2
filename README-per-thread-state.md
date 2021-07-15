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

yices2/tests/api/check_formula_examples_mt.c


