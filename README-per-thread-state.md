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

## Rules of Thumb and Caveats

* The main thread should call `yices_global_init` before spawning any worker threads.
* Once all worker threads have finished, the main thread can call `yices_global_exit` and exit.
* Each worker thread should call `yices_per_thread_init` prior to calling any API routines, and on exiting should call `yices_per_thread_exit`.
* Each thread has its own state (term table, type table etc), which is reclaimed upon calling  `yices_per_thread_exit`.
* There should be no real need to call the Yices Garbage Collector.
* The main thread should not call any other yices API routines (since it doesn't have any term or type tables etc).


## Use

Any application that uses the *per-thread-state* configuration must also be compiled
with the 
```
CFLAGS=-DPER_THREAD_STATE
```
incantation, in order to get the correct definitions from `yices.h`.
