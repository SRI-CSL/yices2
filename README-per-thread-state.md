# Yices 2  Per Thread  (Global) State Branch


## Building

Build via:

```
autoconf
./configure --enable-thread-safety
make
sudo make install
```

## Notes to Self

If all the state becomes thread local, then presumably we can get rid of all the locking?



### Commands