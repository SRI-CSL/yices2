## Yices2 Frequently Asked Questions


## FAQ

**Question:** I tried a simple example and it didn't work.

**Answer:** You are probably using the wrong tool.
Yices comes with four tools, and each expects its input
to be written in a specific language.

* `yices`  expects the input to be written in the `yices` language

* `yices-smt2` expects the input to be in SMT-LIB 2.5 language.

* `yices-smt` expects the input to be in the older SMT-LIB 1.2 language

* `yices-sat` is a boolean satisfiablility that expects the DIMACS CNF format.

For more details see the [manual](http://yices.csl.sri.com/papers/manual.pdf) chapter 1 section 1.2, chapter 4 and
chapter 5.



**Question:** I tried yices and got a `Illegal instruction` error.

**Answer:** This is most likely a hardware incompatibility problem, caused by the
way we distribute yices with a statically linked GMP build.

If you try
```
grep avx2 /proc/cpuinfo
```
and see nothing, then your CPU does not support AVX2 instructions and that would cause
the illegal instruction error. The fix is to build yices from source yourself.
