## Yices2 Frequently Asked Questions


## FAQ

**Question:** I tried a simple example and it didn't work

**Answer:** You are probably using the wrong tool.
Yices comes with four tools, each expects its input
to be written in a specific language.

* `yices`  expects the input to be written in the `yices` language

* `yices-smt2` expects the input to be in SMT-LIB 2.5 language.

* `yices-smt` expects the input to be in the older SMT-LIB 1.2 language

* `yices-sat` is a boolean satisfiablility that expects the DIMACS CNF format.

For more details see the [manual](http://yices.csl.sri.com/papers/manual.pdf) chapter 1.2, 4 and 5.