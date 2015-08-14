VALGRIND=valgrind --leak-check=full --show-leak-kinds=all
#VALGRIND=
YICES_SMT2=${VALGRIND} ../../build/x86_64-apple-darwin13.4.0-debug/bin/yices_smt2
YICES_MAIN=${VALGRIND} ../../build/x86_64-apple-darwin13.4.0-debug/bin/yices_main  --mode=ef
CVC4=cvc4 --produce-models
VERBOSITY=--verbosity=0

BV_TESTS=test11.sat test11b.sat test11c.sat

LRA_TESTS=test1.unsat test2.sat test3.sat test4.sat test5.sat test6.sat test7.sat test8.unsat test9.sat test10.unsat

all: check_bv check_lra

check_bv: 
	for test in ${BV_TESTS} ; do \
	    echo "<$${test}>\n"; \
	    ${YICES_SMT2} ${VERBOSITY} $${test}.exists.smt2 ; \
	    echo "</$${test}>\n"; \
        done

check_lra:
	for test in ${LRA_TESTS} ; do \
	    echo "<$${test}>\n"; \
	    ${YICES_SMT2} ${VERBOSITY} $${test}.exists.smt2 ; \
	    echo "</$${test}>\n"; \
        done

