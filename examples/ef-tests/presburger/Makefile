#VALGRIND=valgrind --leak-check=full --show-leak-kinds=all
VALGRIND=
YICES_SMT2=${VALGRIND} ../../../build/x86_64-apple-darwin13.4.0-debug/bin/yices_smt2
YICES_MAIN=${VALGRIND} ../../../build/x86_64-apple-darwin13.4.0-debug/bin/yices_main  --mode=ef
CVC4=cvc4 --produce-models
Z3=/Users/iam/Repositories/z3/build/z3
VERBOSITY=--verbosity=0

EASY_4_YICES=00 01 02 03 04 05 06 11 12 14

HARD_4_YICES=07 08 09 10 13 15

TEST_4_YICES=16


all: easy

easy:
	for test in ${EASY_4_YICES} ; do \
	    echo "<example_$${test}>"; \
            ${YICES_SMT2} ${VERBOSITY} example_$${test}.smt2 ; \
	    echo "</example_$${test}>\n"; \
        done

hard:
	for test in ${HARD_4_YICES} ; do \
	    echo "<example_$${test}>"; \
            ${YICES_SMT2} ${VERBOSITY} example_$${test}.smt2 ; \
	    echo "</example_$${test}>\n"; \
        done


test:
	for test in ${TEST_4_YICES} ; do \
	    echo "<example_$${test}>"; \
            ${YICES_SMT2} ${VERBOSITY} example_$${test}.smt2 ; \
	    echo "</example_$${test}>\n"; \
        done

