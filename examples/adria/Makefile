YICES_SMT2=../../bin/yices_smt2
YICES_MAIN=../../bin/yices_main
VERBOSITY=--verbosity=0

all: 1y 1s 1fy 1fs

1s:
	${YICES_SMT2} ${VERBOSITY} example_1_implication.smt2

1y:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_1_implication.ys

1fs:
	${YICES_SMT2} ${VERBOSITY} example_1_implication_forall_turned_into_exist.smt2

1fy:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_1_implication_forall_turned_into_exist.ys

2s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected.smt2

2y:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_2constraints_expected.ys

22s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected2.smt2

22y:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_2constraints_expected2.ys

23s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected3.smt2

23y:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_2constraints_expected3.ys

24s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected4.smt2

24y:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_2constraints_expected4.ys

alurs:
	${YICES_SMT2} ${VERBOSITY} example_ALU_add_sub_rewritten.smt2

alury:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_ALU_add_sub_rewritten.ys

ds:
	${YICES_SMT2} ${VERBOSITY} example_distr.efyices.smt2

dy:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_distr.efyices

alus:
	${YICES_SMT2} ${VERBOSITY} example_find_ALU_add_conditions.smt2

aluy:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_find_ALU_add_conditions.ys
