YICES_SMT2=../../bin/yices_smt2
YICES_MAIN=../../bin/yices_main  --mode=ef --logic=QF_BV
VERBOSITY=--verbosity=0

all: 1y 1s 1fy 1fs 23y 23s 24y 24s alury alurs dy ds aluy alus

1s:
	${YICES_SMT2} ${VERBOSITY} example_1_implication.smt2

1y:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_1_implication.ys

1fs:
	${YICES_SMT2} ${VERBOSITY} example_1_implication_forall_turned_into_exist.smt2

1fy:
	${YICES_MAIN} ${VERBOSITY} --mode=ef example_1_implication_forall_turned_into_exist.ys


#==== example_2constraints_expected.ys ====
#yices --mode=ef --logic=QF_BV example_2constraints_expected.ys
#Cputime limit exceeded (core dumped)
#598.875u 0.307s 10:00.12 99.8%    0+0k 0+0io 0pf+0w

2s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected.smt2

2y:
	${YICES_MAIN} ${VERBOSITY} example_2constraints_expected.ys

#==== example_2constraints_expected2.ys ====
#yices --mode=ef --logic=QF_BV example_2constraints_expected2.ys
#Cputime limit exceeded (core dumped)
#598.953u 0.311s 10:00.14 99.8%    0+0k 0+0io 0pf+0w

22s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected2.smt2

22y:
	${YICES_MAIN} ${VERBOSITY} example_2constraints_expected2.ys

#==== example_2constraints_expected3.ys ====
#yices --mode=ef --logic=QF_BV example_2constraints_expected3.ys
#unsat
#0.138u 0.000s 0:00.13 100.0%    0+0k 0+0io 0pf+0w

23s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected3.smt2

23y:
	${YICES_MAIN} ${VERBOSITY} example_2constraints_expected3.ys

#==== example_2constraints_expected4.ys ====
#yices --mode=ef --logic=QF_BV example_2constraints_expected4.ys
#unsat
#0.137u 0.000s 0:00.13 100.0%    0+0k 0+0io 0pf+0w

24s:
	${YICES_SMT2} ${VERBOSITY} example_2constraints_expected4.smt2

24y:
	${YICES_MAIN} ${VERBOSITY} example_2constraints_expected4.ys

#==== example_ALU_add_sub_rewritten.ys ====
#yices --mode=ef --logic=QF_BV example_ALU_add_sub_rewritten.ys
#sat
#0.202u 0.000s 0:00.20 100.0%    0+0k 0+0io 0pf+0w

alurs:
	${YICES_SMT2} ${VERBOSITY} example_ALU_add_sub_rewritten.smt2

alury:
	${YICES_MAIN} ${VERBOSITY} example_ALU_add_sub_rewritten.ys

#==== example_ALU_add_sub_rewritten.ys ====
#yices --mode=ef --logic=QF_BV example_ALU_add_sub_rewritten.ys
#sat
#0.202u 0.000s 0:00.20 100.0%    0+0k 0+0io 0pf+0w

ds:
	${YICES_SMT2} ${VERBOSITY} example_distr.efyices.smt2

dy:
	${YICES_MAIN} ${VERBOSITY} example_distr.efyices

#==== example_find_ALU_add_conditions.ys ====
#yices --mode=ef --logic=QF_BV example_find_ALU_add_conditions.ys
#sat
#0.204u 0.000s 0:00.20 100.0%    0+0k 0+0io 0pf+0w

alus:
	${YICES_SMT2} ${VERBOSITY} example_find_ALU_add_conditions.smt2

aluy:
	${YICES_MAIN} ${VERBOSITY} example_find_ALU_add_conditions.ys
