# Shared Regression Tests (`regress/both`)

Tests in this directory are expected to pass in both solver modes:

- `--mcsat`
- the default SMT2 solver path (currently DPLL(T))

The regression harness runs each SMT2 test in this directory twice, once per
mode. Do not put solver-selection flags such as `--mcsat` or `--dpllt` in
`.options` files here; the harness controls the solver mode automatically.

Keep MCSAT-only tests (for example, `check-sat-assuming-model` and
`get-unsat-model-interpolant`) in `tests/regress/mcsat`.

Keep core-shape-sensitive tests where outputs differ across solvers outside this
directory.
