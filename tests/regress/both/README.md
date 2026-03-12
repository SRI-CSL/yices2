# Shared Regression Tests (`regress/both`)

Tests in this directory are expected to pass in both solver modes:

- `--mcsat`
- `--dpllt`

The regression harness runs each SMT2 test in this directory twice, once per
mode. Do not put `--mcsat` or `--dpllt` in `.options` files here; the harness
injects these flags automatically.

Keep MCSAT-only tests (for example, `check-sat-assuming-model` and
`get-unsat-model-interpolant`) in `tests/regress/mcsat`.

Keep core-shape-sensitive tests where outputs differ across solvers outside this
directory.
