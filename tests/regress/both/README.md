# Shared Regression Tests (`regress/both`)

Tests in this directory are expected to pass in both solver modes:

- `--mcsat`
- `--dpllt`

Each SMT2 test here carries two option sets, tagged `mcsat` and `dpllt`:
`file.smt2.mcsat.options` and `file.smt2.dpllt.options`, each naming its own
solver flag. The harness runs one test per option set, so both modes are used
explicitly rather than through the default path, which may be heuristically
routed to either solver depending on the logic. A test here has no untagged
`file.smt2.options`: that would add a third run, on the default path. Anything
the two modes share, such as `--incremental`, goes in both files.

Most tests should use one shared `.gold` file. If a temporary solver limitation
intentionally gives different output in the two modes, add solver-specific
overrides with `.mcsat.gold` and/or `.dpllt.gold`; otherwise the shared `.gold`
is used for both runs.

`check.sh -x dpllt` (or `REGRESS_DISABLE_TAGS=dpllt`) skips a tag, which is how
an MCSAT-only run covers these tests in one mode.

Keep MCSAT-only tests (for example, `check-sat-assuming-model` and
`get-unsat-model-interpolant`) in `tests/regress/mcsat`.

Keep core-shape-sensitive tests where outputs differ across solvers outside this
directory.
