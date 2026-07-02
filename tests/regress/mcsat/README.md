# MCSAT Regression Tests

Tests in this directory are run only against MCSAT (`yices_smt2 --mcsat`).
Tests that should pass under both solvers belong in `tests/regress/both/`.

## Disabling convention

Files with a `.smt2.disabled` suffix are not picked up by the regression
harness. We use this convention (rather than deleting the test) when MCSAT
temporarily cannot answer a query that it was previously able to handle, so
that the test case is preserved and is straightforward to re-enable once the
underlying capability is restored.

Every disabled test should be tracked in the table below with:

- a one-line description of the input shape,
- the reason MCSAT no longer accepts the input,
- the work item that, when completed, should re-enable the test.

If you disable a test, add a row. If you re-enable a test, remove its row.

## Currently disabled tests

The four tests below were disabled in commit `48f2e4a2f9dd` ("Temporarily
disable MCSAT finite-function equality regressions") while MCSAT function
extensionality was protected by a preprocessing guard. That guard has since
been removed. These tests should stay disabled until they are re-run and
re-enabled individually, since their remaining behavior may involve crashes,
incremental-mode handling, large finite domains, or performance rather than a
preprocessing rejection.

| File | Input shape | Re-enable when |
|---|---|---|
| `iss552.smt2.disabled` | `(Array (Array Bool Bool) Bool)`; function-typed (`Array Bool Bool`) domain on the outer array; equality between two such terms via nested `store` chains | The file runs cleanly under MCSAT and matches its `.gold` output |
| `arrays/bool-array.smt2.disabled` | `(Array Bool Bool)`; directly a `Bool -> Bool` array; asserts disequality between two selected values while constraining the concrete Boolean indices equal | The file runs cleanly under MCSAT and matches its `.gold` output |
| `arrays/linux-4.0-rc1---kernel--locking--locktorture.ko.cil_smt-query.1.smt2.disabled` | LDV-generated incremental `QF_AUFBVNIA` query over many `(Array (_ BitVec 64) (_ BitVec 64))` arrays plus equalities between them | The incremental run is stable and fast enough for the regression suite |
| `32_1_cilled_ok_nondet_linux-3.4-32_1-drivers--input--keyboard--gpio_keys_polled.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out_smt-query.0.smt2.disabled` | LDV-generated incremental `QF_AUFBVNIA` query over many `(Array (_ BitVec 64) ...)` arrays plus equalities between them | The incremental run is stable and fast enough for the regression suite |

The remaining `.smt2.disabled` files in this directory and its subdirectories
predate PR #590 and were disabled for other reasons. If you re-enable any of
them, please attach a tracking note here with the underlying cause and the fix
that addressed it.
