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
disable MCSAT finite-function equality regressions") because they reach
equality/disequality atoms whose type is rejected by the new MCSAT
preprocessor guard `term_needs_function_diseq_guard` introduced in commit
`5110215f` (PR #590). The guard rejects any equality/disequality whose type
contains a finite-domain function sort, a unit-range function sort, or such
a function sort nested inside a tuple/instance/function-codomain. The guard
is a temporary workaround for the long-standing wrong-SAT bug on finite
function types in MCSAT (see issue #414, PR #590, and the
`plan-finite-function-extensionality-option-A.md` /
`plan-finite-function-extensionality-option-B.md` design notes at the
repository root).

| File | Rejected type / shape | Guard branch | Re-enable when |
|---|---|---|---|
| `iss552.smt2.disabled` | `(Array (Array Bool Bool) Bool)` — function-typed (`Array Bool Bool`) domain on the outer array; equality between two such terms via nested `store` chains | finite-domain function (outer) with function-typed domain (inner) | MCSAT supports finite-function extensionality (Plan A/B Commit 1) |
| `arrays/bool-array.smt2.disabled` | `(Array Bool Bool)` — directly a `Bool → Bool` array; asserts `(not (= (select a (= a b)) (select a (not (= a b)))))` and `(= (select a true) (select a false))` | finite-domain function (`Bool` domain) | MCSAT supports finite-function extensionality (Plan A/B Commit 1) |
| `arrays/linux-4.0-rc1---kernel--locking--locktorture.ko.cil_smt-query.1.smt2.disabled` | LDV-generated query in `QF_AUFBVNIA` over many `(Array (_ BitVec 64) (_ BitVec 64))` arrays plus equalities between them | finite-domain function (`(BV 64)` domain — large but finite) | MCSAT supports finite-function extensionality (Plan A/B Commit 1) and the enumeration cap accepts very large finite domains, OR Plan B's lazy-sound infinite-domain mechanism is extended to large-finite domains |
| `32_1_cilled_ok_nondet_linux-3.4-32_1-drivers--input--keyboard--gpio_keys_polled.ko-ldv_main0_sequence_infinite_withcheck_stateful.cil.out_smt-query.0.smt2.disabled` | LDV-generated query in `QF_AUFBVNIA` over many `(Array (_ BitVec 64) ...)` arrays plus equalities between them | finite-domain function (`(BV 64)` domain — large but finite) | Same as above |

The remaining `.smt2.disabled` files in this directory and its subdirectories
predate PR #590 and were disabled for reasons unrelated to the
finite-function guard. If you re-enable any of them, please attach a tracking
note here with the underlying cause and the fix that addressed it.
