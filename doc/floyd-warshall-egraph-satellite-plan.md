# Plan: Floyd-Warshall IDL/RDL Solvers as E-graph Satellites

## Summary

Make the Floyd-Warshall integer-difference-logic and real-difference-logic solvers usable as arithmetic satellite solvers under the E-graph, in the same broad architecture used today for Simplex. The immediate target is a one-shot context architecture where the E-graph is the main theory-combination component and IFW/RFW are attached as Nelson-Oppen-style arithmetic sub-solvers.

This should let Yices use the specialized Floyd-Warshall decision procedures for formulas that combine difference logic with other E-graph-managed theories, especially QF_BV plus scheduling constraints that only interact through Boolean structure or through shared arithmetic equalities that remain expressible as difference constraints. Pure QF_IDL/QF_RDL behavior should remain unchanged.

## Current State

The Floyd-Warshall solvers are currently standalone theory solvers:

- `src/solvers/floyd_warshall/idl_floyd_warshall.h` explicitly says the IDL solver cannot be attached to the E-graph.
- `create_idl_solver` and `create_rdl_solver` in `src/context/context.c` assert that there is no E-graph and no other theory solver.
- Existing mixed-theory arithmetic contexts use Simplex because Simplex exposes both `th_egraph_interface_t` and `arith_egraph_interface_t`.
- The BV solver already has an E-graph attachment path, so the relevant target architecture is not "bit-blast everything before theory selection"; it is "attach BV and difference logic as theory solvers under a shared E-graph/SAT core".

The existing IFW/RFW solvers already have much of the core machinery needed for this:

- Term-to-variable creation through the arithmetic plugin path.
- Difference-atom creation for constraints of the form `x - y <= c`.
- Equality atoms represented as paired zero-bound difference constraints.
- Internal trail/backtracking support.
- Conflict/path explanation support for generated Floyd-Warshall constraints.
- Model construction from distance/potential assignments.

What they do not currently have is the E-graph-facing API surface that lets an equality engine assert shared equalities/disequalities, request explanations, reconcile models, and generate interface lemmas.

One important representation constraint drives the design: an IFW/RFW `thvar_t` is not a Floyd-Warshall graph vertex. It is a `dl_triple_t` of the form `target - source + constant`. An E-graph equality between two arbitrary triples may expand to a four-variable linear equation and may not be representable as difference logic. The first implementation must make this a checked invariant, not an assumption hidden in the E-graph interface.

## Goals

1. Add IFW/RFW E-graph satellite interfaces analogous to the Simplex interfaces.
2. Support one-shot E-graph contexts containing IDL or RDL constraints.
3. Support combinations such as:
   - E-graph + IFW
   - E-graph + RFW
   - E-graph + BV + IFW
   - E-graph + BV + RFW
4. Preserve the existing pure IFW/RFW standalone architectures.
5. Keep unsupported arithmetic outside difference logic on the existing Simplex paths.
6. Provide clear configuration and auto-selection behavior.
7. Add regression coverage for correctness, model construction, conflict explanations, and mixed BV + difference-logic use.

## Non-goals For The First Version

1. Full incremental push/pop support for mixed E-graph + IFW/RFW contexts.
2. Replacing Simplex as the default mixed-theory arithmetic solver in all cases.
3. Refactoring the whole context-architecture enum system into a fully compositional component system.

## Hard Constraints

1. IFW/RFW only support difference-logic atoms: after normalization, arithmetic atoms must have coefficients in `{ -1, 0, 1 }` with at most one positive and one negative variable.
2. E-graph equalities between attached IFW/RFW terms are admissible only if the difference of the two attached `dl_triple_t` values is itself representable as a single difference-logic triple.
3. E-graph disequalities between attached IFW/RFW terms are admissible only under the same representability condition, because disequality/interface lemmas need comparable difference atoms.
4. IDL path computations use signed 32-bit bounds, so overflow detection and fallback/error behavior are part of the solver selection contract. Overflow checks must also cover any interface atoms created during model reconciliation.

## Design Principle

Use Simplex as the integration model.

Simplex exposes:

- A solver-control interface for the context/SAT layer.
- An SMT-theory interface for arithmetic atoms.
- A theory/E-graph interface for equality combination.
- An arithmetic/E-graph interface for variable creation and model values.

The Floyd-Warshall solvers should grow the same E-graph-facing boundary, while preserving their specialized internal representation.

## Phase 0: Design Note And Invariants

Before changing code, write a design note that records the invariants the E-graph integration must preserve. This is not just an audit; it should decide the representation policy used by later phases.

Design decisions to record:

- `dl_triple_t` shape policy: V1 attaches only terms whose E-graph equalities/disequalities can be reduced to a representable difference triple using the existing triple-difference machinery. The first implementation should use existing helpers such as `diff_dl_vars`, `sum_dl_vars`, and `convert_poly_buffer_to_dl_triple` rather than adding a parallel normalizer. If two attached terms produce a non-DL difference, explicit IFW/RFW mode reports a clean unsupported-combination error and auto mode falls back to Simplex.
- Implementation note: many non-DL equalities, such as `a - b = c - d`, are rejected by the IDL/RDL internalizer before they reach the E-graph assertion queue. That is an acceptable V1 enforcement path. If future internalization changes allow such compound attached terms to reach the E-graph queue, the queue-side `diff_dl_vars` check must still reject them.
- No pre-projection helpers in V1. Do not introduce fresh graph vertices of the form `u := target - source + constant` to force arbitrary triples into vertex-shaped form; that needs a separate soundness argument and would change the Floyd-Warshall graph.
- Pure vertex and vertex-plus-constant triples are the expected first supported attached shapes. More general pairs may be accepted only when subtracting the two triples normalizes to a valid `dl_triple_t`.
- Equality translation is not "`thvar x` minus `thvar y` as if both were vertices"; it is "subtract the two `dl_triple_t` values, verify the result is a difference triple, then assert that normalized difference is zero".
- Atom creation during model reconciliation is a prerequisite for disequality/interface-lemma support. The design note must state whether IFW/RFW can safely create and register fresh difference atoms during search, or whether all candidate interface atoms must be pre-created before search.
- IDL overflow behavior must reuse the existing signed-32-bit checks and define explicit-mode error versus auto-mode fallback.
- Atom deletion limitations must be carried into the context architecture restrictions.

Deliverable:

- A committed Markdown design note, or a dedicated section in this plan, that resolves the `dl_triple_t` attachment policy, atom-creation policy, overflow policy, and one-shot/incremental scope before implementation starts.

## Phase 1: Attach Arithmetic Variables To E-graph Terms

The E-graph must be able to map between theory variables and public E-graph terms.

Add per-variable E-graph metadata to the IDL/RDL variable tables:

- `eterm_t eterm` or equivalent for each arithmetic variable.
- A sentinel value for "not attached".
- Accessors analogous to Simplex's `attach_eterm` and `eterm_of_var`.

Implement:

- `idl_attach_eterm`
- `idl_eterm_of_var`
- `rdl_attach_eterm`
- `rdl_eterm_of_var`

Requirements:

- Attaching the same variable twice must either be idempotent or assert consistent input.
- Attaching a `thvar_t` with an unsupported triple shape must fail cleanly in explicit IFW/RFW mode and cause Simplex fallback in auto mode.
- The attached metadata must store enough information to compare model values of `target - source + constant`, not just raw graph vertices.
- Unattached variables must be handled safely.
- Pure IFW/RFW mode must not pay meaningful overhead beyond the extra field.

## Phase 2: Add An E-graph Assertion Path

The E-graph will send equalities, disequalities, and distinct constraints between arithmetic variables.

Add a small E-graph assertion queue to IFW/RFW, modeled after Simplex's pending E-graph assertion handling. This queue should record:

- The kind of assertion: equality, disequality, or distinct.
- The involved theory variables.
- The E-graph explanation object or literal needed to explain why the assertion exists.

Initial equality handling:

- Given attached theory variables `x` and `y`, compute the normalized triple for `x - y`.
- Use `diff_dl_vars` or the equivalent existing normalization path for this computation.
- If `x - y` is not representable as a difference triple, reject the IFW/RFW E-graph path for this problem.
- If `x - y` normalizes to `u - v + c`, then `x = y` becomes:
  - `u - v <= -c`
  - `v - u <= c`
- These constraints must be tagged as E-graph-origin constraints so explanations can refer back to the E-graph source.

Initial disequality/distinct handling:

- Do not eagerly encode `x != y` as a disjunction.
- Track the disequality for model reconciliation.
- Generate an interface lemma only when the current difference-logic model assigns equal values to variables that the E-graph requires to be disequal.

The E-graph assertion queue should reuse the existing Simplex `eassertion_*` queue machinery if practical. If the queue is currently too Simplex-local, factor it into a shared utility first rather than letting IFW/RFW grow a near-duplicate queue.

This keeps the first version close to Simplex's lazy equality-combination strategy and avoids forcing the Floyd-Warshall solver to own SAT-level disjunction generation prematurely.

## Phase 3: Explanation Support

E-graph combination is only sound if conflicts and propagated facts can be explained in terms of input literals and E-graph assertions.

Extend the existing IFW/RFW explanation machinery so it can explain paths that include E-graph-origin equality edges.

For every internal edge, distinguish:

- A user arithmetic atom edge.
- A generated equality edge from an asserted E-graph equality.
- A derived or auxiliary edge introduced by the solver.

The design note should decide how E-graph-origin edges are represented. If the existing literal-tag channel in the edge stack is sufficient, use it with a sentinel or associated explanation-reference table. Otherwise add an explicit per-edge explanation reference. Do not leave this implicit, because explanation expansion depends on recovering the E-graph reason for each generated edge.

Implement E-graph-facing explanation expansion:

- Given a theory explanation request, expand Floyd-Warshall path edges into SAT literals and E-graph explanations.
- Preserve current explanations for pure arithmetic atoms.
- Include both directions of an E-graph equality when equality was encoded as two normalized difference constraints and both directions participate in a conflict.

Tests should include at least:

- Unsat from arithmetic constraints alone.
- Unsat from E-graph equality plus arithmetic constraints.
- Unsat from BV/Boolean structure selecting an E-graph equality that conflicts with IDL/RDL bounds.

## Phase 4: Model Reconciliation And Interface Lemmas

The E-graph and arithmetic solver may build models that disagree on shared equalities. IFW/RFW must participate in model reconciliation.

Implement the E-graph model hooks analogous to Simplex:

- `var_is_constant`
- `check_disequality`
- `reconcile_model`
- `prep_model`
- `var_equal_in_model`
- `gen_interface_lemma`
- `release_model`
- `build_model_partition`
- `release_model_partition`
- `select_eq_polarity`

Expected behavior:

- Use Floyd-Warshall potentials/distances as arithmetic model values, evaluating attached terms as `target - source + constant`.
- `prep_model` should invoke the existing model construction path, such as `idl_build_model` or `rdl_build_model`; `release_model` should tear that representation down rather than introducing a second model store.
- Two variables are equal in the arithmetic model if their exported values are equal.
- If the E-graph says two arithmetic variables must be equal but IFW/RFW cannot satisfy that equality with the current graph, produce a conflict explanation.
- If the E-graph says two variables are disequal but the arithmetic model gives them equal values, generate a lazy interface lemma that forces the SAT search to separate the cases.

The exact lemma shape should follow the Simplex convention where possible, so the E-graph/SAT core does not need solver-specific logic.

Important prerequisite:

- Simplex interface lemmas rely on SAT-visible literals for order/equality facts. IFW/RFW must either support safe creation and registration of fresh difference atoms during reconciliation, via the existing `idl_make_atom`/`rdl_make_atom` style path or an equivalent, or pre-create all interface atoms needed for attached terms before search starts. Milestone 3 is blocked until this is resolved.

## Phase 5: Expose IFW/RFW E-graph Interfaces

Add interface constructors in the Floyd-Warshall modules.

IDL:

- `idl_egraph_interface`
- `idl_arith_egraph_interface`

RDL:

- `rdl_egraph_interface`
- `rdl_arith_egraph_interface`

Headers:

- Add declarations to the corresponding Floyd-Warshall headers.
- Replace the unconditional comments that currently say the solver cannot attach to the E-graph.
- Document the actual limitation instead, for example "E-graph attachment is supported only for one-shot contexts and only for attached triples whose equalities/disequalities remain difference-logic representable."

The interface tables should be static and structured like the Simplex tables, so context construction can attach any arithmetic solver through the same pattern.

## Phase 6: Context Construction

Relax the current standalone-only construction path.

Current pure mode should remain:

- No E-graph.
- IFW/RFW attached directly to the SMT core.
- Existing pure QF_IDL/QF_RDL behavior.

New E-graph satellite mode:

- If `ctx->egraph != NULL`, create IFW/RFW as the arithmetic solver.
- Attach it to the E-graph with its SMT, control, theory/E-graph, and arithmetic/E-graph interfaces.
- Split the current bundled standalone assertions in `create_idl_solver` and `create_rdl_solver`. Pure mode should still require no E-graph and no peer theory solver. E-graph satellite mode should require no existing arithmetic solver but must allow a present E-graph and, in the later BV milestone, a BV solver.
- Keep assertions rejecting unsupported combinations outside the intended first-version scope.

The implementation should mirror the Simplex path in `context.c` rather than inventing a separate attachment protocol.

## Phase 7: Architecture And Configuration

Add explicit architectures for the first supported combinations.

Recommended first set:

- `CTX_ARCH_EGIFW`
- `CTX_ARCH_EGRFW`
- `CTX_ARCH_EGBVIFW`
- `CTX_ARCH_EGBVRFW`

Potential later set:

- E-graph + arrays/functions + IFW/RFW, if tests show the equality-combination hooks are sufficient.

Update:

- `context_types.h`
- Architecture-to-theory masks in `context.c`
- Architecture component tables in `context.c`
- Architecture MCSAT-support tables in `context.c`
- Architecture creation switches in `create_solvers` and related solver-construction paths.
- Architecture selection for SMT logics.
- Config decoding for `arith-solver=ifw` and `arith-solver=rfw`.
- Public/user documentation for accepted solver combinations.

Configuration policy:

- In pure QF_IDL/QF_RDL, preserve current defaults.
- In mixed E-graph logics, allow explicit `arith-solver=ifw` or `arith-solver=rfw` when all arithmetic atoms are difference-logic atoms.
- Keep architecture selection enum-based for this work. A component-based architecture refactor is a separate project after the IFW/RFW satellite path is implemented and benchmarked.
- Auto-selection can come after explicit selection works reliably.

## Phase 8: Eligibility And Fallback

The architecture selector must avoid choosing IFW/RFW when the formula is outside difference logic.

Extend the existing auto-selection checks in `create_auto_idl_solver` and `create_auto_rdl_solver` rather than introducing an independent eligibility pass. Those functions already contain the pure-solver density, overflow, and eligibility logic; the new work is to make that logic aware of E-graph attachment constraints.

Eligibility checks must cover:

- Integer difference constraints only for IFW.
- Real difference constraints only for RFW.
- No non-difference arithmetic atoms.
- No mixed integer/real arithmetic in a single Floyd-Warshall solver.
- No bounds outside the safe representation for IDL.
- No attached E-graph arithmetic terms whose equality or disequality with another attached term can produce a non-DL triple.
- No need for atom deletion or incremental behavior outside what the selected IFW/RFW mode supports.

Fallback behavior:

- If the user explicitly requests IFW/RFW and the formula is unsupported, report a clear unsupported-operation or bad-config error.
- If auto-selection considers IFW/RFW but finds an unsupported atom, fall back to Simplex.
- If IDL bound overflow is detected, fall back to Simplex in auto mode or report a clear error in explicit mode. Treat this as the tentative default unless Phase 10 benchmarking shows a better user-facing policy.

## Phase 9: Testing

Add tests in layers.

Pure-regression parity:

- Existing QF_IDL/QF_RDL tests should keep passing.
- Add a direct check that pure IFW/RFW construction still uses the standalone path.

E-graph + IDL:

- `x = y`, `x - y <= -1` is UNSAT.
- `x != y`, satisfiable difference constraints, model assigns distinct values when required.
- Shared equality generated by uninterpreted structure conflicts with IDL bounds.
- Compound attached triples that cannot be reduced to a difference triple are rejected in explicit IFW mode and fall back to Simplex in auto mode.

E-graph + RDL:

- Same shape as IDL with rational constants.
- Include strict-looking cases if the RDL frontend encodes them through non-strict bounds.

BV + IDL/RDL:

- BV constraints select a Boolean branch that activates IDL/RDL constraints.
- Difference logic and BV do not share arithmetic variables directly but are combined by SAT structure.
- A satisfiable case validates both BV and arithmetic model values.
- An unsatisfiable case validates explanations across Boolean selection and IDL/RDL conflict.

Disequality/interface lemmas:

- E-graph requires disequality.
- IFW/RFW model initially gives equal values.
- Solver generates a lemma and eventually finds a model or conflict.

Cross-theory explanation tests:

- E-graph equality used in an IDL conflict: assert an E-graph-visible equality `x = y`, assert `x - y <= -1`, and check that the explanation/core contains both the E-graph equality reason and the IDL bound reason.
- Difference-logic bound forcing an E-graph split: assert a guarded bound such as `x - y <= -1` while the E-graph model initially puts `x` and `y` in the same equality class, then verify that an interface lemma separates the class or produces a conflict with a complete explanation.
- BV-selected equality conflict: a BV condition selects an E-graph equality, another Boolean branch selects an IDL/RDL bound inconsistent with that equality, and UNSAT must explain through both selected literals.

Negative/config tests:

- Explicit IFW requested on non-difference arithmetic.
- Explicit IFW requested on real arithmetic.
- Explicit RFW requested on integer-only IDL, if that is not intended to coerce.
- Mixed integer and real arithmetic.
- Incremental mode if the first version is one-shot only.

Overflow tests:

- IDL constraints near 32-bit limits.
- Auto mode fallback or explicit-mode error.

Regression harness:

- Add SMT2 regressions for QF_UFIDL, QF_UFRDL, QF_BV+IDL-like Boolean combinations, and QF_BV+RDL-like Boolean combinations if the frontend logic names permit them.
- Add API tests for explicit architecture/config selection.

## Phase 10: Benchmarking

Measure whether the new path helps the intended workloads.

Benchmark groups:

- Existing pure IDL/RDL benchmarks.
- Mixed BV + scheduling benchmarks from the motivating workload.
- Synthetic BV-controlled scheduling benchmarks.
- Existing mixed arithmetic benchmarks that should continue using Simplex.

Compare:

- Current Simplex mixed-theory path.
- New IFW/RFW E-graph path.
- Pure IFW/RFW where applicable.
- Z3 Floyd-Warshall-enabled baseline if useful for external comparison.

Metrics:

- Wall-clock time.
- SAT conflicts/decisions.
- Number of E-graph equalities sent to IFW/RFW.
- Number of generated interface lemmas.
- Number of Floyd-Warshall updates.
- Memory use.

## Risks And Mitigations

### Explanation Unsoundness

Risk:

- A conflict path may include E-graph-origin edges without a complete explanation.

Mitigation:

- Treat every E-graph-origin edge as carrying an explanation reference.
- Add focused unsat-core and conflict tests involving E-graph equalities.

### Disequality Handling

Risk:

- Difference logic naturally handles bounds, not disequality disjunctions.

Mitigation:

- Handle disequalities lazily through model reconciliation and interface lemmas, following the Simplex pattern.

### Model-Reconciliation Loops

Risk:

- E-graph and IFW/RFW repeatedly disagree without progress.

Mitigation:

- Ensure each generated interface lemma rules out the current bad equality partition.
- Add tests that require at least one interface lemma.

### IDL Overflow

Risk:

- IFW uses signed 32-bit path lengths, which may be too narrow for some mixed workloads.

Mitigation:

- Keep explicit overflow detection.
- Fall back to Simplex in auto mode.
- Report a clear error in explicit mode.

### Incrementality

Risk:

- The E-graph architecture may assume stronger push/pop or atom-creation support than IFW/RFW currently provides.

Mitigation:

- Restrict the first version to one-shot contexts if necessary.
- Add explicit config rejection for unsupported incremental use.
- Treat on-the-fly atom creation for interface lemmas as a separate prerequisite from ordinary IFW/RFW push/pop support.
- Extend incrementality only after one-shot correctness and interface-atom creation are established.

### Architecture Proliferation

Risk:

- Adding explicit `EGRAPH + X + IFW/RFW` enum values may grow the architecture table.

Mitigation:

- Keep the first set narrow.
- Do not introduce a component-based architecture refactor in this change.
- Consider a later refactor to build architectures from component flags after Milestone 5.

## Suggested Milestones

### Milestone 1: Compile-Time Attachment Skeleton

- Add E-graph metadata to IFW/RFW variables.
- Add interface constructor stubs.
- Add context construction paths behind explicit config.
- Reject unsupported operations cleanly.

Exit criteria:

- Builds cleanly.
- Existing tests pass.
- Explicit unsupported mixed use returns a controlled error rather than asserting.

### Milestone 2: Equality Constraints

- Implement E-graph equality assertions by subtracting attached triples, checking that the result is DL-representable, then adding the corresponding pair of difference constraints.
- Add explanation records for E-graph-origin equality edges.
- Support simple E-graph + IFW/RFW UNSAT cases.

Exit criteria:

- Tests pass for equality-driven IDL/RDL conflicts.
- Unsupported compound-triple equalities fail or fall back through the documented path.
- Conflict explanations are valid.

### Milestone 3: Model Reconciliation

- Decide and implement the interface-atom creation policy.
- Implement model hooks.
- Add disequality/interface-lemma support.
- Add model tests for satisfiable mixed formulas.

Exit criteria:

- E-graph + IFW/RFW can produce correct SAT models.
- Disequality tests require and validate interface lemmas.

### Milestone 4: BV + Difference Logic

- Enable BV solver and IFW/RFW together under the E-graph.
- Add QF_BV plus scheduling-style tests.

Exit criteria:

- BV + IDL/RDL mixed tests pass.
- No regression in existing BV or IDL/RDL tests.

### Milestone 5: Auto-Selection And Documentation

- Add eligibility-based auto-selection.
- Document the new solver combinations.
- Benchmark intended workloads.

Exit criteria:

- Explicit and auto modes behave predictably.
- Documentation explains limitations.
- Benchmarks show whether the new architecture is worth enabling by default for selected logics.

## Open Questions

1. Should the first version support arrays/functions plus IFW/RFW, or only BV plus IFW/RFW?
2. How much incrementality is required before exposing the feature broadly?
3. What public logic names should advertise this path, given that SMT-LIB does not standardize every useful BV-plus-difference-logic combination?

## Recommended First Implementation Slice

Start with one-shot `EGRAPH + IFW` and `EGRAPH + RFW` without BV. This isolates the Nelson-Oppen boundary before adding BV.

Then add `EGRAPH + BV + IFW/RFW` once:

- Equality assertions are explained.
- Models reconcile.
- Disequality/interface lemmas work.

This sequencing reduces the chance that BV bit-blasting noise hides a theory-combination bug in the new IFW/RFW interface.
