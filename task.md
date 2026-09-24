# Independent type safety: working state

Updated 2026-09-24 for branch `typesafety`.  This file owns the current state,
agenda, open decisions, and working notes for the independent language work.
The [development plan](plan.md#15-establish-independent-core-type-safety) links
this track to the repository roadmap.  The [proof journal](plans/type-safety-journal.md)
preserves the history of proofs, failed approaches, and test results.

## Current checkpoint

| Item | State |
|------|-------|
| Objective | Complete the independent runtime-language definition and its type-safety proofs, extending the checked core through the remaining operation families. |
| Branch base | `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`. |
| Latest proof milestone | Exact core injection, Unit, and sum-elimination execution in this revision; preceding published proof checkpoint `e9470e55` established first-step inversion. |
| Latest specification commit | `2a3747f4`: first derived Option/Except increment. |
| Active branch | `typesafety`, tracking `origin/typesafety`. The ongoing proof session incorporated the concurrent working-record update `72c89e7f` before publishing this milestone. |
| Last complete proof check | The ongoing proof session passed twenty-three build jobs, 758 semantic examples, and 438 theorem audits on 2026-09-24. Every audited theorem uses at most `propext`. |
| Separate checkout attempt | The documentation session attempted a check at `6f12ef18` and stopped while acquiring the shared Lean lock. This historical attempt is distinct from the completed checks in the ongoing proof session. |
| Next proof | Transparent derived-sum constructors and combinators, exact typing/inference/relevance, followed by their exact public execution laws. |
| First derived-sum increment | Transparent Option/Except constructors, map/bind, and map-error, with exact typing, inference, relevance, and execution laws. |
| Open language decision | Inclusion or exclusion of payload-discarding APIs under the relevance profile. |

The latest completed sequence is exact environment and branch lookup support
(`049fd3b7`), raw operational correspondence (`afc81685`), and continuation
decomposition (`08a7d50a`), first-step inversion (`e9470e55`), and core sum
execution in this revision.
The [derived-sum specification](plans/type-safety-derived-sums.md)
records the next increment.  Its definitions and proofs remain pending.

## Scope and established semantics

The current calculus has independently defined syntax, extrinsic typing,
executable machine transitions, and a complete type-safety theorem for those
definitions.  Under a well-typed program, `closed_type_safety` proves that every
state reached by a finite execution of a well-typed closed expression retains
its result type and can either step or produce a permitted terminal outcome.
`type_safety` also covers typed open states with environments and continuations.
`return_type` and `overflow_is_justified` characterize completed outcomes.

The language uses deterministic, strict, left-to-right evaluation.  A conditional
executes its condition and selected arm.  A call evaluates arguments in order
and starts its body in a fresh parameter environment.  Recursion and mutual
recursion are admitted.  General termination and overflow-freedom remain
separate proof obligations.

The relevance profile requires each introduced binding and function parameter
to occur syntactically in its scope.  Product elimination binds both fields,
and the profile rejects projections.  Repeated uses and uses in a single branch
are allowed.  Profile admission combines this check with ordinary typing.
Runtime safety uses configuration typing.  Ownership permissions and all-path
usage require their own judgments.

Bounded naturals and array lengths are below `2^64`.  Natural addition and
multiplication can terminate with a tagged, mathematically justified overflow.
Checked array operations represent failure as `inl unit` and success as
`inr payload`.  Arrays are persistent mathematical values.  Missing bindings,
missing functions, and malformed eliminations produce stuck raw states, which
the safety theorem excludes for typed executions.

The broader runtime-language theorem requires the remaining syntax, semantics,
and proofs listed below.  Adequacy for the existing LeanExe source language,
extraction correctness, physical memory management, and WebAssembly compiler
correctness are separate tracks.  The existing compiler has demand-based cases
whose correspondence with this strict language remains open.  Lean's kernel
and the audited foundation form the proof's trusted basis.

## Completed proof inventory

The [language definition](docs/runtime-language.md) specifies the rules.  The
[proof reference](docs/type-safety.md) gives theorem statements and module details.
All module paths below belong to `LeanExe/TypeSafety` and are imported by the
[independent build target](LeanExe/TypeSafety.lean).

| Area | Checked content | Source |
|------|-----------------|--------|
| Core expressions and calls | Unit, Bool, bounded naturals, words, products, annotated sums, variables, lets, conditionals, product/Unit/sum/natural elimination, and direct calls with exact argument types and arity. | [Core judgments](LeanExe/TypeSafety/Core.lean), [machine rules](LeanExe/TypeSafety/Machine.lean). |
| Formation and nominal declarations | Type/table formation, exact Boolean checks, monomorphic recursive declarations, finite value typing, and exhaustive branch arities.  Empty types are permitted. | [Formation](LeanExe/TypeSafety/Formation.lean), [core judgments](LeanExe/TypeSafety/Core.lean). |
| Machine and safety | Lexical environments, typed frames and continuations, determinism, progress, preservation, finite-execution safety, result typing, and justified overflow. | [Machine](LeanExe/TypeSafety/Machine.lean), [safety proofs](LeanExe/TypeSafety/Safety.lean). |
| Admission and inference | Exact relevance checks, profile safety, total inference, checker soundness/completeness, public program admission, and expression type uniqueness. | [Profile](LeanExe/TypeSafety/Profile.lean), [typing checker](LeanExe/TypeSafety/Typing.lean). |
| Bounded naturals | Add/subtract/multiply/divide/remainder/min/max, comparisons, overflow laws, derived successor/predecessor/Boolean conversion, and zero/successor case analysis. | [Natural operations](LeanExe/TypeSafety/NatOperations.lean), core and machine. |
| Explicit-width words | 8/32/64-bit modular arithmetic, unsigned comparisons, conversions, AND/OR/XOR, complement, and width-masked logical shifts with arithmetic per-bit laws. | [Bit operations](LeanExe/TypeSafety/BitOperations.lean), [word operations](LeanExe/TypeSafety/WordOperations.lean). |
| Persistent arrays | Typed empty construction, size, checked get/set/push/append, exact failure and result laws, length bounds, element ordering, and read-after-write. | [Array operations](LeanExe/TypeSafety/ArrayValues.lean). |
| Derived Booleans | NOT and strict AND/OR/XOR/equality expansions, typing, inference, relevance, evaluation staging, and truth tables. | [Boolean expansions](LeanExe/TypeSafety/BoolDerived.lean). |
| Structural equality | Exact raw value/list comparison, independent `EqTy` admission, constructive Boolean-table stabilization bound, exact terminating domain checker, and strict homogeneous source equality. | [Value equality](LeanExe/TypeSafety/ValueEquality.lean), [finite-table bound](LeanExe/TypeSafety/EqualityFlags.lean), [equality domain](LeanExe/TypeSafety/EqualityTypes.lean). |
| Binding transport | Capture-avoiding traversal, pointwise map laws, syntax identity/composition, context transport, typing preservation, and ordinary/prefix-preserving weakening. | [Renaming](LeanExe/TypeSafety/Renaming.lean). |
| Relevance transport | Exact free-occurrence images, protected-prefix use, expression/list/branch admission equality, and profile typing transport/weakening. | [Renaming and relevance](LeanExe/TypeSafety/RenamingProfile.lean). |
| Environment transport | Exact raw lookup agreement, identity/composition, lifting, prefix insertion, and branch lookup preserving absence and arity. | [Renaming environments](LeanExe/TypeSafety/RenamingEnvironments.lean). |
| Operational transport | Per-frame environment relations, exact optional step results, both finite-trace directions, terminality/stuckness, and exact return/overflow/stuck-reachability equivalences. | [Renaming dynamics](LeanExe/TypeSafety/RenamingDynamics.lean). |
| Continuation sequencing | Continuation extension, exact finite boundary decomposition, and return/overflow/stuck sequencing equivalences. | [Continuation proofs](LeanExe/TypeSafety/Continuations.lean). |
| First-step inversion | Exact head decomposition; no-successor start and endpoint laws; exact first-operand return/overflow/stuck sequencing. | [Execution proofs](LeanExe/TypeSafety/Execution.lean). |
| Core sum execution | Exact arbitrary-expression injection/Unit/sum return, overflow-record, and stuck-reachability laws, including malformed shapes and selected-body behavior. | [Sum execution](LeanExe/TypeSafety/SumExecution.lean). |

`inferRaw_iff` characterizes raw expression typing.  Public inference additionally
checks formation of declarations, signatures, and context.  The checker-to-safety
theorems are `checked_type_safety` and `profile_checked_type_safety`.

Raw structural comparison covers every finite value tree.  Source equality
requires the independent `EqTy` judgment, whose domain excludes recursive nominal
dependencies, including recursion beneath arrays and unused sum alternatives.
Every field of every constructor participates in equality-domain admission.

## Current agenda

### Derived-sum execution support

- [x] Run the complete maintained proof gate in the ongoing proof session; the latest successful result is recorded above.
- [x] Prove exact continuation-extension stepping laws with an explicit boundary at `ret value []`.
- [x] Prove successful finite-trace extension and execution decomposition at that return boundary.
- [x] Prove general first-step inversion for the derived-form execution arguments.
- [x] Prove exact raw injection, Unit-elimination, and sum-elimination outcomes, including malformed shapes.
- [ ] Use those laws to characterize derived-form returns and faults in both directions for arbitrary scrutinee executions.
- [x] Add focused continuation/execution examples and all support theorem audits, run the maintained check, and record the results and proof difficulties in the journal.
- [x] Integrate core sum execution into the gate with focused semantic examples and all new theorem audits.
- [ ] Repeat that integration for the individual derived APIs.

Appending a continuation can enable a step from `ret value []`.  An
unconditional equality of optional step results across continuation extension
would therefore be false.  The checked continuation laws isolate this return
boundary and decompose execution through it.  `appendKont_returns_iff`,
`appendKont_overflows_iff`, and `appendKont_reaches_stuck_iff` distinguish
operand outcomes from continuation outcomes.  The
[derived-sum proof obligations](plans/type-safety-derived-sums.md#required-results)
specify the required statements and behavior checks.

The completed renaming theorems provide exact environment lookup agreement,
including absence, under `EnvCorresponds`.  `FrameCorresponds`,
`KontCorresponds`, and `StateCorresponds` preserve matching optional steps and
transfer finite traces in both directions.  `rename_returns_iff`,
`rename_overflows_iff`, and `rename_reaches_stuck_iff` compare exact results under
the same program, with arbitrary raw values and initially empty continuations.
Their premises permit noninjective maps when every mapped lookup agrees.

Existing syntax traversal fixes type annotations, function IDs, nominal IDs,
constructor tags, and branch arities.  Its binder depths are:

| Body | Protected prefix |
|------|------------------|
| Let body, each sum arm, natural successor arm | One value. |
| Complete product-pattern body | Left then right, at indices zero and one. |
| Nominal match arm | Its explicit field arity, in field order. |
| Unit elimination and natural zero arm | Zero values. |
| Called function body | Fresh argument environment in parameter order.  Caller bindings remain in suspended continuations. |

The checked continuation relation gives each suspended frame its own map and
captured environment.  Calls enter unchanged program bodies with identical
argument environments under the identity map and retain the related caller
continuations.  Return, overflow, and stuck-reachability equivalences apply
without typing premises.

### Option/Except derived forms

- [x] Specify `Option α := Sum Unit α` and `Except ε α := Sum ε α`, callback binding, and the first API's evaluation rules.
- [ ] Define transparent constructors, Option map/bind, Except map/bind, and Except map-error using the existing syntax.
- [ ] Prove typing, exact inference, free-occurrence equations, and exact profile-admission equations for each expansion.
- [ ] Prove supplied-sum and arbitrary-scrutinee execution laws in both directions, distinguishing scrutinee faults from selected-callback faults.
- [ ] Check captures, fresh calls, skipped and selected failing callbacks, strict scrutinee evaluation, malformed payloads, and nested sums, then run the maintained check and audit every new theorem.
- [ ] Decide inclusion or exclusion of payload-discarding APIs and specify the remaining defaults, filters, tests, fallback, and conversion operations.

The [first derived-sum specification](plans/type-safety-derived-sums.md) scopes
callback code under `payload :: Γ`.  An operation evaluates its scrutinee once
and executes only the selected callback in the captured lexical environment.
Option's None arm consumes Unit with `unitCase`; a raw non-Unit left payload
remains stuck.  Except's forwarding arm retains its payload.  Admission requires
a syntactic use of the callback's payload binding.

The first increment leaves payload discard as an open design decision.  Expansions
of `isSome`, `isOk`, and Except-to-Option can introduce unused pattern fields and
fail current admission.  Resolving that conflict requires an explicit policy
decision.  Dummy occurrences would defeat the chosen relevance rule.

### Remaining language coverage

These obligations follow the binding work.  Their order awaits the relevant
design decisions.  The [coverage ledger](docs/type-safety-coverage.md) records
their relationship to the documented LeanExe operation families.

| Family | Remaining work |
|--------|----------------|
| Array construction and wrappers | Literals, replicate, emptiness, defaults, back/pop, slicing, insert/erase/swap/reverse, and specified checked/trapping/fallback behavior. |
| Array callbacks | Map/filter/modify/find/find-index/any/all, captured environments, traversal order, bounds, and early exits. |
| Folds, loops, and recursion forms | Complete accumulator/element/index binding rules, range-step arithmetic, and done/yield/failure behavior, through primitive rules or proved expansions. |
| Bytes | Representation, signatures, bounds, copy/slice behavior, endian conversions, and precise failures. |
| Binary64 | Permitted floating-point results, including NaNs and exceptional values, plus operation laws and safety for every permitted result. |
| Data generalizations | Specialization and any intended dependent/indexed or further type-level features. |
| Generic traps and trapping wrappers | An inclusion decision and explicit typing, execution, and permitted-failure rules. |
| Counter reads and explicit release | An inclusion decision, abstract state, permission/ownership judgments, and their soundness proofs. |
| Static strings and source libraries | Compile-time admission/desugaring boundaries and separate ASCII/JSON library correctness obligations. |

Each primitive extension requires formation, canonical forms, binding lemmas,
progress, preservation, reachable-state safety, exact executable admission,
and type uniqueness for its defined behavior.  Each derived form requires an
explicit hygienic expansion and typing, relevance, and evaluation proofs.

## Verification and working notes

### Maintained checks

The [type-safety check](tools/type-safety.js) builds the independent target,
runs nineteen semantic example files with warnings treated as errors, and checks
the transitive axiom dependencies of every listed theorem.  Its accepted axiom
set is `{propext}`.  The recorded toolchain is Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, selected by `lean-toolchain`.

```sh
tools/type-safety.js check
```

The driver invokes `tools/leanrun` for each Lean/Lake command with a 120-second
command timeout and a 30-second lock wait.  Standard execution applies
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`,
`LEAN_NUM_THREADS=1`, `nice -n 10`, and `ionice -c 3`, with the shared machine
lock.  The [repository instructions](AGENTS.md) govern runner failures and
diagnostic timeouts.  Local execution without cgroups requires explicit user
authorization. The user authorized local execution in the ongoing proof
conversation, including its 2026-09-24 checks. That authorization does not
change the default for separate sessions.

Documentation checks are:

```sh
git diff --check
tools/check-docs.js
```

### Current notes

In the separate documentation checkout on 2026-09-24, its local check failed
because the sandbox blocked spawning
`tools/leanrun` with `EPERM`.  The approved retry reached the runner and exhausted
its 30-second wait for the machine-wide slot.  The driver reported status 75
for `lean --version`.  This records lock acquisition failure before Lean
execution. The ongoing proof session has independently completed the full gate,
as recorded above; that result does not claim a successful run in the other
checkout.

The documentation review passed whitespace and checker-syntax checks.  The
complete documentation check reports one existing failure in the
[WGSL review](paper/wgsl-verification-report/review.md): an absolute temporary
workspace path in its opening paragraph.  The new working record's links pass
that check.

Recent occurrence proofs acquired a `Quot.sound` dependency through
simplifier-generated function extensionality beneath existential predicates.
Explicit witness transport and a Boolean-disjunction image lemma reduced the
dependencies to the allowed set.  Pointwise map statements and audits of helper
theorems remain relevant to the next proof.  The journal also records that
explicit local equality types resolved simplifier matching between `lift` and
`liftN 1`.

The operational proof used successful-option extraction lemmas to handle
unreduced machine steps in the finite-trace argument.  Its examples cover
caller captures and fresh callees, different binder prefixes, noninjective maps
in both directions, finite recursive prefixes, exact tagged faults, forged
overflow records, and malformed return frames.  The journal records all
eighteen new proof declarations within the existing axiom limit.

Continuation extension and decomposition added twenty audited proofs using
only `propext`.  The 24 new examples check the empty-return boundary, existing
frames before the appended suffix, fresh callees, operand versus continuation
faults, forged overflow, blocked operands, and both directions of the exact
outcome equations.  These results preserve the existing primitive syntax,
typing rules, and transition function.

Exact occurrence transport uses an existential image under arbitrary maps.
Protected-prefix laws preserve the use of existing local bindings.  Newly
inserted function parameters still need their own uses, and public admission
still checks formation of an inserted context.

First-step inversion added eight audited proofs using only `propext`. Five
additional examples bring the continuation/execution file to 29 examples. They
exercise a counterexample without the endpoint premise, a malformed no-successor
frame, and the three first-operand sequencing laws. The initial example run
needed explicit starting states in two theorem applications; the corrected full
gate passed. The concurrent documentation commit `72c89e7f` was preserved during
publication rather than replacing its working record.

Core sum execution adds 27 audited declarations and 23 semantic examples. The
laws quantify over arbitrary scrutinees and distinguish malformed shapes from
selected branch behavior. The documentation checker was also rerun in the
ongoing proof session: its only reported failure remains the existing absolute
temporary path in the WGSL review noted above.

The original development record calls for checked milestones with status
updates, commits, and pushes.  Important design changes and added dependencies
require user confirmation.  This working record changes with each milestone
or blocker: it keeps the current agenda and evidence here, with detailed proof
history in the journal and normative rules in the language reference.
