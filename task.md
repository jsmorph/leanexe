# Current task: complete compiler correctness on correct — in progress

The user resumed compiler work on `correct` from main on 2026-09-26.
The user requested continued work until compiler correctness covers the entire
LeanExe dialect, with frequent updates, commits, and pushes. Main through
`fb8cd5da` is merged into `correct`, including the drone proofs and the call-result
annotation fix. This compiler-proof task remains active; the completed drone task
is preserved separately at the end of this file. Lean runs locally through
`tools/leanrun`. Full-dialect correctness is not yet proved.

Directly applied named Boolean helpers now accept UInt64 or Bool arguments and
Bool results, including standard Id annotations. Exact source binders and
lexical captures are preserved. The recognizer checks matching parameter domains
and proves that removing the helper binder preserves the argument. Captures,
nesting, scalar/step conditions, Id actions and loop exits are checked.

The general source-to-WASM theorem and all sixteen axiom audits pass. Native
Lean/V8 agree on 1,587 inputs across 95 declarations, including 27 range
declarations. All 84 prior modules retain identical bytes. New focused tests
pass 2,200 native/IR comparisons and 720 invalid-input tests. Previous fixtures
pass 1,496 comparisons and 316 rejections.

Evidence, exact modules, source hashes and proof logs are in
[the named Boolean helper archive](proofs/compiler/named-boolean-2026-09-26/README.md).
The preceding [immediate application](proofs/compiler/boolean-application-2026-09-26/README.md),
[saved decision](proofs/compiler/saved-decision-2026-09-26/README.md),
[dependent decision](proofs/compiler/dependent-decision-2026-09-26/README.md),
[compound guard](proofs/compiler/guard-decision-2026-09-26/README.md), and
[atomic comparison](proofs/compiler/reannotation-2026-09-26/README.md) archives
record their checked increments.

Next: support reusable UInt64-to-Bool local helpers in arbitrary enclosing scalar
bodies, with a distinct typed function binding and Boolean environment. Preserve
captures, check unused bodies, and reject word/Boolean function type confusion.
Then extend the same capability to loop steps and broader helper signatures.
Full-dialect correctness remains unfinished. Get each capability proved and
executing end to end, and commit/push frequently.

## Reusable Boolean functions — in progress

A distinct predicate-function binding now represents UInt64-to-Bool closures
in source values and compiled lexical bindings. Its matching relation requires
the compiled result to evaluate to the native Boolean's zero/one encoding.
Flags and predicate functions have separate fields in the Boolean environment;
ordinary value binders shift both kinds of captures.

The environment, typed lookups, binding matching and existing scalar/step
compiler proofs pass. The current named-helper fixtures still pass 2,200
comparisons and 720 invalid-input checks. Predicate-call syntax, typed lexical
lookup, acceptance, scope, evaluation correctness and IR structural-property
proofs now pass. Reusable helper declarations are next; this capability is not yet admitted or
recorded as complete. Run the full theorem and selected native/Wasm checks after
those parts are integrated.

## Directly applied named Boolean helpers — complete

The source form retains a named helper whose entire binding body applies it to
one argument. The argument may capture outer values but cannot reference the
helper. Arrow/lambda domains match exactly, and result annotations are checked.
Independent recognition and Boolean parser proofs, scalar/step correctness,
the general compiler theorem, sixteen axiom audits and native/V8 checks pass.
Repeated calls from an arbitrary body remain subsequent work.

## Immediate Boolean lambda applications — complete

`BooleanBindingForm` preserves either the original let binding or immediate
lambda application. Both use typed lexical binding evaluation. Source size,
parser acceptance/soundness, scalar correctness and loop-step correctness pass.
New focused tests cover captures, nested scopes, annotations, unused arguments,
dependent conditions, Id actions and loop exits. Native fixtures assert that
elaboration retains the lambda applications.

The general compiler theorem, fourteen axiom audits and native/V8 checks pass.
Named Boolean helper bindings and calls remain subsequent work.

## Saved proposition decision equivalence — complete

Saved `decide` values and ordinary/dependent Boolean-result proposition choices
retain checked `DecidedGuard` evidence. The source proposition guard keeps its
distinction from direct Boolean conditions. Scalar and loop-step correctness
proofs pass, including reconstruction under erased proof binders.

The general compiler theorem, fourteen axiom audits and emitted-Wasm checks pass.
Focused tests cover saved/captured flags, nested Boolean choices, helper bodies,
Id actions, unused values, loop break/continue, decision evidence and proof domains.

## Dependent decision equivalence — complete

The recognizer checks standard `GuardDecision` evidence and both exact
proof-lambda domains. Scalar and loop-step source evaluation retain the erased
binder. Canonical syntax helpers remain available through canonical witnesses.

Validation completed:

- General source-to-WASM theorem and all fourteen axiom audits.
- `scalar_dependent_decision.lean`: 132 comparisons across six scalar and two
  range declarations, including nested binders, helpers and Id actions.
- `scalar_dependent_decision_syntax.lean`: 336 comparisons and 264 invalid-input
  checks of evidence, connective instances, propositions and proof domains.
- Previous dependent-if and compound syntax tests: 640 comparisons, 152 rejections.
- Native Lean/V8: 1,035 comparisons across 62 declarations; 54 prior binaries
  unchanged. Source reannotation evaluation is rechecked with the new guard type.

Saved decisions and Boolean-result proposition choices are the next annotation
gap. Boolean compound subguards retain their exact standard evidence.

## Compound decision equivalence — complete

`GuardDecision` independently describes standard decision evidence for guard
trees. Its recognizer soundness and acceptance pass Lean checking and are included
in the fourteen-declaration compiler audit. Ordinary scalar and loop-step guard
admission shares the existing tree lowering.

Validation completed:

- General compiler theorem and all fourteen axiom audits.
- `scalar_guard_decision.lean`: 132 native/IR comparisons across six scalar and
  two range declarations, including helpers, Id actions, nested and negated guards.
- `scalar_guard_decision_syntax.lean`: 336 comparisons and 144 invalid-input tests
  with nested junctions, literal and Boolean subguards, and repeated negation.
- The preceding atomic source/syntax fixtures: 1,550 comparisons and 990 rejections.

The native Lean/V8 run passes 903 comparisons across 54 declarations.
Differently annotated decision operands in
dependent branches and saved decisions remain subsequent work. Boolean compound
subguards retain their exact standard evidence.

## Merged compiler proof integration — complete

Main's shared scalar programs preserve branch result types. The general compiler
translation now retains those i64/i32 types, and its binary-translation witness
agrees. The complete compiler proof passes after this correction. The initial
failure and focused proof diagnostics are retained for the evidence archive.

## Atomic comparison operand equivalence — completed at aadf243e

The source relation covers exact expressions, standard UInt64 arithmetic heads,
standard numerals and corresponding metadata wrappers. Checked recognizer
soundness and acceptance connect that relation to ordinary scalar and loop-step
comparison admission. This includes all six propositional comparisons, Boolean
equality/inequality guards, nested negation, local helper bodies and Id actions.
Compound guard evidence, dependent branch evidence and saved decisions still
require identical condition and decision operands.

Validation completed:

- General compiler theorem and all twelve axiom audits; only the standard
  `propext`, `Classical.choice`, and `Quot.sound` allowances are used.
- `scalar_reannotation.lean`: 150 native/IR comparisons.
- `scalar_reannotation_syntax.lean`: 1,400 comparisons and 990 invalid-input tests
  across ten arithmetic operations and ten comparison forms.
- `scalar_id_comparison.lean`: 264 comparisons and four rejected declarations.
- `scalar_comparison_id_type.lean`: 252 comparisons and 210 invalid-input tests.

The selected native/WASM run passes 771 comparisons across 46 declarations.
The first engine invocation caught missing names in the checked corpus list;
that list is corrected, and V8 passes using the already-built artifacts. No
Lean rebuild was needed for the test configuration fix. This checkpoint does
not claim full LeanExe dialect correctness.

## Main integration — complete

Main includes `ciogpt` through `3a0222be`. The fetched `origin/main` at `a4655383`
was already an ancestor, so the merge was a fast-forward with no conflicts or
code changes. The compiler, proof, and runtime checks recorded below apply to
the merged code. Documentation and whitespace checks pass on main.

Next: continue compiler coverage incrementally, with end-to-end proofs and
execution checks for each capability, keeping this file current and committing
and pushing frequently.

## User documentation — complete

The README and linked guides describe current capabilities, runnable examples,
and proof boundaries. GPT-2 FP32/quantized generation, Euler, numerical kernels,
byte I/O, scalar compilation and artifact verification have direct entry points.
The documentation index, capabilities page, manual, language/compiler references,
scalar proof guide, core type-safety introduction and development setup agree
with those boundaries. Exact FP32 source and packaged-binary claims are distinct.
The README uses direct descriptions of capabilities, commands, and proof scope,
without filler introductions or metaphors.

Validation: the documented scalar quickstart builds, compiles and returns 42
in Wasmtime; all 178 maintained Markdown files pass the documentation check;
local heading targets and whitespace are checked. GPT command arguments are
checked against the Python parsers and implementation. Model execution and
Python dependency downloads are outside this documentation-only validation.

The documentation is included in main. Further compiler coverage follows the
incremental proof and execution workflow below.

---

# Current integration: ciogpt — complete

The user requested `ciogpt` from `correct`, merging `iogpt`, then pushing it for a
subsequent merge into main. Merge commit `6f05315c` has parents `correct` at
`49f79f0f` and `iogpt` at `8f703c51`. The final extraction fix is `cbefab5e`.
Both commits are pushed to `origin/ciogpt` and included in main.

All six textual conflicts are resolved, retaining both compiler/proof tracks,
both development histories, arithmetic and multi-export CLI entries, and both
extraction dependencies. The prior correct checkpoint's pending arithmetic
evidence is retained separately from this integration's fresh results.

The merge exposed three areas needing repair. The scalar shortcut now applies
only to single-export compilation, so mixed scalar/byte-array exports are kept.
Arithmetic class-method resolution preserves runtime operands such as byte
indexing; exact standard UInt8/UInt32 numeral evidence preserves the previous
emitted constants while custom instances retain their actual meanings. A broader
raw-constant-folding attempt changed existing GPT instructions and was discarded.
The byte-I/O validator uses an explicit `List.head!` simplification after the
shared decoder import narrowed. No proof statement or premise was weakened.

Fresh integration validation is COMPLETE:

- All nine general scalar compiler axiom audits and 527 native Lean/V8 comparisons
  across thirty declarations pass. All thirty emitted modules match correct.
- All 46 byte-I/O theorem audits and the freshly compiled exact echo binary pass.
- Running-sum source passes nine audits; its exact binary passes all six decoding,
  validation and import/export audits and matches fresh compiler output.
- All four regenerated GPT models and annotation caches match iogpt. The three
  quantized binaries also match their registered artifacts byte for byte. The
  current FP32 output remains 18,966 bytes and matches the iogpt model; its separate
  historical frozen artifact remains 19,083 bytes. This distinction predates ciogpt.
- Four narrow numeral cases, 56 class-evidence comparisons, six narrow arithmetic/
  byte-access probes and the mixed multi-export test pass.
- All twelve selected runtime/documentation commands pass: byte I/O and host,
  heap loops, reference counts, quantized operations, FP32, packed data, running
  sum, CLI diagnostics, LEB encoding, thirteen WAT/binary comparisons and 178
  maintained Markdown files. Byte I/O, quantized operations and mixed exports
  pass again after the final extraction adjustment.

Evidence, hashes, commands and preserved failures are in
[the integration archive](proofs/compiler/ciogpt-2026-09-25/README.md).
The broader source/artifact aggregates, large GPT reference runs and unrelated
type-safety archive retain their parent-revision records; they were not rebuilt
for this merge. General correctness still applies to the admitted scalar/range
subset. Byte I/O retains its modeled-host boundary, and running sum still lacks
a universal WASM execution and memory theorem.

The main merge is complete. Further dialect coverage remains incremental,
following the scalar work record below; each increment needs end-to-end proofs,
execution checks, a current task record, and frequent commits/pushes.

---

# Scalar compiler correctness: arithmetic complete; expanding coverage

## Current instructions and status — local continuation, 2026-09-24

The user explicitly resumed work on `correct` here and authorized running Lean
locally, with frequent commits and pushes. This section supersedes the stopped
handoff below. The user removed both the separate clean-checkout requirement
and deliberate compiler/package/harness breakage checks. Do not reinstate them.
The false-equality control is also omitted from the current driver. Type-safety
checks remain explicitly requested. Continue the ordinary proof build, actual
compiler execution comparisons, standalone source proof package, and docs.

The arithmetic milestone is complete. The real compiler and Node/V8 passed all
85 comparisons across seven declarations, including source admission and all
reserved-export checks. The general proof passed all nine axiom audits. The
independent type-safety check passed its 19 behavior-test files and 438 theorem
audits. The standalone archive rebuilt all 133 bundled source modules and passed
all nine audits (3164 Lake jobs). These results use candidate `878cfd1e` and are
preserved in `proofs/compiler/arithmetic-2026-09-24/`, including the exact archive,
emitted modules, native expected results, logs and verification metadata.

Completed next increment: pure UInt64 `let` bindings, including nested bindings,
shadowing, unused bindings and zero-argument declarations. Candidate `d777caf2`
passed the full general source-to-byte compiler theorem and all nine axiom
audits, plus all 142 native Lean/Wasm comparisons over twelve declarations.
Source admission and all reserved exports also passed. The increment's evidence
is in `proofs/compiler/let-2026-09-24/`. The extractor substitutes only pure total
arithmetic expressions; this preserves source results but can expand emitted
code/repeat computations. No type-safety implementation changed, so its prior
438-theorem audit was not repeated.

Completed next increment: UInt64-valued conditionals over `=`, `<`, `≤`, `>`,
`≥`, `==`, and `!=`, with exact standard instance and decision evidence.
Candidate `b06b8e12` passed the general proof and all nine axiom audits, plus
254 native Lean/Wasm comparisons over twenty declarations. Static bounds cover
both branches; nested choices and branch-local bindings are included. The first
execution attempt exposed distinct `GT.gt`/`GE.ge` heads, which were then added
and proved before repeating the checks. Evidence is retained in
`proofs/compiler/conditionals-2026-09-25/`.

Completed next increment: standard pure `Id.run do` operations, UInt64 monadic
bindings, straight-line updates, early returns, nested blocks and branch-local
binds. Candidate `140ce818` passed all nine general compiler axiom audits and
339 native Lean/Wasm comparisons across twenty-seven declarations. Evidence is
retained in `proofs/compiler/do-2026-09-25/`. Complete standard Id instance
expressions are checked; no backend emission changes were needed.

Completed next increment: local UInt64 functions, lexical captures and the
continuations introduced by joined `do` branches and branch updates. Candidate
`d73e047d` passed all nine general compiler axiom audits and 437 native Lean/Wasm
comparisons across thirty-four declarations. Evidence is retained in
`proofs/compiler/local-functions-2026-09-25/`. The source model distinguishes
word/Unit/function bindings internally while preserving the public scalar ABI.
All function bodies are checked, including unused ones. Plain unary functions
and the `Unit → UInt64 → result` update-continuation form have distinct binding
kinds. Other arities and top-level helpers remain outside this increment.

Completed next increment: one bounded `[:count.toNat]` range loop with a UInt64
accumulator and yielding steps. Candidate `f4ffe0e0` (proof sources from
`d1fbcaf7`) passed all nine general compiler axiom audits and 582 native Lean/V8
comparisons across forty-one declarations. Source admission and reserved-export
checks passed. Evidence is retained in `proofs/compiler/range-2026-09-25/`.
The proof connects native ascending range iteration to source extraction,
ordinary scalar IR, the actual annotated emitter, exact complete module bytes,
validation and exported execution. It covers zero iterations, explicit
UInt64.ofNat index conversion, wrapping accumulators, step bindings and scalar
conditional updates, captures and pure computations before/after the loop.
The loop uses three fresh locals and the remaining iteration count as a
termination measure. Constant bounds currently use a UInt64 value followed by
.toNat. Breaks, continue, other range starts/steps, multiple accumulators and
multiple/nested loops remain outside this increment. Focused dependency builds
and cached general checks were used; the fixed arithmetic archive and unrelated
438-theorem type-safety suite were not rebuilt.

Completed next increment: direct local-function bindings in the yielding loop
body. Candidate `430802eb` passed all nine general compiler axiom audits and
217 native Lean/V8 comparisons across ten range declarations, with source
admission and reserved-export checks. Evidence is retained in
`proofs/compiler/range-local-functions-2026-09-25/`. The yield wrapper preserves
binding types and order; the scalar extractor checks all bodies, including
unused functions. Captures retain the accumulator value from the binding point
even across later updates. Unsupported bodies and arities remain rejected.
The fixed range test group avoids recompiling unchanged arithmetic fixtures.

Completed next increment: standard Id monadic UInt64 bindings (`let x ← …`)
inside yielding loop steps. Candidate `728098c4` passed all nine general compiler
axiom audits and 289 native Lean/V8 comparisons across thirteen range declarations,
with source admission and reserved-export checks. Evidence is retained in
`proofs/compiler/range-do-2026-09-25/`. The source relation preserves the exact
standard Bind evidence; the scalar grammar checks each bound value and
continuation. Nested do computations and unused monadic values are included.
The first execution attempt exposed a distinct branching-continuation form;
that failure is retained. Conditional scalar values inside pure are supported,
while custom Bind evidence and breaks after a bind remain rejected.

Completed next increment: yielding branch continuations in range steps.
Candidate `1cfb4228` passed all nine general compiler axiom audits and 385
native Lean/V8 comparisons across seventeen range declarations, including
source admission and reserved-export checks. Evidence is retained in
`proofs/compiler/range-branches-2026-09-25/`. The independent YieldType relation
preserves function domains and binder information while removing the yielding
result wrapper. Syntax conversion handles continuation types/bodies and both
branches together, while the scalar extractor checks the full result. Joined
monadic branches, mutable branch updates followed by computation, nested
branches and continue now work end-to-end. The previously rejected monadic join
is an explicit passing fixture. Breaks, unused done-returning functions, and
custom comparison evidence remain rejected.

Completed next increment: early-exit range loops. Candidate `f22803ce` passed
all nine general compiler axiom audits and 601 native Lean/V8 comparisons across
twenty-six range declarations, plus admission and reserved-export checks.
Evidence is retained in `proofs/compiler/range-break-2026-09-25/`, including the
initial borrowed-Nat metadata failure and correction, all exact emitted range
modules, native expected results, hashes and final logs. Break, updated done
values, step-valued continuations, both function shapes and continue mixed with
break now work through the actual public compiler and full module theorem.
The new four-local layout stages the decision before the value; the termination
proof uses the result of remaining native iterations. The unchanged arithmetic
archive and independent runtime suite were not rebuilt. The general proof
includes type validation of every admitted program.

Early-exit preparation journal (superseded by the completed result above).
At the initial checkpoint, `Source/ScalarRangeExit.lean` proves bounded
early-exit iteration agrees with native List/range ForIn behavior, including
the accumulator produced by done. The existing yielding iteration is proved
to be a special case. `IR/ScalarIterationExit.lean` proves finite while
execution for either advancing the index or moving it directly to the bound
after done. Both focused targets pass. Source extraction, the actual local-slot
layout, emitted control flow, general proofs and execution tests remain pending;
the public compiler still rejects break while this capability is developed.
The concrete four-local layout now has checked reads/writes, decision staging,
accumulator updates, index advance/exit and complete IR loop execution in
`IR/ScalarRangeExitSlots.lean`. The exit decision is evaluated before changing
the accumulator; done moves the index to the stop, and yield increments it.
The focused target passes, including zero iterations and the returned done
accumulator in the universally quantified statement.
The source step grammar and total evaluation theorem now pass in
`Source/ScalarStep.lean`, with separate scalar/step-valued closures, exact
done/yield, scalar comparisons, binds and both continuation shapes. Its lexical
values project step functions to inaccessible Unit placeholders when checking
scalar subterms, preserving binder positions while preventing a step result
from being used as a scalar. This is isolated from the completed scalar model.
Extraction and the public source/function integration remain pending.
The paired code/binding interface in `Extract/ScalarStepBindings.lean` also
passes: one compiled continuation carries value and done projections for the
same native step outcome. Its scalar projection preserves binding positions
and the existing scalar matching relation. The source totality audit uses only
the three permitted logical axioms. No public extraction behavior has changed
in these preparation commits.
`Extract/ScalarStep.lean` now compiles done/yield, scalar branches, binds,
scalar functions and both step-valued continuation shapes into paired IR
expressions. Its result-type checks and reusable equations pass, as does
`ScalarStepCorrectness.lean`: both projections preserve the same source step
and leave locals unchanged. `test/scalar_range_exit.lean` passed 120 native
Lean/IR comparisons using the concrete early-exit loop layout, including
returned done values, wrapping, joined branches and both continuation shapes.
Source acceptance/success support, static bounds, whole-function extraction,
Wasm proofs and public execution checks are still pending.

The step admission proofs now pass in both directions: every independently
supported step compiles under total typed bindings, and every successful
extraction belongs to that grammar, including unused function bodies.
`ScalarStepInvariant.lean` proves both projections preserve scalar expression
invariants for later arithmetic/local-read bounds. The separate whole-range
source model also has checked total evaluation, preserving early-exit outcomes
and scalar computations before/after the loop. These focused targets pass;
whole-function extraction and WebAssembly integration remain in progress.

Whole early-exit range extraction now passes acceptance, success-support,
scalar-invariant preservation, source semantics, and complete IR function
execution proofs. The four-local layout evaluates the exit flag before the
accumulator and normalizes the index to the bound on done. Result computations
are proved valid for every final flag. A separate focused test passed 144 native
Lean/whole-function IR comparisons across six actual do/for declarations:
break, update-before-break, joined binds, captured helper calls, branch updates,
and continue mixed with break. The public compiler and WebAssembly proof
connection remain pending; these isolated tests do not claim that integration.

The early-exit backend connection now passes as well: recognition of the actual
IR, exact annotated instruction emission, scratch accounting, typed instruction
sequences, terminating WebAssembly loop execution, whole-function execution,
and complete function-body byte parsing. The loop invariant tracks the native
result of remaining iterations, with the same decreasing index rank for yields
and immediate termination for done. The new proof modules built from cached
dependencies; public source dispatch and whole-module tests are next.

Public scalar extraction now tries the proved early-exit range after the pure
and yielding-range cases. Source declaration support/application and all general
function/module/validation/invocation proofs include the new case. The full
affected compiler proof target and nine axiom audits pass. Nine public execution
fixtures and updated admission tests are ready for the focused native/V8 check;
that check is still pending at this candidate checkpoint.

The first public range execution run accepted the real break cases but exposed
borrowed Nat metadata on the explicit Unit-prefixed step-function fixture.
The old exact range-head recognizer rejected that annotation before reaching
the already-proved step compiler. `ScalarRangeExitSyntax.lean` now retains the
exact annotated index type and checks that removing only metadata yields Nat;
the full standard ForIn instance evidence and matching binder type remain
checked. The independent source grammar carries this checked type, and focused
acceptance, support, preservation and IR proofs pass. The failed execution log
is retained. The Unit-prefixed fixture now exercises yielding before done as
well as wrapping. Final general proof and engine reruns follow this correction.

Completed next increment: direct ForInStep constructor expressions. Candidate
`37cef9bf` passed all nine general compiler audits and 673 native Lean/V8
comparisons across twenty-nine range declarations, with admission and reserved
exports. Evidence is in `proofs/compiler/range-direct-2026-09-25/`. Callbacks and
both local continuation shapes can return unwrapped done/yield values. The
source grammar and proofs cover these directly; the existing early-exit Wasm
layout is reused. The focused native/IR test passed 216 comparisons. All
twenty-six prior range modules retained byte-for-byte identical output.

Completed next increment: standard Nat literal range bounds. Candidate
`49c8e055` passed all nine general compiler audits and 793 native Lean/V8
comparisons across thirty-four range declarations, including admission and
reserved exports. Evidence is in `proofs/compiler/range-count-2026-09-25/`.
The source count model retains Nat semantics and proves scalar lowering cannot
wrap; literals must use the standard OfNat evidence and be smaller than 2^64.
Tests include zero, one, small loops with break and the maximum bound with an
immediate exit; overflow and custom literal instances reject. The focused test
passed 120 native Lean/IR comparisons and two rejection tests. All twenty-nine
prior range modules retained identical bytes. The general proof includes full
type validation; the fixed arithmetic archive and unrelated runtime suite were
not rebuilt.

Completed next increment: loop-step result bindings and nested standard Id
computations. Candidate `317cbb8b` passed all nine general compiler audits and
985 native Lean/V8 comparisons across forty-two range declarations, including
admission and reserved exports. Evidence is in
`proofs/compiler/step-results-2026-09-25/`. The independent typed step environment
now distinguishes step results from scalar values and functions. Ordinary lets,
aliases, captures, computed pure results, straight-line monadic binds and Id.run
preserve both the value and exit decision. Exact result annotations admit any
number of standard Id layers. All 192 focused native Lean/IR comparisons passed;
unused unsupported computations and custom instance evidence reject. All
thirty-four prior modules retained identical bytes. Initial Id-annotation and
joined-bind failures are retained. The fixed arithmetic archive and unrelated
runtime suite were not rebuilt; general type validation passed.

Completed next increment: local functions taking loop-step results. Candidate
`a56a2a6d` passed all nine general compiler audits and 1,129 native Lean/V8
comparisons across forty-eight range declarations, including admission and
reserved exports. Evidence is in `proofs/compiler/result-functions-2026-09-25/`.
The previously rejected joined monadic branch now works. A distinct typed
binding carries a complete native step argument and its paired compiled
projections. Captures, chained calls, ignored arguments, unused bodies and
nested Id annotations are checked. All 144 focused native Lean/IR comparisons
passed; unsupported unused bodies and other argument/result domains reject.
All forty-two prior modules retained identical bytes. General type validation
passed; the fixed arithmetic archive and unrelated runtime suite were not rebuilt.

Completed next increment: UInt64 inequality and negated comparison conditions.
Candidate `95ea4329` passed all nine general compiler audits and the full
1,764-result/94-declaration native Lean/V8 group, including source admission and
reserved exports. Evidence is in `proofs/compiler/negative-conditions-2026-09-25/`.
The recursive comparison model preserves canonical Ne, repeated Not and exact
standard decision evidence. Source recognition, semantic lowering, Wasm
recognition, encoding and typing are checked. All 198 focused native Lean/IR
comparisons passed across twelve new declarations, including negation of every
comparison family, repeated negation, functions and monadic binds, plus break,
continue and step-result branch joins. Custom decision expressions reject.
All eighty-two previous modules retained identical bytes. The fixed arithmetic
archive and unrelated runtime suite were not rebuilt; general type validation
passed. Boolean ! and compound conditions remain separate capabilities.

Completed next increment: nonzero standard literal range starts with unit step.
Candidate `6aa364fd` passed all nine general compiler audits and 1,465 matching
native Lean/V8 results across sixty-two range declarations, including admission
and reserved exports. Evidence is in `proofs/compiler/range-interval-2026-09-25/`.
The native interval, truncated distance and shifted index proofs connect the
new source syntax to the existing early-exit backend. All 264 focused native
Lean/IR comparisons and three rejection tests passed. Equal/reversed bounds,
break/continue, captured helpers, result joins, high indices and huge intervals
with immediate exits are included. All fifty-one previous range modules kept
identical bytes. General type validation passed; unrelated suites were not rebuilt.

Completed next increment: dynamic range starts from supported UInt64 expressions.
Candidate `ce8443b8` passed all nine general compiler audits and 1,729 matching
native Lean/V8 results across seventy-three range declarations, including
admission and reserved exports. Evidence is in
`proofs/compiler/range-dynamic-2026-09-25/`. Both endpoints share the checked
source model. Truncated distance, offset and captured-start semantics connect
to the existing loop backend. All 264 focused native Lean/IR comparisons and
two rejection tests passed. Computed/conditional bounds, captured initial
accumulators, high indices, empty/equal bounds, break/continue and result joins
are included. All sixty-two preceding range modules retained identical bytes.
General type validation passed; unrelated suites were not rebuilt.

Completed next increment: positive standard literal range strides.
Candidate `a98a6517` passed all nine general compiler audits and 2,017 matching
native Lean/V8 results across eighty-five range declarations, including
admission and reserved exports. Evidence is in
`proofs/compiler/range-stride-2026-09-25/`. Native strided traversal, the bounded
ceiling-divided count and scaled source indices connect to the existing backend.
All 288 focused native Lean/IR comparisons and four rejection tests passed.
Uneven distances, dynamic endpoints, captures, high indices, maximal steps,
empty ranges, break/continue and result joins are included. Explicit stride
proofs are retained; numeric positivity and representability are checked
independently. All seventy-three prior range modules kept identical bytes.
General type validation passed; unrelated suites were not rebuilt.

Completed next increment: local functions with two UInt64 arguments and scalar
results. Candidate `7dcd290c` passed all nine general compiler audits and 2,850
matching native Lean/V8 results across 143 declarations, including admission
and reserved exports. Evidence is in
`proofs/compiler/binary-functions-2026-09-25/`. Distinct function bindings retain
argument order and captured values. Both pure expressions and helpers defined
inside loop steps have checked acceptance/support, semantics and invariants.
All 270 focused native Lean/IR comparisons and six rejection tests passed,
covering captures/shadowing, chained/nested helpers, unused bodies, Id results,
conditionals and break/continue. All 128 prior modules kept identical bytes.
General type validation passed; unrelated suites were not rebuilt.

Completed next increment: local functions with two UInt64 arguments returning
ForInStep UInt64, including standard Id result wrappers. Candidate `1579917a`
passed all nine general compiler audits and 2,401 matching native Lean/V8
results across 101 range declarations, including admission and reserved exports.
Evidence is in `proofs/compiler/binary-step-functions-2026-09-25/`. Both arguments,
lexical captures and the paired value/exit result have checked source semantics,
acceptance, preservation and invariants. All 240 focused native Lean/IR comparisons
and five rejection tests passed. All 91 preceding range modules retained identical
bytes. General type validation passed; unrelated suites were not rebuilt.

Completed next increment: Boolean `!` over standard UInt64 equality/inequality
guards, including repeated negation and combination with propositional `¬`.
Candidate `3c620953` passed all nine general compiler audits and 3,298 matching
native Lean/V8 results across the full 165-declaration group, including admission
and reserved exports. Evidence is in `proofs/compiler/boolean-not-2026-09-25/`.
Independent Boolean syntax and native semantics preserve exact standard BEq
and decision evidence. The polarity lowering, encoding and type validation are
checked. All 208 focused native Lean/IR comparisons and three rejection tests
passed, covering pure/monadic branches, local functions, computed operands,
break, continue and result joins. All 153 preceding modules kept identical bytes.

Completed next increment: local scalar helpers defined before a range loop,
with lexical captures available to its bounds, initial value, body and final
result. Candidate `01d0c335` passed all nine general compiler audits and 2,737
matching native Lean/V8 results across 115 range declarations, including
admission and reserved exports. Evidence is in
`proofs/compiler/range-outer-functions-2026-09-25/`. The source/IR proofs cover
unary, binary and Unit-prefixed helpers, retaining captures for every loop state.
All 240 focused native Lean/IR comparisons and four rejection tests passed.
All 105 preceding range modules kept identical bytes. General type validation
passed; unrelated suites were not rebuilt.

Completed next increment: ordinary UInt64 let bindings whose value is a range
computation. Candidate `e11f409a` passed all nine general compiler audits and
2,977 matching native Lean/V8 results across 125 range declarations, including
admission and reserved exports. Evidence is in
`proofs/compiler/range-let-results-2026-09-25/`. Source/IR acceptance, support,
preservation and invariants compose the loop result with its pure continuation.
All 240 focused native Lean/IR comparisons and three rejection tests passed,
covering nested lets, aliases, shadowing, unused results, stepped exits,
continue, monadic continuations and captured helpers. All 115 preceding range
modules kept identical bytes. General type validation passed; unrelated suites
were not rebuilt.

Completed next increment: UInt64 bitwise complement through the direct primitive
and standard `~~~` operator. Candidate `efaa5c37` passed all nine general compiler
audits and 3,986 matching native Lean/V8 results across the full 197-declaration
group, including admission and reserved exports. Evidence is in
`proofs/compiler/complement-2026-09-25/`. Exact source heads and native semantics
are connected to XOR-with-all-ones lowering, extraction and scalar invariants.
The public range/source proof includes the new literal-bound syntax distinction.
All 208 focused native Lean/IR comparisons and three rejection tests passed,
covering arithmetic, guards, functions, monadic code, break/continue and
complemented interval bounds near the UInt64 limit. All 185 preceding modules
kept identical bytes. General type validation passed; unrelated suites were not
rebuilt.

Completed next increment: nested propositional conjunction and disjunction
through scalar conditionals and loop-step results. Candidate `943588a1` passed
all nine compiler audits and 4,242 native Lean/V8 comparisons across 211
declarations, including admission and reserved exports. Evidence is in
`proofs/compiler/compound-guards-2026-09-25/`. Separate recursive guard syntax
checks the entire standard decision evidence and every pure, total operand;
proved lowering reuses existing Boolean-word AND/OR and equality operations.
All 256 focused native Lean/IR comparisons and three rejection tests passed,
covering truth tables, mixed nesting, negated leaves, zero divisors, functions,
monadic joins, break, continue and step-result continuations. All 197 prior
modules kept identical bytes. The general proof includes type validation;
unrelated suites were not rebuilt.

Completed next increment: negation around compound propositional guards,
including repeated Not wrappers and arbitrary nesting. Candidate `1c6a528b`
passed all nine compiler audits and 4,450 native Lean/V8 comparisons across
223 declarations, including admission and reserved exports. Evidence is in
`proofs/compiler/compound-negation-2026-09-25/`. The shared guard syntax retains
wrapper counts and exact decision evidence; proved lowering tests each previous
Boolean word against zero. All 208 focused native Lean/IR comparisons and three
rejection tests passed, covering negated truth tables, nested groups, functions,
monadic joins, break, continue and step-result continuations. All 211 prior
modules kept identical bytes. General type validation passed; unrelated suites
were not rebuilt.

Completed next increment: Boolean &&/|| guards with repeated ! at any nesting
level. Candidate `f55d3440` passed all nine compiler audits and 4,658 native
Lean/V8 comparisons across 235 declarations, including admission and reserved
exports. Evidence is in `proofs/compiler/boolean-compound-2026-09-25/`.
Independent Boolean syntax converts to the shared guard representation with
proved operand and native-result preservation, and the common CompoundGuard
interface reuses the existing scalar/loop-step integration. All 208 focused
native Lean/IR comparisons and three rejection tests passed. All 223 preceding
modules kept identical bytes. General type validation passed; unrelated suites
were not rebuilt.

Completed next increment: Boolean compounds inside propositional conjunction,
disjunction and negation, including repeated negation at either layer.
Candidate `cf104d36` passed all nine compiler audits and 4,866 native Lean/V8
comparisons across 247 declarations, including admission and reserved exports.
Evidence is in `proofs/compiler/mixed-guards-2026-09-25/`. Mixed guard nodes retain
both wrapper kinds and exact decision evidence. The checked Boolean compiler
helper composes with the propositional compiler, retaining the existing public
scalar/step integration. All 208 focused native Lean/IR comparisons and three
rejection tests passed. All 235 preceding modules kept identical bytes. General
type validation passed; unrelated suites were not rebuilt.

Completed next increment: standard UInt64 min/max with exact instance checks.
Candidate `93471a4b` passed all nine compiler audits and 5,074 native Lean/V8
comparisons across 259 declarations, including admission and reserved exports.
Evidence is in `proofs/compiler/extrema-2026-09-25/`. Native min/max are connected
to unsigned comparison/selection lowering and independent source rules, with
scalar and whole-function proofs carrying them through helpers, do blocks,
loop steps and bounds. All 208 focused native Lean/IR comparisons and three
rejection tests passed, including high-bit ordering and short near-limit
intervals. All 247 preceding modules kept identical bytes. General type
validation passed; unrelated suites were not rebuilt.

Execution checks now support fixed named groups in
`test/arithmetic-engine-groups.json`. The initial `guard-core` group passed all
295 native Lean/V8 comparisons across seventeen existing declarations. This
reduces repeated compiler invocations for narrow increments. Each increment
still checks the general compiler and type proofs and records its exact
execution scope. The full 259-declaration comparator also passed against the
already generated min/max artifacts after the driver change.

Completed next increment: Boolean and propositional literal guards.
Candidate `73760621` passed all nine compiler audits and all 503 native
Lean/V8 comparisons in the fixed 29-declaration `guard-literals` group. Evidence
is in `proofs/compiler/literal-guards-2026-09-25/`. Shared guard source, parser and
lowering proofs carry literals and repeated negation through scalar expressions,
helpers, do blocks and loop control. Both branches remain checked. All 208
focused native Lean/IR comparisons and three rejection tests passed. The
seventeen selected preceding modules kept identical bytes. The full corpus now
has 271 declarations; this execution run checked 29. General type validation
passed, using cached dependencies; unrelated suites were not rebuilt.

Completed next increment: PUnit.{1} do-block continuations.
Candidate `af86f5d8` passed all nine compiler audits and all 453 native
Lean/V8 comparisons in the fixed 24-declaration `punit-continuations` group.
Evidence is in `proofs/compiler/punit-continuations-2026-09-25/`. A shared concrete
unit syntax description carries both spellings through scalar and step helper
semantics, yielding conversion and outer range helpers. The original generated
branch-update join now passes. All 228 focused native Lean/IR comparisons and
three rejection tests passed. The twelve selected preceding modules kept
identical bytes. The full corpus now contains 283 declarations; this execution
run checked 24. General type validation passed with cached dependencies.

Completed next increment: retained scalar Id result and bind annotations.
Candidate `4c8beae3` passed all nine compiler audits and all 471 native
Lean/V8 comparisons in the fixed 26-declaration `id-annotations` group. Evidence
is in `proofs/compiler/id-annotations-2026-09-25/`. Recursive result annotations
are checked in standard run/pure/bind operations, with exact bind input/parameter
agreement. Shared scalar and loop proofs cover helpers and computations before
and after a loop. All 208 focused native Lean/IR comparisons and three rejection
tests passed. The fourteen selected preceding modules kept identical bytes.
The full corpus now contains 295 declarations; this execution run checked 26.
General type validation passed using cached dependencies.

Completed next increment: arbitrary finite UInt64 parameter lists for local
scalar helpers. Candidate `e3e3f2a5` passed all nine compiler audits and
all 571 native Lean/V8 comparisons in the fixed 31-declaration `finite-arity`
group. Evidence is in `proofs/compiler/finite-arity-2026-09-25/`. Shared syntax,
argument-list and closure rules preserve exact arity, source order, captures,
strict operand checking and unused body checking, including helper definitions
inside steps and around loops. All 256 new native Lean/IR comparisons, four
declaration rejection tests and two raw arity rejection tests passed. The
preceding local-function test passed 140 comparisons and three rejection tests;
its former three-argument rejection is now positive. The preceding outer-helper
test also passed 264 comparisons and three rejection tests after the equivalent
admission expectation was updated. The seventeen selected
preceding modules kept identical bytes. The full corpus contains 309 declarations;
this execution run checked 31. General type validation used cached dependencies.

Completed next increment: arbitrary finite UInt64 parameter lists for local
helpers returning complete ForInStep results. Candidate `87a042ad` passed
all nine compiler audits and all 609 native Lean/V8 comparisons in the fixed
28-declaration `step-finite-arity` group. Evidence is in
`proofs/compiler/step-finite-arity-2026-09-25/`. Shared argument-list and closure
rules preserve exact arity, source order, captures and strict checking, with
distinct scalar/step-result bindings and proved value/stop projections. All 240
new native Lean/IR comparisons, four declaration rejection tests and two raw
arity rejection tests passed. The preceding step-helper test passed 264
comparisons and four rejection tests, with its three-argument case now positive.
The eighteen selected preceding modules kept identical bytes. The full corpus
contains 319 declarations; this execution run checked 28. General type validation
used cached dependencies.

Completed next increment: dependent conditionals (`if h : condition then ...
else ...`). Candidate `7d9535a3` passed all nine compiler audits and all 623
native Lean/V8 comparisons in the fixed 34-declaration `dependent-if` group.
Evidence is in `proofs/compiler/dependent-if-2026-09-25/`. Exact decision and
proof-lambda domain checks preserve an erased binder in each branch context.
Scalar and step source semantics, totality, acceptance, support, correctness
and output invariants cover the new form. All 304 focused native Lean/IR
comparisons, four declaration rejection tests and four proof-domain rejection
tests passed. The eighteen selected preceding modules kept identical bytes.
The full corpus contains 335 declarations; this execution run checked 34.
General type validation used cached dependencies.

Completed next increment: ordinary internal Boolean local bindings and ordinary
Boolean conditions over saved flags. Candidate `f9d25355` passed all nine
compiler audits and all 623 native Lean/V8 comparisons in the fixed
34-declaration `boolean-locals` group. Evidence is in
`proofs/compiler/boolean-locals-2026-09-25/`. Native and compiled binding kinds
keep Booleans distinct from UInt64 values, with proved zero/one representation.
Independent source rules, totality, acceptance, successful extraction support,
correctness and invariants cover aliases, negation, conjunction/disjunction,
helper captures, loop steps and outer loop bindings. All 304 focused native
Lean/IR comparisons, four declaration rejection tests and four binding-kind
rejection tests passed. Eighteen selected preceding modules kept identical
bytes. The full corpus contains 351 declarations; this execution run checked 34.
General type validation used cached dependencies.

Completed next increment: dependent conditions over saved Boolean flags.
Candidate `fec27059` passed all nine audits and 623 native Lean/V8 comparisons
across the fixed 34-declaration `boolean-dependent` group. All 304 native/IR
comparisons, four declaration rejections and six proof-binder rejections passed.
The 18 selected preceding modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-dependent-2026-09-25/`. Exact proof-domain checks and
erased binder positions preserve captures throughout helper and loop scopes.
The full corpus contains 367 declarations; this run checked 34. Type validation
used cached dependencies; the fixed archive and runtime suite were not rebuilt.

Completed next increment: standard UInt64 numeral instances behind constant
let/lambda/application/metadata wrappers. Candidate `422d32d8` passed all nine
compiler audits and 537 native Lean/V8 comparisons across the fixed 30-declaration
`literal-instances` group. The original captured helper that failed in the prior
increment now passes unchanged. All 208 focused native/IR comparisons, four
custom-instance declaration rejections, five raw instance rejections and one
metadata check passed. Eighteen selected preceding modules kept identical bytes.
Evidence is retained in `proofs/compiler/literal-instances-2026-09-25/`. The corpus
contains 379 declarations; this execution run checked 30. No backend or runtime
change, full archive rebuild or unrelated runtime-suite rebuild was needed.

Completed next increment: standard Nat numeral expressions at UInt64 conversion
and numeric-instance positions, with type/value metadata. Candidate `f6151291`
passed all nine compiler audits and 537 native Lean/V8 comparisons in the fixed
30-declaration `natural-numerals` group. Both preceding saved failure forms now
pass unchanged. All 208 focused native/IR comparisons, four declaration
rejections, five raw numeral rejections and two metadata checks passed. The 18
selected preceding modules kept identical bytes. Evidence is retained in
`proofs/compiler/natural-numerals-2026-09-25/`. The corpus contains 391 declarations;
this run checked 30. No emitter/runtime changes or unrelated archive/runtime
suite rebuilds were needed. Custom instances and general Nat arithmetic remain
outside the admitted source grammar.

Completed next increment: standard Id Boolean monadic bindings in scalar code,
helper bodies, loop steps and computations surrounding a loop. Candidate
`d17cbd2f` passed all nine compiler audits and 623 native Lean/V8 comparisons
across the fixed 34-declaration `boolean-bind` group. All 304 focused native/IR
comparisons, four declaration rejections, six raw bind rejections and two
metadata checks passed. The first failure exposed inferred Id Bool action
annotations; the grammar/parser proofs now retain nested Id annotations and
the unchanged fixture passes. Eighteen selected preceding modules kept
identical bytes. Evidence is retained in
`proofs/compiler/boolean-bind-2026-09-25/`. The full corpus contains 407
declarations; this was a focused execution run. No emitter/runtime changes or
unrelated archive/runtime suite rebuilds were needed.

Completed next increment: Boolean-valued conditionals over Boolean guards,
including saved flags, ==/!= comparisons, literals, negation and junctions.
Candidate `27abf6a0` passed all nine compiler audits and 623 native Lean/V8
comparisons across the fixed 34-declaration `boolean-choice` group. All 304
focused native/IR comparisons and twelve rejection checks passed on the first
execution run. The earlier Boolean-local/dependent tests also pass unchanged:
608 native/IR comparisons and eighteen rejection checks. Eighteen selected
preceding modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-choice-2026-09-25/`. The full corpus contains 423
declarations; this was a focused execution run. The source grammar, parser and
shared Boolean lowering were extended; scalar/step/loop proofs reused their
interfaces. No emitter/runtime changes or unrelated suite rebuilds were needed.

Completed next increment: Boolean-valued choices with propositional guards,
including all six UInt64 comparisons, propositional literals, negation and
junctions with existing closed Boolean leaves. Candidate `30d47e67` passed all
nine compiler audits and 623 native Lean/V8 comparisons across the fixed
34-declaration `proposition-choice` group. All 304 new native/IR comparisons
and twelve rejection checks passed on the first execution run. The preceding
Boolean-choice fixture also passes unchanged: 304 comparisons and twelve
rejections. Eighteen selected preceding modules kept identical bytes. Evidence
is retained in `proofs/compiler/proposition-choice-2026-09-25/`. The full corpus
contains 439 declarations; this was a focused execution run. Source/parser and
shared lowering proofs cover the new form; scalar/step/loop proofs reuse their
interfaces. No emitter/runtime changes or unrelated suite rebuilds were needed.

Completed next increment: unary Boolean-parameter helpers returning UInt64 or
ForInStep UInt64, with nested Id result annotations and the continuations Lean
introduces for conditional Boolean binds. Scalar/step semantics, typed support,
totality, extraction proofs and scalar helpers surrounding loops are integrated.
The implementation passed all nine general compiler audits at `8255840f`.
Candidate `548ffaec`, with the same implementation, passed 647 native
Lean/V8 comparisons over 35 declarations. All 328 focused native/IR comparisons
and sixteen rejection checks pass; the preceding propositional-choice fixture
also passes unchanged (304 comparisons and twelve rejection checks). Eighteen
selected preceding modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-function-2026-09-25/`. The full corpus contains 456
declarations; this was a focused execution run.

The three originally inspected conditional-bind examples now compile unchanged.
The fixture's first attempt needed an explicit UInt64 annotation after a nested
Id result. A separate loop test introduced an implicit Prop-to-Bool decide
conversion; that remains unsupported and was replaced by Boolean equality for
this increment. Both failed fixture logs and both original syntax inspections
are retained. An old rejection expectation for an unused Bool → ForInStep
helper was moved unchanged into accepted IR/admission/execution fixtures.
The first failed admission log is also retained. The scalar dispatch realizes its ordinary generated induction
theorem in the defining module with a local 300,000-heartbeat budget; its core
builds in 12 seconds and its proof consumer in 1.2 seconds.

Completed next increment: explicit `decide` and implicit Prop-to-Bool conversions
over the existing closed guard grammar. The parser checks Decidable.decide with
its full standard decision evidence; source syntax/operands/native meaning and
shared lowering extend through unchanged scalar and loop interfaces. Candidate
`c06588b6` passed all nine general compiler audits and 623 native Lean/V8
comparisons across 34 declarations. All 304 focused native/IR comparisons and
twelve rejection tests passed on the first execution run. The preceding
Boolean-function fixture also passed unchanged: 328 comparisons and sixteen
rejections. Eighteen selected preceding modules kept identical bytes. Evidence
is retained in `proofs/compiler/decide-2026-09-25/`. The full corpus contains 472
declarations; this was a focused execution run.

All five inspected declarations rejected before the change and now compile
unchanged, including the implicit conversion in the loop-stop form exposed by
the previous increment. Both syntax logs and source are retained. No emitter,
runtime, scalar dispatch or loop dispatch changes were needed. The cached
proof build includes complete module type validation and the usual nine axiom
audits; unrelated runtime suites and the fixed arithmetic archive were reused.

Completed next increment: Bool.toUInt64 applied to admitted Boolean expressions,
flags, choices and decisions. Native source semantics, typed support, totality
and the scalar compiler/proofs use the existing checked zero/one representation.
Step and surrounding-loop proof modules reuse the scalar interface unchanged.
Candidate `cdfe21b4` passed all nine general compiler audits and 623 native
Lean/V8 comparisons across 34 declarations. All 304 focused native/IR comparisons
and seventeen rejection checks passed on their first fixture run. The preceding
decide fixture passed unchanged: 304 comparisons and twelve rejections. Eighteen
selected preceding modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-word-2026-09-25/`. The full corpus contains 488
declarations; this was a focused execution run. Four original inspected
examples now compile unchanged. No emitter/runtime changes were needed.

Completed next increment: Bool-valued equality and inequality (`==`, `!=`,
BEq.beq and bne) with the exact standard Bool equality instance. Recursive
Boolean inputs preserve typed flags, scalar operands and native equality;
shared lowering compares their checked zero/one words. All scalar/step/loop
semantics and compiler proofs reuse existing interfaces. Candidate `67876321`
passed all nine general compiler audits and 623 native Lean/V8 comparisons
over 34 declarations. All 304 focused native/IR comparisons and twenty rejection
checks passed on the first fixture run. The preceding Boolean-conversion fixture
passed unchanged: 304 comparisons and seventeen rejections. Eighteen selected
preceding modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-equality-2026-09-25/`. The complete corpus contains 504
declarations; this was a focused execution run. Five original inspected
examples now compile unchanged. No emitter/runtime or dispatch changes were needed.

Completed next increment: propositional Boolean equality and inequality guards
(`if flag = other ...`, `if flag ≠ other ...`) in scalar and step conditions,
including dependent branches. An indexed form preserves exact Eq/Ne syntax and
decision evidence while reusing the proved Boolean equality meaning. The
literal-true RHS keeps its previous truth-condition path. Candidate `d4b102ba`
passed all nine general compiler audits and 623 native Lean/V8 comparisons over
34 declarations. All 304 focused native/IR comparisons and 44 rejection checks
pass. Prior equality, Boolean-local and dependent fixtures each pass all 304
comparisons and their twenty/eight/ten rejection tests. Eighteen selected prior
modules have identical bytes, and the five original examples compile unchanged.
Two initial fixture failures came from leading ! consuming a larger proposition;
intended Boolean operands were parenthesized and failures retained. Evidence is
in `proofs/compiler/boolean-proposition-2026-09-25/`. The complete corpus has 520
declarations; this was a focused execution run. No emitter/runtime changes.

Completed next increment: explicit decide and implicit Prop-to-Bool conversions
for Boolean equality/inequality, including saved flags and truth coercions.
The recursive source form retains exact Eq/Ne conditions and standard evidence;
a native decide lemma connects it to the shared Boolean equality lowering.
Candidate `25a0d3b5` passed all nine compiler audits and 623 native Lean/V8
comparisons across 34 declarations. The first focused fixture passed all 304
native/IR comparisons and 36 rejection checks. Prior proposition-guard and
closed-decide fixtures each passed 304 comparisons and their 44/twelve rejection
checks unchanged. Eighteen selected prior modules kept identical bytes. All
five original examples and both retained leading-negation failures now compile
unchanged; all seven bodies are included in the execution fixtures. Evidence is
in `proofs/compiler/boolean-local-decide-2026-09-25/`. The complete corpus contains
536 declarations; this was a focused execution run. No emitter/runtime changes.

Completed next increment: Boolean-result choices guarded directly by Boolean
Eq/Ne, including saved flags, choices and decisions. The unified source form
retains exact conditions/evidence and checks both inputs and both result
branches. A proved literal-true specialization preserves ordinary Boolean
choice lowering. Candidate `2b75649b` passed all nine compiler audits and 623
native Lean/V8 comparisons across 34 declarations. The first focused fixture
passed 304 native/IR comparisons and 44 rejection checks. The preceding
Boolean-local-decide and original Boolean-choice fixtures each passed 304
comparisons and their 36 and twelve rejection checks unchanged. Eighteen
selected prior modules kept identical bytes. Five original examples compile
unchanged and have matching bodies across execution fixtures. Evidence is in
`proofs/compiler/boolean-relation-choice-2026-09-25/`. The complete corpus has 552
declarations; this was a focused execution run. No emitter/runtime changes.

Completed next increment: dependent Boolean-result choices over admitted Boolean
and closed propositional guards. Structural proof-binder insertion/removal has
checked inverse and size lemmas, preserves nested scopes and rejects proof reads.
Its independent native test checked 4,452 binder positions, with 3,987 successful
removals and 465 rejected proof references. Exact proof domains, decision
evidence and source reconstruction are proved. Candidate `ba0b0f70` passed all
nine compiler audits and 623 native Lean/V8 comparisons across 34 declarations.
The first focused fixture passed 304 native/IR comparisons and 76 rejections.
The preceding ordinary relation-choice and dependent-condition fixtures each
passed 304 comparisons and their 44/ten rejections unchanged. Five original
examples compile unchanged with matching bodies across all execution fixtures;
eighteen selected prior modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-dependent-choice-2026-09-25/`. The complete corpus has
568 declarations; this was a focused execution run. No emitter/runtime changes.

Completed next increment: Boolean-local let expressions inside Boolean values.
Exact binding syntax, nested scopes, shadowing and typed captures are retained.
Scalar operands remain wrapped in their original Boolean scope; unused bound
values are still checked. Parser reconstruction, size, completeness, totality,
semantic and invariant proofs pass. Candidate `d7368686` passed all nine compiler
audits and 623 native Lean/V8 comparisons across 34 declarations. The first
focused fixture passed 304 native/IR comparisons and 44 rejections; prior
dependent-choice and Boolean-local fixtures each passed 304 comparisons and
76/eight rejections unchanged. Five original examples compile unchanged with
matching bodies across all execution fixtures; eighteen selected prior modules
kept identical bytes. Evidence is in `proofs/compiler/boolean-let-2026-09-25/`.
The complete corpus has 584 declarations; this execution run was focused. No
emitter/runtime changes; pure bound computations may repeat in compiled code.

Completed next increment: UInt64 let bindings inside Boolean expressions. Exact
word scopes compose with nested/shadowed Boolean bindings. Recursive source type
checks and successful-compilation proofs prevent word slots from being used as
Boolean references; bound values are checked even when unused. Candidate
`2477b2bb` passed all nine compiler audits and 623 native Lean/V8 comparisons
across 34 declarations. The first focused fixture passed 304 native/IR comparisons
and 68 rejections. Five original examples compile unchanged. The preceding word
binding exclusion became `boolWordLetOriginal` with its body unchanged; the
updated Boolean-let fixture passed 318 comparisons and 39 rejections after also
promoting four raw word-let shapes. Its before/after source is retained. The prior
dependent-choice fixture passed 304 comparisons and 76 rejections unchanged.
Eighteen selected prior modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-word-let-2026-09-25/`. The corpus has 600 declarations;
this was a focused run. No emitter/runtime changes; pure computations may repeat.

Completed next increment: standard Id type annotations on Boolean/UInt64 lets
inside Boolean expressions, including nested Id layers. Exact annotations remain
in source syntax; derived scalar operands use underlying types with checked
size and annotation-independent evaluation rules. Two execution failures exposed generated operand types and annotated arithmetic
result types; both are retained and the fixture was unchanged by the fixes. All
ten word operations admit the latter with exact inputs and instance evidence;
a focused test passed 420 native/IR comparisons and 100 malformed-head rejections.
Two earlier invalid probe drafts are also retained separately from the five valid
pre-implementation examples, which now compile unchanged. Candidate `1feb91fb`
passed all nine audits and 623 native Lean/V8 comparisons across 34 declarations.
The focused fixture passed 304 native/IR comparisons and 100 rejections. Prior
word-let and Boolean-let fixtures passed unchanged with 304/318 comparisons and
68/39 rejections. Eighteen selected prior modules kept identical bytes. Evidence
is in `proofs/compiler/boolean-let-annotation-2026-09-25/`. The full corpus has
616 declarations; this was a focused run. No emitter/runtime changes.

Completed next increment: standard Boolean Id.run/pure operations nested inside
Boolean expressions, including Id annotations and metadata. Shared recursive
value/action syntax preserves exact source expressions and native meanings.
All source/parser/lowering proofs and nine compiler audits passed. Candidate
`44637199` passed 623 native Lean/V8 comparisons across 34 declarations; the
focused fixture passed 304 native/IR comparisons and 164 rejections. All five
original probes compile unchanged. Prior annotated-let and word-let fixtures
passed unchanged (304 comparisons each, 100/68 rejections); eighteen prior
modules kept identical bytes. Evidence is retained in
`proofs/compiler/boolean-nested-id-2026-09-25/`. The corpus has 632 declarations;
this was a focused run. No emitter/runtime changes.

Completed next increment: standard nested Id annotations on ordinary lets,
including matching numeral instance layers. Exact let syntax and annotations
remain in the source relation; extraction removes one checked Id layer at a time
and preserves the underlying binding rules. All scalar, step and range source,
extraction and correctness proofs pass. Candidate `cef8b86e` passed all nine
compiler audits and 623 native Lean/V8 comparisons across 34 declarations.
The first focused fixture passed 304 native/IR comparisons, eighteen typed-numeral
comparisons and 148 rejection tests (four declarations, 64 malformed lets and
eighty malformed numeral forms). All five original examples compile unchanged.
The twenty focused/admission bodies and sixteen accepted native bodies match.
Prior nested-Id and annotated-Boolean-let fixtures passed unchanged with 304
comparisons each and 164/100 rejection tests. Eighteen prior modules kept identical
bytes. Evidence is retained in `proofs/compiler/id-let-2026-09-25/`. The corpus
has 648 declarations; this was a focused run. No emitter/runtime changes.

Completed before integration: standard Id annotations on arithmetic input and
instance arguments. Candidate `49f79f0f` passed all nine general compiler audits
and 527 native Lean/V8 comparisons across thirty declarations. The first focused
fixture passed 208 comparisons and four declaration rejections; primitive tests
passed 840 comparisons and 300 malformed-head rejections across all ten operations.
The preceding Id-let and primitive-result fixtures passed unchanged, and eighteen
selected prior WASM modules kept identical bytes. Five valid original examples
compile unchanged. The two invalid preliminary drafts are retained separately.
Evidence is in `proofs/compiler/id-arithmetic-2026-09-25/`. The complete corpus
has 660 declarations; the emitted-WASM check was focused. These results apply to
`correct` before the ciogpt merge; combined validation is tracked at the top.

The next completed increment after integration is recorded at the top: Id type
annotations on propositional word comparisons. Differing annotations inside
condition and decision operands remain open. Boolean-returning helpers, Boolean
public ABI, mixed Bool/word helper parameters, saved-flag propositions and loops
inside helpers remain later work.

Current checkout: `/Users/jamiestephens/Documents/Codex/2026-09-24/get/leanexe`.
Local Lean is the pinned 4.34.0-rc2 toolchain; Node is 24.13.0. All Lean commands
continue through `tools/leanrun`, with local mode and a shared serial lock.
The old Linux recovery paths below are historical. After this arithmetic milestone, the user requests incremental expansion to
full leanexe dialect coverage: one capability working through compilation,
proofs, and execution tests before starting the next. Begin with strict `let`,
then conditionals, `do`, and loops as their dependencies permit. Report, commit,
and push each useful step frequently. Type definitions and proofs may change
where needed; preserve their justified guarantees, not their incidental shape.
Use focused checks and Lake's dependency rebuilds, avoiding repeated full builds.
Keep the arithmetic source archive as a fixed milestone. Do not regenerate it
or rerun unrelated full runtime suites for each subsequent feature; check the
changed source/compiler/proof dependencies and that feature's execution cases.

---

# Historical handoff — superseded by the resumed work above

## Stopping-point record — 2026-09-25 UTC / 2026-09-24 America/Chicago

At this historical stopping point, the user requested a documentation handoff
and a pause. The user subsequently authorized resuming implementation and
incremental expansion, with frequent commits and pushes. The current status and
next steps above supersede this stopping-point record. Preserve the journal as
history; its earlier missing-work lists and paused-work instructions do not
describe the current code or authorization.

### What exists and what does not

Repository: `jsmorph/leanexe`. Working branch: `correct`, originally based on
`typesafety` at `834ba204d84720e00deef9b4ce476d4a04e55ff4`. Do not change `main`
or `typesafety`. The separate backend/manual-certificate implementation was
removed earlier (commit `7243e727`); do not restore it as a substitute for this
task. Every admitted source program must inherit the same general theorem.

**Checked and pushed:** the general arithmetic source-to-exact-Wasm-module
compiler theorem, source acceptance theorem, successful-admission soundness
theorem, full module validation, and axiom audit. Their commit is
`5dfcd8f5d42ab945258970f605c7f22e096fa7df` (tree
`9e4ceb98a54c79de6244aceab0fb29109c4c6e79`). The proof build finished successfully
with 3166 jobs before the latest workspace loss. The final general compiler
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

**Not complete:** the arithmetic milestone's final executable/reproducibility
gates and documentation. The larger scalar language agenda is also incomplete.
Do not say the milestone or the whole compiler is certified/completed on the
strength of the checked theorem alone. Use the exact scope and pending gates
below in status reports.

This handoff commit also preserves three gate files already reconstructed and
locally checkpointed before the stop instruction:

- `tools/arithmetic-check.js`: proof/audit/negative-control and CLI/engine driver.
- `test/ArithmeticMilestone.lean`: fresh source declarations and native Lean
  expected results.
- `test/arithmetic_engine.mjs`: independent Node/V8 WebAssembly comparator.

**These reconstructed gate files have not completed a verification run.** A
previous, subsequently lost version passed its proof/audit and kernel-negative
steps. Its native CLI build was still running at the last observed output;
there is no confirmed CLI/engine result. The standalone package script and draft
archive were not pushed before maintenance and are lost. Recreate that script
from the requirements below; do not claim an existing verified package.

### Exact arithmetic contract

The input is the original elaborated `Lean.Expr` body and type of an environment
declaration, not hand-written IR or a program-specific proof certificate. The
declaration must have an executable body, be safe and total, and use an export
name outside the ten reserved runtime names. Independent source support covers:

- Zero or more `UInt64` arguments and one `UInt64` result.
- Argument reads, metadata, literals (including literals reduced modulo 2^64),
  and arbitrary finite nesting of addition, subtraction, multiplication,
  unsigned division/remainder, bitwise and/or/xor, and left/right shifts.
- Direct UInt64 primitive heads and canonical elaborated overloaded heads with
  their exact standard instance evidence, including canonical UInt64 `OfNat`.
- Native UInt64 semantics: modular arithmetic, division by zero returns zero,
  remainder by zero returns the dividend, and shift counts are masked.

Source lets, branches, helper calls, recursion/loops, custom typeclass instances,
runtime Nat, heap values, allocation, imports, mutable globals, and floats are
outside arithmetic admission. Some compile through the general compiler; that
does not put them under the arithmetic theorem. The production output still
contains its actual allocator/reset/retain/release functions and ten runtime
exports; their validation is included. Do not replace the output with a smaller
module to avoid proving these obligations.

Admission checks explicit numeric WebAssembly format limits. In
`LeanExe/Wasm/ArithmeticBounds.lean`, `Fits func entry` bounds by 2^32 the parameter
count, result count, UTF-8 export-name length, locals plus scratch count, actual
encoded user-body payload length, and actual type/export/code payload lengths.
These are executable size checks, not assumptions that generated code is
correct. The body payload includes local declarations, actual emitted user
instructions, and the final end byte. The shared payload definitions are used
by both admission and the layout proofs.

### Public theorem and implementation map

Proof paths in this paragraph are relative to `proofs/talos/lean/`.
`Project/Compiler/SourceCorrectness.lean` defines
`Project.Compiler.ArithmeticModule.Correct α source entry arity bytes`:

```lean
∃ raw, Wasm.Binary.decode bytes = .ok raw ∧
  Validator.validateRaw raw = .ok () ∧
  (Translation.module raw).findExport entry = some 0 ∧
  ∀ (args : List UInt64), args.length = arity →
    ∀ (host : Wasm.HostEnv α) (store : Wasm.Store α),
      ∃ value : UInt64, LeanExe.Source.Scalar.Apply source [] args value ∧
        ∃ N, ∀ fuel ≥ N,
          Wasm.run fuel (Translation.module raw) 0 store
            (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store
```

The module decodes and validates, the requested export resolves to function 0,
and for every input, host and store the invocation terminates with the original
source result and unchanged store. The reversed argument stack is the actual
interpreter calling convention, with source declaration order restored in locals.
Fuel is an interpreter parameter: the result holds for every sufficiently large
fuel, not merely for one selected execution bound.

The public theorems in that namespace are:

| Theorem | Premises and conclusion |
| --- | --- |
| `extracted_correct` | Successful actual scalar extraction, available export name, and `Fits` imply `Correct` for the exact production `CoreWasm.moduleBytes { funcs := #[func] }`. |
| `compileEnvironment_correct` | Original environment lookup/body, safe/total declaration, exportable name, independent `DeclarationSupported`, and explicit format limits imply both normal and arithmetic compilation succeed with the same module, and its exact bytes satisfy `Correct`. |
| `compileEnvironment_sound` | A successful `LeanExe.Extract.Arithmetic.compileEnvironment` result alone yields the original declaration/body and `Correct` for that output's exact bytes. There is no caller-supplied semantic or correspondence certificate. |

The acceptance theorem's limits premise is
`∀ func, extractScalarFunc ... = some func → Fits func entry`; it only states
the numeric bounds on the extractor's result. The admission code checks those
bounds. Source support is defined independently, not as compilation success.

| Repository path | Role |
| --- | --- |
| `LeanExe/Source/Scalar.lean`, `ScalarHead.lean`, `ScalarFunction.lean` | Independent expression/declaration syntax and source application semantics tied to native UInt64 operations. `DeclarationSupported` uses `Arrow`, lambda collection, and source `Supported`. |
| `LeanExe/Extract/ScalarPrimitive.lean`, `ScalarExpr.lean`, `ScalarFunc.lean` | Actual primitive/expression/function extraction; preservation, acceptance, and success-implies-support proofs; real result-slot ABI. |
| `LeanExe/Extract/Core.lean` | Existing normal `compileEnvironment` uses the proved scalar fast path before the general extractor; all ten reserved export names are checked. |
| `LeanExe/Extract/ScalarEntryCorrectness.lean` | `compileEnvironment_of_scalar_extraction` connects successful extraction to the actual normal compiler and its exact single-function IR module. |
| `LeanExe/Extract/Arithmetic.lean` | Strict source admission and size checks, followed by a call to the existing normal compiler. Its IO wrapper uses the existing environment loader. |
| `LeanExe/Extract/ArithmeticCorrectness.lean` | `compileEnvironment_accepts`, `compileEnvironment_success`, and supporting admission proofs. |
| `LeanExe/CLI.lean` | `compile-arithmetic --module ... --entry ... --out ...`; calls strict admission and the production module emitter. |
| `LeanExe/Wasm/Binary.lean`, `LeanExe/Wasm/Image/Emit.lean` | Actual instruction and module byte emitters; no alternate proof-only emitter. |
| `LeanExe/Wasm/ArithmeticBounds.lean` | Executable format bounds and shared actual payload definitions. |
| `proofs/talos/lean/Project/Compiler/SourceFunctionBytes.lean`, `SourceModuleBytes.lean`, `ModuleInvocation.lean`, `SourceInvocation.lean` | Generic source/IR/instruction/byte/execution composition and actual argument/local ABI. |
| `proofs/talos/lean/Project/Compiler/ArithmeticModuleBytes.lean` | Exact full six-section production module bytes and decoder connection; actual runtime bodies and exports included. |
| `proofs/talos/lean/Project/Compiler/FunctionTyping.lean`, `SourceFunctionValidation.lean`, `MetadataValidation.lean`, `ModuleValidation.lean` | User instruction/function validation, full module metadata/exports/lengths, and composed actual validator result. |
| `proofs/talos/lean/Project/Compiler/RuntimeValidation.lean`, `RuntimeRetainValidation.lean`, `RuntimeAllocValidation.lean`, `RuntimeReleaseValidation.lean` | Validation of the fixed actual runtime functions for arbitrary admitted user code and export name. |
| `proofs/talos/lean/Project/Compiler/SourceCorrectness.lean`, `ArithmeticCompilerAudit.lean` | Final compiler theorems and nine dependency audits. |

The axiom audit prints admission acceptance/success, three large runtime
validation results, full module validation, extracted correctness, and both
public compiler theorems. The final theorem whitelist is exactly the three
standard axioms above. Runtime retain/alloc/release proofs use only `propext`.
The independent `LeanExe.TypeSafety` policy remains **propext only**; never
broaden that policy to match the compiler theorem's dependencies.

The trusted boundary includes Lean's kernel and these standard axioms, the
specified source semantics and pinned Wasm interpreter/decoder/validator model.
The source rules explicitly use native Lean UInt64 operations; this is not a
proof of the whole Lean evaluator. The theorem does not kernel-prove CLI IO,
environment-file loading, Node/V8, hardware, or equivalence of the Wasm model to
every engine/specification implementation. The real CLI/engine gate checks that
integration independently. State these limits alongside the positive theorem.

### Resume procedure and environment recovery (do not execute until resumed)

The transient workspace has been removed twice during this session, including
checkout, installed Lean, unpushed gate work, and logs. GitHub commits survived.
Do not rely on a local path or a prior process still existing. Inspect current
Git state first; preserve any unpushed work. If a checkout is gone, clone into a
new directory rather than overwriting a surviving tree:

```bash
git clone --branch correct --single-branch https://github.com/jsmorph/leanexe.git leanexe-resume
cd leanexe-resume
git status --short
git rev-parse HEAD
```

At this handoff the restored checkout is
`/workspace/scratch/d899a1fad5ce/leanexe-recovered`; the older sibling `leanexe`
is a pruned remnant and must not be used. Lean was restored to
`/workspace/scratch/d899a1fad5ce/toolchains/lean-4.34.0-rc2-linux`; proof
dependencies/caches have not been restored after the latest loss. No Lean job
is running at the stop point. These paths are conveniences, not durable inputs.

Read `AGENTS.md` in the recovered checkout. All Lean/Lake/compiler execution
must go through `tools/leanrun`, serially under its shared machine lock. The
user already authorized local execution: `LEANRUN_LOCAL=1` is permitted and
does not require asking again. It retains pinning/locking/timeouts/thread
limits; it does not enforce the standard systemd memory/CPU cgroup limits.
Do not spawn agents without authorization. Provide progress updates at least
every minute while actively working and announce every successful push with
its remote SHA. Commit and push useful checkpoints before long operations,
even when the checkpoint is an explicitly labeled unverified draft.

Pinned Lean: `leanprover/lean4:v4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. If missing, the Linux release archive
is at:

`https://github.com/leanprover/lean4/releases/download/v4.34.0-rc2/lean-4.34.0-rc2-linux.tar.zst`

It is approximately 553 MiB. Extract with
`tar --no-same-owner --zstd -xf <archive> -C <toolchain-parent>`; omitting
`--no-same-owner` previously caused extensive ownership errors. Use absolute
paths in the following environment variables and keep the same lock path
across original checkout, clean checkout, and standalone package runs:

```bash
export LEANRUN_LOCAL=1
export LEANRUN_TOOLCHAIN=/absolute/path/lean-4.34.0-rc2-linux
export LEANRUN_LOCKDIR=/absolute/path/shared-leanrun-lock
tools/leanrun --timeout 30 lean --version
```

Do not repurpose `HOME` or `CODEX_HOME`. Do not call raw `lean`/`lake` or wrap
runner-calling drivers in another `tools/leanrun`: nested calls deadlock on the
same non-reentrant lock and the local runner rejects them.

The proof dependencies are pinned in `proofs/talos/lean/lake-manifest.json`.
Root LeanExe has no external package dependencies. Key proof dependency pins:

| Package | Revision |
| --- | --- |
| CodeLib / talos | `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47` (codelib subdirectory; interpreter in the same checkout) |
| iris | `e7a0a43814c4f1154ca0c8049883ca56c2288b86` |
| mathlib | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |

Use the manifest for exact Qq/batteries/plausible/LeanSearchClient/importGraph/
proofwidgets/aesop/Cli pins. Let Lake fetch the pinned dependencies, or, if
recovery requires manual fetching, read each git entry's URL/revision from the
manifest, initialize `proofs/talos/lean/.lake/packages/<name>`, fetch that exact
revision with depth 1 and check out `FETCH_HEAD`. Respect each entry's subDir.
Independent Git downloads may overlap; Lean processes may not. Do not update
the manifest to newer versions to fix recovery problems.

The focused third-party cache command is:

```bash
tools/leanrun --timeout 900 lake -d proofs/talos/lean exe cache get Mathlib.Tactic Mathlib.Data.Nat.Bitwise Mathlib.Data.List.Sort
```

Earlier cache requests needed roughly 3000 files and several minutes; short
180/300-second attempts timed out after partial downloads. Split remaining
imports/cache work rather than repeatedly rerunning an unchanged timeout.
Third-party caches are allowed for release gates, but the repository's own
LeanExe/Project/Interpreter proof artifacts must be rebuilt from source in the
clean and standalone gates. Never count a download timeout as a failed proof
or a partially completed build as a successful proof.

### Remaining gate 1: actual CLI and independent engine

After a resume instruction, start with the reconstructed driver and fix any
real errors it exposes. It is currently a draft, not accepted evidence:

```bash
tools/arithmetic-check.js engine
```

The driver directly invokes `tools/leanrun` for these stages: native
`lake build lean-wasm` (600-second bound), strict admission regression,
fixture compilation, native Lean evaluation, and the real `compile-arithmetic`
CLI for every fixture entry. Then Node/V8 validates, instantiates, and invokes
the requested exports from those exact `.wasm` files and compares results to
native Lean. The driver itself must not be wrapped in `tools/leanrun`.

Expected fixture set: `constant`, `wrapping`, `quotient`, `remainder`, `shifts`,
`nested`, and `order` in `ArithmeticMilestone`. Fourteen argument pairs for
each two-argument function and one constant result yield **85 comparisons over
seven fresh, unregistered declarations**. Inputs include zero, maximal UInt64,
high-bit values, overflow, zero divisors, shifts by 63/64/65/max, and asymmetric
arguments to detect reversed ABI order. The nested fixture uses all ten
operations. Read the committed fixture for the exact pairs and expressions.
Expected results come from native Lean, not the extractor/IR evaluator.

Logs and artifacts are written under `.lake/arithmetic-check/`:
`<stage>.log`, `<stage>.stderr.log`, `expected.jsonl`, each entry's `.wasm`, and
`engine.log`. The driver captures subprocess output to files and reports stage
completion; it does not continuously print Lean output. While a long stage is
running, read its log and communicate status without launching another Lean
process. Native `Extract.Core:c.o` alone previously took roughly 56 seconds;
a cold native build is materially slower than proof elaboration.

Pass means every stage exits successfully, every module is accepted by V8,
the requested exports exist, and all 85 source/engine results match. Do not
claim a pass from only successful source evaluation or an executable build.
The admission regression in `test/arithmetic_mode.lean` previously passed:
arithmetic/bits/overflow literals match the normal compiler's exact bytes;
lets/branches/helpers/custom instances/wrong types/reserved/missing entries
are rejected; a 2^32 parameter-count check rejects before allocating a huge
type vector. Preserve this behavior and rerun it through the driver.
`test/arithmetic_reserved_exports.lean` separately checks all ten runtime
names, internal functions and ordinary entries; it also previously passed.

For a focused manual CLI diagnostic after fixture compilation, use:

```bash
tools/leanrun --timeout 60 lake env .lake/build/bin/lean-wasm compile-arithmetic --module test.ArithmeticMilestone --entry ArithmeticMilestone.nested --out /absolute/path/nested.wasm
```

### Remaining gate 2: final proof/audit and clean checkout

The focused checked target and the draft automated gate are:

```bash
tools/leanrun --timeout 900 lake -d proofs/talos/lean build Project.Compiler.ArithmeticCompilerAudit
tools/arithmetic-check.js proof
```

Use the driver for the gate, the direct command for a focused diagnostic; do
not run both unnecessarily. The driver audits both final compiler theorem
names against the three-axiom whitelist and runs
`test/negative/arithmetic_kernel.lean`. This intentionally false equality must
fail with `(kernel) declaration type mismatch`; failure caused by a missing
import, timeout, syntax error, or unrelated issue is not a valid negative
control. Audit parsing must handle whitespace/newlines inside the printed
axiom list. Review all nine printed declarations, even though the draft driver
automatically checks only the two final public theorems.

Create a new checkout of the final candidate commit. Record its SHA and clean
Git state. Use only pinned third-party caches; do not copy this repository's
`.lake/build` products. Build the proof/audit from that checkout and run the
CLI/engine gate against its own executable/source. This gate is not satisfied
merely by restoring a previously built checkout. Cold proof builds previously
took several minutes; warm final SourceCorrectness/audit builds took about
3.4/2 seconds. A timeout during many progressing dependency jobs is not proof
completion. After a timeout inspect and reduce the work boundary before retry.

### Remaining gate 3: standalone independently checkable proof package

No verified standalone arithmetic package exists yet. A draft packaging script
was lost before push; recreate it as a repository tool (suggested path
`tools/arithmetic-package.py`) and push its draft before running a long build.
The package must contain the general compiler theorem and actual definitions,
not a generated theorem for selected example programs. Verification must not
execute the compiler CLI or a proof/artifact generator.

The previously computed source import closure of
`Project.Compiler.ArithmeticCompilerAudit` contained 133 Lean source modules:
73 Project, 43 LeanExe and 17 Interpreter. Recompute, do not hardcode these
counts. Resolve imports from these three source roots:

1. Repository root for LeanExe modules.
2. `proofs/talos/lean` for Project modules.
3. `proofs/talos/lean/.lake/packages/CodeLib/interpreter` for Interpreter modules.

Copy sources by module path into a new standalone directory. Parse imports
properly, including `public import` and multiple modules if present; fail on
unresolved nonstandard dependencies. The previous closure's external roots
were `Init.Data.ByteArray.Extra`, `Init.Data.ByteArray.Lemmas`,
`Init.Data.Nat.Lemmas`, `Init.Data.String.Basic`, `Init.Omega`, `Lean`,
`Lean.Data.Json.Printer`, `Mathlib.Tactic`, and `Mathlib.Tactic.Ring`. It required
neither the CodeLib library nor iris code. Check this again against final
sources rather than silently dropping an unfamiliar import. Include dependency
license/attribution material when redistributing the Interpreter sources.

Copy the exact `lean-toolchain` and `tools/leanrun`. A minimal standalone
`lakefile.toml` can use:

```toml
name = "ArithmeticCompilerProof"
version = "0.1.0"
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4"
rev = "85e3a25e006c35636f0e53b0e9296caca2685bc0"
[[lean_lib]]
name = "LeanExe"
[[lean_lib]]
name = "Interpreter"
[[lean_lib]]
name = "Project"
```

Derive its `lake-manifest.json` from the pinned proof manifest: set the package
name; retain pinned git dependencies except CodeLib/iris; remove path
dependencies; set mathlib `inherited` false and its `inputRev` to the exact
revision; keep other dependencies inherited and retain their exact revisions.
Verify the resulting closure rather than accepting extraneous path references.

Add `proof-package.json` with a versioned schema, exact audit target, pinned
toolchain/dependency identities, and SHA-256 hashes of all bundled source,
configuration, runner, verifier and README files. Verify paths stay within the
package, reject missing/changed/extra executable or source inputs, and reject
unknown schemas/targets/pins. The manifest is an integrity inventory, not an
authenticated signature; record the final archive hash outside the archive.

The verifier must first validate the manifest, then require the package's own
`.lake/build` to be absent, and run:

```bash
tools/leanrun --timeout 900 lake build Project.Compiler.ArithmeticCompilerAudit
```

Capture full output in `verification.log` and perform the same final theorem
axiom audit. Ordinary kernel reduction of compiler definitions inside proofs
is expected; invoking the CLI or a generator to produce missing proof sources
is prohibited in this gate. A package may use pinned third-party caches in an
external dependency directory; it must not load original-checkout LeanExe,
Project or Interpreter source/olean files. Prefer verification in an isolated
directory where the original checkout is not a source-search dependency.

Produce a source-only `.tar.gz` with no build/cache/log files. Extract that
archive into a second new directory and verify it there. Record archive SHA-256,
originating commit, exact verification command/environment, successful output,
and axiom audit. The earlier approximately 326 KiB draft archive is lost and
was never verified; no hash or result from it counts for this gate.

### Remaining gate 4: meaningful deliberate mutations

Implement a repeatable mutation driver in isolated checkouts/copies. Never
mutate the live baseline branch in place. Require each replacement to match
the intended production occurrence exactly once, verify a passing baseline,
invalidate/rebuild affected modules and dependents, and restore the baseline
between cases. A mutation is detected only when the intended semantic,
correspondence, validation or manifest check rejects it. Missing dependencies,
timeouts and incidental syntax errors are inconclusive. Save every log and
the exact mutation diff.

Candidate concrete mutations to implement and verify against current source:

| Boundary | Deliberate change | Expected rejecting check |
| --- | --- | --- |
| Source admission | Change a fresh accepted source declaration to contain a let, branch, helper call, or custom arithmetic instance. | Real arithmetic CLI rejects unsupported source; no output is reported certified. Existing admission regressions provide the source patterns. |
| Extractor operator | In `LeanExe/Extract/ScalarPrimitive.lean`, change production `toIR` case `\| .add => .add` to subtraction. | General `denote_toIR`/`lower_correct` proof fails when building that module. |
| IR literal | In `LeanExe/Extract/ScalarExpr.lean`, change the direct `UInt64.ofNat` literal branch from `some (.u64 n)` to `some (.u64 (n + 1))`. | General extraction preservation/literal proof fails. |
| Opcode | In `LeanExe/Wasm/Image/Emit.lean`, change `.addI64` byte 124 to 125. | Actual byte/instruction correspondence (`Project.Compiler.ArithmeticEncoding` or full audit dependency) fails. |
| Runtime call | In `LeanExe/Wasm/Binary.lean`, change `let callReleaseChild := localGet childLocal ++ call releaseIndex` to call `releaseIndex + 1`. | Runtime release validation or an earlier actual-byte correspondence proof fails; index 5 is invalid in the five-function arithmetic module. |
| Export | In production `exportSection`, change `exportEntry exportName 0 item.fst` to use `item.fst + 1`. | Actual export-section/full-module correctness proof fails. |
| Argument ABI | In `extractScalarFunc`, remove `.reverse` from `extractScalarExpr (List.range arity).reverse body` without changing its specification. | General source-application/function correctness proof fails; asymmetric real-engine fixture can also expose it. |
| Package manifest | Change audit target or pinned dependency, or alter a bundled source without updating its recorded checksum. | Standalone verifier rejects before Lean runs, for the intended target/pin/hash error. |

Also corrupt one expected native result or engine input to confirm the
comparison harness rejects a mismatch; label this a harness check, not a
compiler proof. Manifest mutations must distinguish content corruption from
authentication: an attacker replacing both sources and inventory requires the
externally recorded archive hash to detect substitution.

### Remaining gates 5 and 6: policy, documentation, final evidence

Run the existing independent policy gate serially:

```bash
tools/type-safety.js check
```

It builds `LeanExe.TypeSafety`, runs its existing behavioral regressions and
audits its theorem dependencies under the original **propext-only** whitelist.
It has not been run in this continuation. Do not weaken its policy to pass a
changed implementation. Its success does not replace the arithmetic theorem
or the arithmetic gates.

Update user-facing documentation with the exact source grammar, numeric limits,
CLI examples, actual theorem statements and locations, admitted/rejected
examples, independent engine/package procedures, trust boundary, and excluded
features. Make all drivers fail clearly on errors and document prerequisites
(Git, pinned Lean/Lake, Node supporting i64 BigInt WebAssembly, Python 3 for the
planned package tool, and tar/zstd for toolchain recovery).

For each final gate record the tested commit/tree, toolchain/compiler and Node
versions where relevant, exact command, exit status, meaningful result counts,
audit output, and durable log/artifact location. Preserve evidence in Git or
another explicitly selected durable destination before relying on it; local
scratch logs have already been lost twice. Do not check in dependency caches
or large build trees. Any fix after a passing gate requires rerunning the
affected gate on the final candidate; prior results may be retained as history.

Arithmetic completion requires all of: general acceptance/soundness and full
byte/export invocation theorem; strict usable admission; successful actual CLI
and 85 independent-engine comparisons; clean-checkout proof and executable
gates; isolated package verification with recorded archive hash; meaningful
mutation rejections; unchanged TypeSafety policy passing; accurate docs and
durable evidence; all final changes committed and pushed to `correct`.
Do not ask the user to supply semantic or correspondence proofs for their
programs. The theorem is already general; examples test integration, not its
mathematical quantification.

### Known proof/performance issues already resolved

`Project/Compiler/KernelReduction.lean` defines `kernel_rfl`. It constructs an
ordinary `Eq.refl` proof for the equality target's left side and assigns it;
the declaration kernel must check definitional equality with the claimed
right side. It does not use `native_decide`, a new axiom, or unchecked declaration
insertion. `test/negative/arithmetic_kernel.lean` attempts `0 = 1` and was
rejected by the kernel with a declaration type mismatch. Keep this negative
control as an expected failure, not in a positive-only regression list.

The three large actual runtime validators use `by kernel_rfl`; the reset
validator uses `rfl`. They checked in approximately 3.5–3.7 seconds each with
only `propext`. Earlier elaborator `rfl` hit 200000 heartbeats, and broad `simp`
timed out at 90 seconds. Do not repeat those unchanged experiments or raise
limits to hide the elaboration boundary. Runtime/metadata imports were narrowed
to actual module bytes plus the binary validator, avoiding an unnecessary
SourceInvocation dependency. Root `ArithmeticBounds` payload definitions are
shared by proof layout abbreviations; some simplification needs the explicit
root definitions. These fixes are already in checked commits.

The actual runtime indices are user 0, allocator 1, reset 2, retain 3,
release 4; the free export aliases release. All ten reserved runtime exports
must be excluded for the user entry; an earlier duplicate-export bug was fixed
and checked. Do not regress to checking only a subset of reserved names.

Useful checked commit anchors:

- `cb26c4948c17ce10c0c5807badba6cd4c821e0ba`: reserved runtime export fix/regression.
- `62cb863e3d105f98d11604925c1aed8682492929`: module metadata validation.
- `1464f53b1ae83843f4172df1eadba2dda6c7c0bb`: strict admission/format limits.
- `c9e71b6c955e246ccb7d27f97e5f98f6ddccdc50`: admission proofs and arithmetic CLI.
- `a465dbf9c6f2c8ba25840de50a6d26d31aa56a3b`: shared format payloads/import reduction.
- `9caa5a6c723bb064f326640589e85cb7bfc6698b`: all runtime validation and kernel negative control.
- `5dfcd8f5d42ab945258970f605c7f22e096fa7df`: final generic arithmetic compiler theorem and audit.

The reconstructed gate files were locally checkpointed as `5d55b78d` before
this handoff; the remote handoff commit includes them. Treat their verification
status as draft regardless of their presence in Git.

### Deferred full scalar agenda after arithmetic completion

The original agreed scope remains concrete Wasm scalar values: UInt64 inputs
and results, internal Bool, modular arithmetic, unsigned comparisons, bit
operations/masked shifts, strict bindings, branches, acyclic scalar helper
calls, and explicitly supported terminating structured iteration. Runtime Nat,
heap objects, imports, mutable globals and allocation remain excluded.
Proof-level Nat and explicit source termination arguments are permitted.
The user's priority is to finish arithmetic completely before extending it.

For each extension, first define independent source syntax, typing, semantics
and termination/ABI conditions; update executable admission with explicit
unsupported-form errors; prove extraction acceptance and preservation; prove
the actual IR/lowering/encoding/validation/invocation steps used; then extend
the one general compiler theorem. Maintain source-meaning independence and
the actual normal production compiler/emitter path throughout.

1. Strict scalar bindings: correct evaluation order, scope/local indices and
   result-slot preservation through extraction and stack/local lowering.
2. Bool, unsigned comparisons and branches: source condition semantics,
   branch-local typing, result joins and actual structured Wasm control flow.
3. Acyclic scalar helpers: independent declaration graph/support, successful
   extraction of all reachable helpers, call indices/signatures, argument and
   return ABI, module layout/exports, and terminating call semantics.
4. Supported structured loops: choose and state the exact source constructs
   and termination contract before admitting them; prove loop-state semantics,
   lowering, block/branch depths, validation and total execution from that
   contract. Do not replace this with arbitrary recursion or a per-program
   Wasm behavior proof. Existing type work may be modified where appropriate.
5. Reapply clean-checkout, independent-package, real CLI/engine, mutation,
   axiom, TypeSafety and documentation gates to the expanded scope. Keep
   arithmetic as a regression. Finish only when every admitted construct is
   covered and every required gate passes on the final committed version.

The broader completion checklist below remains open wherever its full-scalar
scope is unfinished, even when the arithmetic instance of that item is proved.
Do not report broader scalar compiler correctness from the arithmetic result.

---

## Correction and authorization

The prior completion reports were false. They covered a separate backend and
five manually supplied source/IR certificates. They did not establish a usable
certified Lean-source compiler. The user has explicitly instructed removal of
that implementation and completion of the actual job. Those changes are removed
from the working tree; Git history preserves what happened. Work remains on
`correct`, with the reviewed `typesafety` source restored from
834ba204d84720e00deef9b4ce476d4a04e55ff4. Main and typesafety are untouched.

Do not mark this agenda complete because examples or backend proofs pass.
Completion requires the source-declaration compiler interface below.

## Required result

Prove the actual compiler correct once for every program in a precisely defined
scalar source subset. The general theorem must connect the original checked Lean
source declaration, the actual extraction and lowering functions, and the exact
emitted WebAssembly bytes. It must quantify over every valid input. In addition
to preservation on successful compilations, prove compilation succeeds for the
defined supported subset. Define support from source syntax and types, not from
whether an output happens to satisfy correctness.

The executable must call the functions covered by these proofs. Source meaning
must be independent of compilation and connected to Lean's operations. Each new
supported program inherits correctness from the general compiler theorem. A
separate backend, a registry of examples, or individual generated correspondence
proofs does not fulfill this task. No handwritten IR or compiler-correctness
certificate is required from the user.

The profile uses concrete WASM values: UInt64 arguments/results, internal Bool,
modular arithmetic, unsigned comparisons, bit operations and masked shifts,
strict bindings, branches, acyclic scalar helper calls, and supported terminating
structured iteration. Division by zero returns zero and remainder by zero the
dividend. Runtime Nat, heap objects, imports, mutable globals, and allocation are
excluded. Proof-level Nat and explicit termination arguments are permitted.

## Immediate milestone: arithmetic expressions end to end

The user now explicitly prioritizes a totally complete arithmetic-expression
milestone before additional language features. Finish the current independently
specified UInt64 arithmetic-expression fragment through exact emitted bytes,
full decoded module, and exported invocation for every input. No extra
source/IR or byte-correspondence certificate may be required per program.
Do not extend source bindings, branches, helpers, or loops until this milestone
is proved, pushed, audited, and demonstrated on unregistered source functions.
The larger agenda below remains deferred, not reported complete.

The arithmetic milestone is complete only when all of these hold:

- [x] Production instruction bytes decode correctly, including div/rem guards.
- [x] The complete production module decodes and validates, including runtime
      bodies, function types, locals, exports, and all section lengths.
- [x] Export lookup and invocation initialize the ABI correctly, terminate,
      and return the original source's UInt64 result for every input.
- [x] One general theorem composes original source, actual compiler entry,
      exact emitted bytes, decoded module, and exported execution. Admission
      follows source syntax and explicit format limits, with no per-program
      correspondence certificates or assumed correctness of generated code.
- [x] An explicit compiler mode rejects unsupported and oversized source
      rather than presenting compilation outside the proved subset as covered.
      Admission and wiring are checked; the native CLI/engine gate is pending.
- [ ] Clean-checkout proof build, axiom audit, independent package verification,
      and fresh real-CLI/Wasm-engine examples and edge cases all pass.

## Completion gates for the full scalar agenda (arithmetic is the first milestone)

- [x] Read and identify the actual existing extraction, IR, lowering, and emission paths.
- [ ] Define independent scalar semantics and precise source/ABI/termination contracts.
- [ ] Implement source-only certified entry admission with explicit errors.
- [ ] Prove general original-Lean-source to actual extracted-IR semantic preservation.
- [ ] Prove extraction succeeds for the defined source subset.
- [ ] Prove every scalar lowering pass used by the accepted subset.
- [ ] Compose a general theorem for the actual compiler entry point and emitted bytes.
- [ ] Cover strict bindings, branching, numeric boundaries, and acyclic helper calls.
- [ ] Cover the agreed structured-loop/termination cases without per-program WASM proofs.
- [ ] Use actual compiler emission and prove full decoded-module equality for exact bytes.
- [ ] Produce portable proof packages independently checkable without compiler/generator execution.
- [ ] Compile and certify unseen source functions with no registration, handwritten IR, or correctness certificates.
- [ ] Check deliberate source/extractor/IR/opcode/call/export/ABI/manifest mutations.
- [ ] Audit final theorem dependencies: no holes, fresh axioms, or native-evaluation shortcuts.
- [ ] Preserve the independent TypeSafety propext-only policy.
- [ ] Pass a clean-checkout gate starting from source declarations and a separate package-only gate.
- [ ] Update documentation with actual scope, exact commands, limitations, and remaining obligations.

## Work policy

Commit and push frequently; explicitly announce every successful push. Keep Lean
processes serial under the pinned toolchain. The user explicitly authorized direct
local Lean execution; tools/leanrun with LEANRUN_LOCAL=1 retains locking and
bounded execution. Split a timed-out diagnostic before retrying it. Do not spawn
other agents without authorization. No status statement can exceed its evidence.

## Journal

### Restart

Inspected the real path: LeanExe.Extract.compileEnvironment uses the existing
extractor to produce LeanExe.IR.Module; LeanExe.Wasm.Binary.CoreWasm emits it.
ScalarDescriptor and ScalarCertificate already connect parts of actual lowering
to reusable descriptor code. The typesafety base also contains the Talos
ScalarTransition proof library. The previous separate Correct/Scalar64 path,
manual-certificate CLI, bundled pilot packages, and false completion report have
been removed. The required source-only frontend is currently UNIMPLEMENTED.

### Source traversal refactor (checked)

The previous task text still allowed individual proof-producing compilation as
the final result. Corrected it to the requested general compiler theorem and
added a separate acceptance theorem to rule out vacuous success-by-rejection.

The production source traversal used opaque partial definitions for application
decomposition, lambda collection, forall collection, application reconstruction,
and a fuel-bounded beta reducer. Moved the first four into Extract.Syntax as
total functions, with reconstruction and metadata invariance proofs; made the
existing beta reducer total on its fuel. This is source traversal infrastructure,
not a source-to-IR semantics proof. No end-to-end theorem exists yet.

Validation: `lake build LeanExe.Extract.Syntax LeanExe.Extract.Types` and
`lake build LeanExe.Extract.Core` passed through tools/leanrun. The application
spine reconstruction and metadata invariance proofs were checked by Lean.

### Native scalar operations (checked)

Added independent relational semantics over the existing IR for finite locals,
strict bindings, arithmetic, branches, and short-circuit conditions. Unsupported
operators and out-of-range locals have no evaluation rule. This semantics is not
the diagnostic partial evaluator. Calls and loops still need semantic rules.

Refactored the ten direct UInt64 primitive branches in the production extractor
to call ScalarPrimitive.lower. Proved ofName_sound, ofName_name, denote_toIR, and
lower_correct against Lean's native UInt64 operations and the IR relation for
arbitrary operands. The extractor rebuild passes. This proves the primitive
lowering step only, not the enclosing opaque recursive extractor or WebAssembly.

Identified that overloaded arithmetic dispatch ignores its typeclass evidence;
checking a concrete custom-instance counterexample before changing that boundary.

### Source instance dispatch regression (checked)

Reproduced a real mismatch through compileEnvironment: a custom HAdd UInt64
instance implementing subtraction evaluated to 7 on (10,3), while extracted IR
returned 13. Removed the bypass that skipped class-evidence normalization for
arithmetic projections. The same source now extracts subtraction and returns 7.
Made the existing fuel-bounded class normalizer total. Its semantic preservation
has not yet been proved.

Added test/scalar_class_evidence.lean: 48 source-versus-extracted-IR comparisons
cover custom HAdd/HSub/HMul/OfNat, standard arithmetic, bit operations, shifts,
and branching, including zero and overflow inputs. All passed via tools/leanrun.
These are regression checks, not a substitute for the general compiler theorem.

### Recursive primitive-expression extraction (checked)

Added an independent source relation over actual Lean.Expr syntax. Its primitive
constants are explicitly paired with their native Lean definitions, separately
from the compiler's operator table. Added total extractScalarExpr and wired it
into both production extractExprFrom and extractValueFrom for materialized
scalar slots.

Proved preservation for arbitrary expression trees and inputs; support implies
compilation success; compilation success implies syntactic support; and a
combined total-correctness theorem for this extraction fragment. No examples or
per-function proof certificates occur in these proofs. Current fragment: direct
UInt64 primitives, UInt64.ofNat literals, variables, and metadata. The actual
extractor rebuild and the 48 class-evidence regression checks pass.

These theorems do NOT cover complete declarations, overloaded-source
normalization, strict bindings, branches, helpers, loops, WASM lowering, or bytes.
The full agreed subset and source-to-bytes theorem remain incomplete. Auditing
current theorem dependencies in test/scalar_expr_axioms.lean.

### Canonical elaborated scalar expressions (checked)

Extended the same production traversal and general proofs to the canonical
HAdd/HSub/HMul/HDiv/HMod/HAnd/HOr/HXor/HShiftLeft/HShiftRight applications emitted
by Lean, including exact instance evidence, and canonical OfNat UInt64 literals.
Custom instances are excluded from this proved traversal and continue through
the existing evidence-normalizing path. A class recognizer soundness theorem
connects accepted heads to the independent native-operation source relation.

The 56 regression comparisons pass. They now also assert raw-source admission
before any normalization: ordinary arithmetic, affine arithmetic with literals,
bits, shifts, and a literal above 2^64 are accepted; custom instances and the
still-unproved branch fragment are excluded. The extractor rebuild passes.

Updated axiom audit: preservation/acceptance/combined extraction theorems now
use propext, Quot.sound, and Classical.choice; recognizer soundness uses propext
and Quot.sound. These are standard Lean axioms, with no sorryAx, fresh axioms,
or native-decide shortcut. The independent TypeSafety policy is unchanged.
Declaration application and source-to-bytes composition are still unproved.

### Production entry point to IR (checked)

Added scalar function application semantics over the original elaborated lambda
term, argument-order and finite-local-slot proofs, and scalar IR statement and
single-result function semantics. Proved extractScalarFunc_correct for every
successful declaration extraction and every argument list of the declared arity,
and extractScalarFunc_accepts for the independent source support predicate.

The normal compileEnvironmentWithEntryModeDetailed now handles the proved scalar
declaration case before the general opaque recursive extractor. It uses the same
IR and result-slot ABI and continues into the existing emitter. The generic
compileEnvironment_scalar_total_correct theorem references that actual entry
point, the original environment declaration/body, syntactic source support, and
all inputs. Its endpoint is IR.Func.ScalarEval. Native scalar constants have
explicit meanings in the independent source grammar; arbitrary Lean syntax is
not included. Existing unsafe/partial and reserved-export exclusions remain.

The proof and production extractor build pass. The 56 regression checks pass
through the changed entry point. This is NOT the end-to-end compiler theorem:
WASM lowering/encoding and the rest of the agreed language features remain open.

### Production emitter transparency (checked)

Made the existing expression/condition/local-let/statement scratch calculators
and annotated statement emitter total. The nested-list termination obligation
uses element membership and structural size; their equations and emitted code
were not replaced by a separate backend. Existing ScalarCertificate proofs pass.

Proved scalarFunc_emit for the normal emitFuncInstrs function: the exact emitted
instruction list is the recognized descriptor's code followed by the actual
result-slot store/load. Added descriptor scalar evaluation and operator meaning
lemmas as preparation for the IR-to-WASM semantic proof. The descriptor evaluator
alone is not a WebAssembly execution theorem. Talos semantics, scratch bounds,
module assembly, and exact binary correspondence still need to be connected.

### IR descriptor semantic preservation (checked)

Proved Expr.ofIR_eval and Cond.ofIR_eval for the existing descriptor recognizers.
Every recognized scalar IR evaluation has the same descriptor value and leaves
source locals unchanged. The proof covers arithmetic, branches, comparisons,
negation, and short-circuit conjunction/disjunction. Strict bindings cannot be
silently discarded: this pure recognizer rejects them. The proof is generic over
IR expressions, stores, and results and passes the kernel.

Next connection is to the existing Talos ScalarTransition program theorem via
an explicit interpretation of the production Instr syntax. That bridge is being
implemented in Project.Compiler.ScalarLowering; it is not yet an established
WebAssembly correctness result.

### Emitted instruction correspondence and control annotations (checked)

Added a total interpretation of the production structured instruction syntax
into Talos instructions. Proved expression_program and condition_program for
all existing scalar descriptors and scratch indices: the actual emitter's
instruction list interprets to the existing ScalarTransition program. This
includes division/remainder guards and short-circuit/conditional control.

Separately proved that changing static block/loop/if type annotations while
preserving arities and related bodies preserves Talos execution at every fuel,
and consequently its total-correctness WP. The proof was split after an initial
timeout; it now uses bounded interpreter unfolding and checks in seconds.

Both proof modules build. The interpreter translation currently omits static
type annotations to match ScalarTransition. Connecting it to the typed binary
decoder requires the proved annotation relation; that connection is still open.
Scratch-state correspondence, allocation bounds, module assembly, and byte
roundtrips remain open. These results do not establish source-to-bytes correctness.

### Scratch bounds and emitted expression execution (checked)

Proved correspondence between native scalar descriptor evaluation and Talos's
scratch-aware scalar evaluator. The theorem covers every expression/condition,
preserves all source slots, preserves local capacity, and establishes successful
evaluation whenever the descriptor scratch width fits. Native division and
remainder at zero and masked shifts are proved to agree with Talos operations.

Proved that the production exprScratch/condScratch calculations equal recognized
descriptor widths, and that funcScratch for scalar declarations supplies exactly
that width. Proved expression_execution: the actual emitted structured expression
instructions, interpreted in Talos, terminate with the source value and unchanged
source slots. Also proved the initial parameter/local ABI state representation.
All four new proof modules build. This execution theorem is for instructions;
encoded module bytes and whole exported-function invocation remain unconnected.

### Production source entry to complete function instructions (checked)

Proved that every successful production scalar expression extraction is accepted
by the existing backend descriptor recognizer. This is derived from source
syntax; backend acceptance is not an extra per-program obligation.

Added scalar_function_execution and extracted_function_execution, including
actual zero-initialized locals, the production scratch allocation, result-slot
store/load, and all source inputs. Composed compileEnvironment_instructions for
the actual normal compiler entry: independent source support implies successful
compilation and termination of the full emitted function instructions with the
original source value. Its scope is the arithmetic declaration fragment, and its
endpoint is Talos interpretation of structured instructions, not decoded bytes.

All new modules build. Project.Compiler.AxiomAudit reports only propext,
Classical.choice, and Quot.sound for the composed theorem and backend lemmas;
no sorryAx or fresh axioms. Remaining obligations include binary encoding and
full decoded-module equality, exported invocation, explicit admission errors,
strict bindings/branches/helpers/loops at source, and the final release gates.

### Unsigned production byte encoding (checked)

Proved that the shipped UInt64-based LEB encoder emits the independent Wasm
binary grammar's U32 encoding for every value below 2^32, and its U64 encoding
for every UInt64. The proof establishes length, continuation bits, final-byte
bounds, and decoded numeric value. It connects directly to Binary.u32leb.
Added the list-view equivalence needed for the actual ByteArray.toList calls.
The proof builds; signed constants and complete module encoding are next.

A first signed-bit helper attempted bv_decide and Lean exited with code 139.
That failed attempt is not committed or counted as evidence; replacing it with
explicit bitvector/arithmetic lemmas.

### Signed encoder bit operations (checked)

Replaced the crashing automated bitvector attempt with explicit kernel-checked
lemmas. Proved that the production sar7 implements signed arithmetic division by
128 on every UInt64 bit pattern, and that the low seven bits equal the signed
remainder modulo 128. The sign-fill proof handles every bit position explicitly.
SignedLebBits builds without bv_decide, native_decide, holes, or new axioms.
This is a checked part of signed-LEB correctness; the full signed encoding and
module-byte theorem remain unfinished.

The user reiterated frequent updates, commits, and pushes. Continue pushing each
checked increment, announce the pushed SHA immediately, and provide a progress
update at least every minute during ongoing work.

### Complete production signed LEB correctness (checked)

Proved the actual s64lebU64 encoder satisfies the independent binary grammar's
S64 relation for every UInt64 bit pattern, with exactly its two's-complement
signed value. The proof covers stopping conditions, final-byte bounds,
continuation form, at most ten bytes, and numeric reconstruction, and connects
the actual ByteArray output to the grammar. SignedLebStop, SignedLebTrace, and
SignedLeb all build. There are no per-constant certificates or finite test
assumptions. Next: instruction encoding, module assembly/decoding, and exported
execution for the arithmetic-only milestone.

### Arithmetic instruction binary grammar (checked)

Proved that the actual CoreWasm.encodeInstr/encodeInstrs output satisfies the
independent Wasm instruction grammar for scalar arithmetic instructions,
UInt64 constants, bounded local indices, and the structured i64 conditionals
used by division/remainder guards. The proof uses the production signed and
unsigned encoders and exact opcode bytes, including nested instruction lists.
ArithmeticEncoding builds. The relation still needs to be derived for every
admitted source expression and connected to the decoder and module theorem.

### Production integer and atomic-instruction decoder roundtrips (checked)

Proved parser composition with arbitrary prefixes, suffixes, and section limits.
Proved the existing decoder consumes production U32 and signed I64 encodings and
returns their exact values. Proved the same roundtrip for every arithmetic
opcode, literal, and bounded local read/write emitted by the actual instruction
encoder. Parsing, LebParsing, and ArithmeticParsing all build. Structured
conditionals, full functions/modules, and source-to-byte composition remain.

### Arithmetic admission and sequence-parser lemmas; workspace recovery

Proved that successful arithmetic extraction yields an arithmetic-only backend
descriptor, and that evaluation bounds all local reads. Added the peek-and-bind,
sequence terminator, sequence cons, and instruction-prefix lemmas. These files
passed Lean before workspace maintenance removed the checkout, installed
toolchain, and unpushed files. Restored the checkout from correct at a488bc3c
and reconstructed these exact changes from the session. A fresh rebuild after
recovery is pending while the pinned toolchain and dependencies are restored.
The structured instruction roundtrip was still being repaired and is not
counted as checked. The whole arithmetic milestone remains incomplete.

### Complete arithmetic instruction-sequence decoding (checked after recovery)

StructuredParsing now proves the actual decoder roundtrips production arithmetic
instruction sequences, including nested i64 conditionals and final terminators,
at arbitrary prefixes/suffixes and section limits. ArithmeticEmission derives
binary-grammar coverage for every arithmetic descriptor with bounded local
indices and sufficient scratch-index range; it requires no per-program
correspondence certificate. Parsing, SequenceParsing, StructuredParsing,
ArithmeticAdmission, and ArithmeticEmission passed the fresh restored build.
Container parsing/encoding and translation to execution are still being checked;
complete module decoding, validation, exported invocation, and final gates remain.

### Length-prefixed containers (checked)

ContainerEncoding identifies the production byte-vector, item-vector, and
section emitters with their exact list-of-bytes encodings. ContainerParsing
proves exact consumption for bounded parsers, sized payloads, and vectors,
including the decoder's remaining-input checks. Both modules build. These are
general module/body assembly lemmas, not yet a complete module theorem.

### Decoded arithmetic instructions to execution (checked)

ArithmeticTranslation proves raw decoded arithmetic syntax translates to the
previously proved executable program, including exact signed-constant bit
reconstruction and static control annotations. ArithmeticFunctionBytes composes
this with the actual function emitter and decoder: the complete emitted
instruction bytes decode to a program that executes with the arithmetic IR's
proved value. This theorem still assumes the existing IR evaluation premise;
the earlier general source-extraction theorem supplies it, but the composed
source-byte statement is not yet added. It does not cover the enclosing module
or exported invocation. Both new modules build. Narrowed the binary translator's
import to the interpreter syntax it uses; its implementation is unchanged.

### Original arithmetic source to exact function-body bytes (checked and audited)

FunctionParsing proves decoding of the actual emitFuncBody output, including
local declarations and the size prefix. SourceFunctionBytes composes original
source application, production extraction, actual encoding/decoding, and decoded
body execution for every input, subject to explicit local-count and body-size
format limits. There is no per-program semantic/correspondence hypothesis.
This is still a function-body theorem, not a whole-module/export theorem.
ArithmeticBytesAudit builds and reports only propext, Classical.choice, and
Quot.sound for the composed theorem and decoder lemmas; no sorryAx or new axioms.
Full module construction/validation, invocation, source admission limits, and
final clean-checkout/independent-package/runtime gates remain unfinished.

### Function signatures and UTF-8 names (checked)

HeaderParsing proves exact parsing of production byte vectors, arbitrary UTF-8
export names, repeated i64 parameter/result types, and complete function types,
subject to the relevant U32 length bounds. It connects String.fromUTF8? to the
original string and includes arbitrary byte prefixes, suffixes, and limits.
The module builds. Complete sections, fixed runtime bodies, validation, and
exported invocation still remain.

### Export, memory, and global entries (checked)

MetadataParsing proves exact production export-entry parsing, bounded function/
memory/global indices, minimum memory limits, mutable i64 global types, and
signed i64 global initializers. The module builds. These lemmas supply the
metadata payloads for the forthcoming complete module decoder theorem.

### Module header and section-loop composition (checked)

SectionParsing proves complete-input parser composition and section-loop steps,
including duplicate-section and order checks. ModuleParsing connects a completed
section stream to the actual module magic/version parser; ParsesEnd.runAll
connects that result to the public complete-input decoder. Both modules build.
Split the original module-header proof after an elaboration heartbeat limit;
explicit parser continuations now check without raising the limit. The exact
compiler module still needs its six concrete sections and fixed runtime bodies
instantiated, followed by validation and exported invocation.

### Fixed-runtime instruction forms (checked)

RuntimeAtoms proves roundtrip decoding for the additional indexed, memory,
global, call, branch, conversion, comparison, and signed -1 instructions used
by the production runtime. RuntimeStructure proves their structured-control byte
shapes and non-terminator opcode prefixes. Both modules build. The runtime's
nested instruction-sequence decoder proof and the four concrete runtime bodies
are still pending; arithmetic source support has not been expanded.

### Nested runtime instruction decoding (checked)

RuntimeParsing proves decoding for nested runtime instruction sequences,
including blocks, loops, empty-result conditionals with and without else arms,
and expression terminators. The proof uses the production instruction encoder
and the existing decoder with sufficient byte-derived fuel. The focused build
completed successfully. This is a general parser lemma, not yet its instantiation
for the four actual runtime bodies or a complete module theorem.

### Arithmetic milestone completion requirements (restated)

Completion requires the actual normal source compiler's emitted whole Wasm file
to decode, validate, and execute the requested export with the original source
result for every UInt64 argument list of the right arity. The accepted source
syntax and format limits must imply compilation success without per-program
semantic or compiler-correspondence certificates. A usable proved-subset mode
must reject unsupported source and exceeded bounds. Clean-checkout builds,
axiom inspection, independent portable-package verification, independent Wasm
engine edge cases, and the existing mutation gates remain required. Arithmetic
source-to-function-body bytes is checked; whole-module assembly, validation,
exported invocation, admission limits, and final gates remain incomplete.

### Actual fixed runtime instruction lists (checked)

RuntimeBodies constructs raw Wasm syntax together with the encoding-relation
proofs for the existing allocator, reset, retain, and release instruction lists.
The release function uses index four, as in an actual single-source-function
module. Each construction applies checked relation constructors to the real
runtime definition; no runtime code or compiler output is replaced. The module
builds, and RuntimeParsing therefore supplies instruction-expression decoding
for these exact lists. Local declarations and body size prefixes, complete
section assembly, module validation, and exported invocation remain to compose.

### Complete runtime body containers (checked, length bounds explicit)

RuntimeFunctionParsing composes the fixed runtime instruction proofs with actual
local declarations and the production body size-prefix encoder. Each of the
four body parsers is proved under its explicit U32 payload-length bound. The
module builds. These fixed bounds are being discharged using general encoder
length lemmas; complete section assembly, validation, and exported execution
remain unfinished.

### Runtime body decoding without assumed bounds (checked)

LebLengths proves the production signed and unsigned UInt64 encoders emit at
most ten bytes. RuntimeLengths bounds nested runtime instruction encodings and
discharges all four fixed payload limits. RuntimeFunctionParsing now proves
complete decoding of all four actual runtime bodies without length hypotheses.
All three modules build. This completes that component; complete module
sections, validation, exported invocation, and final gates remain pending.

### Whole six-section decoder composition (checked)

ModuleSections composes payload parsing into the public complete-input module
decoder for the exact six-section layout emitted by the production compiler.
It proves section order and uniqueness checks, exact module header consumption,
and sufficient section-loop fuel. The module builds. The remaining task at this
boundary is to supply the actual compiler payloads and their bounds; this general
composition theorem alone is not the source-to-module correctness result.

### Production vectors and fixed module payloads (checked)

ContainerEncoding now characterizes the native unsigned-vector emitter.
PayloadVectors proves production vectors decode from their entry proofs and
nonempty encodings, including arbitrary bounded U32 vectors. FixedPayloads
instantiates this for the actual five function-type indices, 16-page memory,
and six mutable i64 globals, and connects these payloads to the production
sections. All affected modules build. Variable signatures, exports, and user
code must still be assembled with these fixed payloads.

### All six concrete payload parsers (checked)

UserPayloads proves the actual variable function signatures and UTF-8 exports
decode correctly under their U32 bounds. CodePayloads assembles the actual user
body and all four proved runtime bodies into the production code vector.
FixedPayloadBounds discharges fixed function-index, memory, and global section
length bounds using general vector and constant-encoding length proofs. All
affected modules build. The exact moduleBytes composition theorem is now being
checked; validation and export invocation remain unfinished.

### Exact production module bytes decode (checked)

ArithmeticModuleBytes proves that the public decoder consumes the exact
CoreWasm.moduleBytes output for a single source function, including all runtime
functions and metadata. Its user-body parsing premise is the one established
by SourceFunctionBytes; its remaining format hypotheses are only parameter,
result, name, and variable section sizes. The module builds. Source composition
is next. This is not validation or export-invocation correctness.

### Original source to whole module bytes (checked and audited)

SourceModuleBytes composes successful production source extraction with exact
whole-module decoding and decoded user-body execution for every input. Parser
determinism fixes one decoded body; the universal execution proof is applied
to every argument list and every surrounding module/store. The theorem also
records the exact local declarations. ModuleBytesAudit reports only propext,
Classical.choice, and Quot.sound for the composed theorem, module decoder, and
runtime body proofs. Both modules build. Export lookup/calling convention,
module validation, normal-entry success composition, usable admission mode,
and final gates remain unfinished.

### Source-to-exported-invocation preservation (checked and audited)

ModuleInvocation proves lookup of the actual requested export, the translated
user function, argument reversal into interpreter stack order, exact local
initialization, and return-value extraction. SourceInvocation composes this
with exact module decoding and original source semantics: every argument list
of the correct arity terminates with the source value and preserves the store.
The explicit format bounds remain. Both modules build; the expanded audit
reports only propext, Classical.choice, and Quot.sound. This theorem does NOT
yet assert that the module passes validation. Full validation, normal compiler
entry success composition, the usable admission mode, and final gates remain.

### Compositional validation rules (checked); larger runtime checks pending

ValidationRules proves signed constant ranges, typed stack operations, and
validator sequence composition. TypedSequences derives typed encoding for
locals, constants, all ten arithmetic operations, equality, framing, and
concatenation. RuntimeValidation currently proves only reset. These modules
build. Direct reduction of retain/alloc/release hit the 200000-heartbeat limit;
a broad simplification attempt then reached the 90-second process timeout
without further diagnostics. Preserved that attempt in the scratch log area
and split the checked reset theorem from the unfinished larger proofs. The
next arithmetic validation step is the compiler-generated division/remainder
conditional, followed by the general expression theorem. No full-module
validation claim is made.

### General arithmetic validation induction (checked)

TypedConditionals proves the validator accepts the i64-result conditionals
used by division/remainder guards. ArithmeticTyping proves every admitted
arithmetic descriptor emits a sequence with the required stack type, under
its local-index and scratch-allocation bounds, for arbitrary nesting and all
ten operators. Both modules build. FunctionTyping and the source-to-function
validator composition are still being checked; no complete module-validation
claim follows yet.

### Actual source-produced user function validates (checked and audited)

FunctionTyping connects typed sequences to the existing complete function
validator, including actual i64 parameters/locals and result framing.
SourceFunctionValidation derives the typed sequence from production source
extraction and uses parser uniqueness to identify the actual decoded body.
Both modules build. ModuleBytesAudit reports only propext, Classical.choice,
and Quot.sound for extracted_function_valid. Larger runtime functions and
whole-module metadata validation remain. During export validation, found
reservedExportNames omits seven runtime exports; a regression and fix are next.

### Runtime export collision bug fixed and regression-tested

The production reserved-export list covered only memory/alloc/reset despite
emitting retain/release/free and four counter exports as well. A regression
against the actual compiler reproduced acceptance of RuntimeExportNames.retain
before the fix. Extended the list to all ten runtime exports. Rebuilt
LeanExe.Extract.Core and reran the regression successfully: every runtime name
is rejected for exported entries with the expected diagnostic, each remains
allowed for an internal function, and an ordinary arithmetic export compiles.
This fixes invalid duplicate-export modules and supplies the needed name
precondition for whole-module validation.

### Complete module metadata validation (checked)

MetadataValidation proves section ordering, the fixed memory limit and globals,
function type resolution, all eleven export indices, UTF-8 name agreement, and
export-name uniqueness for every source entry outside the runtime reserved list.
The module builds. This closes the metadata portion of validation; retain,
allocator, release, full validator composition, normal-entry composition,
usable arithmetic mode, and final gates remain unfinished.

### Execution blocked after metadata checkpoint (2026-09-25)

MetadataValidation completed successfully (3148 jobs) and was pushed at
62cb863e3d105f98d11604925c1aed8682492929. The subsequent bounded retain-validation
attempt used a restricted simp set, but the execution connection disconnected
before its result could be retrieved. New commands now fail with HTTP 409,
environment_offline: Environment is not connected. Resuming the existing process
also fails. This is not evidence that files were deleted or that the proof
passed. No retain validation result is claimed. The GitHub workflow-directory
lookup returned 404, so an existing CI runner was not available as a fallback.

Resume from the pushed metadata checkpoint, recover the retain attempt if it
remains on disk, and reduce its proof boundary before another long check. Finish
retain/allocator/release validation, compose full validation and the normal
compiler-entry theorem, implement the arithmetic admission mode, then run every
remaining clean-build, axiom, package, runtime, and mutation gate. The arithmetic
milestone remains INCOMPLETE.

### Workspace restored; arithmetic admission implementation being checked

After the execution outage, automated workspace maintenance removed the local
checkout files and toolchain. Restored `correct` from GitHub into a fresh local
checkout, restored pinned dependency revisions, and installed the exact pinned
Lean release. The production extractor and source-to-IR proofs rebuilt. The
first cache recovery reached its process limit after restoring part of the
cache; dependencies are being recovered in smaller steps.

Added reusable numeric arithmetic module size bounds and a strict arithmetic
entry that rejects excluded source forms, unsafe/partial entries, reserved
exports, and format overflows before invoking the existing normal compiler.
The two new production modules build. Admission regression checks, the CLI
wiring, and the proof connection are still being checked. No new end-to-end
correctness claim is made.

The arithmetic admission regression now passes. Supported expressions, bit
operations, and an overflowing literal produce byte-for-byte normal-compiler
output. Bindings, branches, helper calls, custom instances, non-UInt64 types,
reserved exports, and missing entries are rejected. An oversized parameter
count is rejected without constructing its type vector. These are executable
regression checks; the complete correctness theorem and CLI gate remain open.

### Arithmetic admission proofs and CLI wiring (checked)

ArithmeticCorrectness proves strict compilation accepts the independent source
subset whenever the explicit numeric format limits hold. It also proves every
successful strict compilation provides the original environment declaration,
safe/total flags, nonreserved export name, exact scalar extraction, and all
numeric bounds. ScalarEntryCorrectness now exposes the reusable connection
from successful extraction to the actual normal compiler. These modules build.
The CLI's compile-arithmetic command builds and calls this strict entry followed
by the unchanged production emitter. The actual CLI executable/engine gate and
full source-to-module theorem are still pending.

### Shared admission sizes connected to the checked byte layout

The production admission mode and the module-byte proofs now use the same type,
export, and code payload definitions for numeric size checks. The production
emitter is unchanged. Rebuilt exact whole-module decoding, fixed runtime-body
parsing, reset validation, and complete metadata validation successfully
(3110 jobs). Narrowed the runtime and metadata validation imports to the binary
layout and validator definitions they need. Retain/allocator/release validation
and the final composed theorem are still being checked.

### All actual runtime functions validate (checked and audited)

Retain, allocator, and release validation now pass Lean kernel checking in
3.5, 3.6, and 3.7 seconds respectively. Each theorem quantifies over the actual
surrounding arithmetic module and reports only propext in its dependencies.
Together with reset, all four fixed runtime bodies are covered.

KernelReduction constructs an ordinary Eq.refl proof term and leaves the
conversion check to declaration kernel checking, avoiding repeated expensive
elaborator normalization. It adds no axiom or native-evaluation oracle. A
negative control asserting Nat 0 = 1 was rejected by the kernel with a declaration
type mismatch. Full module-validation composition and the complete normal-entry
source-to-file theorem are being checked next; final gates remain open.

### Complete general compiler theorem (checked and audited; gates still open)

ModuleValidation composes source-function validation, all runtime functions, and
metadata into validateRaw for the exact decoded production module.
SourceCorrectness.extracted_correct combines this with exact byte decoding,
requested export lookup, argument/local ABI, and total source-equal execution
for every input, host, and store.

SourceCorrectness.compileEnvironment_correct proves independent source support
and explicit numeric format limits imply both normal and arithmetic-mode
compilation succeed with the same module and this full correctness property.
compileEnvironment_sound proves every successful arithmetic-mode compilation
has the property, with no caller-supplied semantic/correspondence premise.
All modules build (3166 jobs). The final compiler theorems report only propext,
Classical.choice, and Quot.sound; no holes, new axioms, or native-evaluation
certificates. This is the complete arithmetic compiler theorem. The milestone
remains INCOMPLETE until the actual CLI/independent-engine, standalone-package,
clean-checkout, mutation, and policy gates pass and documentation is finished.

### Second maintenance recovery; unfinished gates checkpointed

A later maintenance event again removed the restored checkout, installed Lean,
and local run logs. The complete general theorem and its audit remain pushed
at 5dfcd8f5. The previous automated proof gate and kernel-negative check passed,
but the CLI executable build was still in progress at the last observed log;
its eventual result is unavailable and is not counted as a passed gate.

Restored the gate driver, independent-engine comparator, and fresh Lean source
fixtures from the session. They are checkpointed before rerunning to avoid
another loss of unpushed gate work. Their reconstructed versions have not yet
passed the full run. Package verification, clean-checkout proof build, mutation
tests, and the independent type-safety policy gate also remain pending.


---

# Historical I/O parent task record

The following record is retained from the I/O parent. Its current-work language
and earlier pending items describe that parent session; the ciogpt agenda above
is authoritative for this combined branch. The iogpt merge results are recorded
in devnotes.md.

# Byte I/O completion

## Current state and scope

Updated 2026-09-24 after resuming on ARM macOS.  Branch `io` tracks `origin/io`; this session resumed from `4f3c3a394a8f13c4e897478b334c3cc9de16c989`.  Its implementation baseline is `fb19b5efdd6cc171033adf888667764203c14f14`, based on `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b` on `main`.  The resumed work repairs string-literal and nested-loop temporary ownership, adds regression and CLI checks, proves the modeled byte-I/O host and protocol behavior, refreshes the existing compiler proofs, and reconciles the documentation.  The user requested frequent commits and pushes as validation proceeds.

The current task is to complete primitive byte I/O, validate its shared compiler changes, and reconcile the documentation.  The user deferred release-identity work on 2026-09-24.  Release receipts, release-input digests, and cold release verification remain deferred.  The user included formal verification of the new byte-I/O host behavior on 2026-09-24.  Rechecking the existing Talos proofs is part of compiler validation.

This document owns the current continuation agenda.  The [Development Journal](devnotes.md#2026-09-23-byte-io-on-branch-io) preserves the implementation history and reported test evidence.  Its September 23 entry contains both intermediate and final results.  The current I/O count is 47 execution cases.  Counts of 26, 30, and 38 describe earlier revisions.

The resumed session has built the compiler and reproduced the focused execution checks.  Current results below distinguish fresh runs from earlier reports.  The non-release inventory has run, including a successful source/IR comparison rerun after a local-runner compatibility fix.  All 69 regenerated source caches match, and the complete current source-proof library passes for all 68 registered complete specifications.  Release identity remains deferred.

## Agreed behavior

The [Language Specification](docs/spec.md#byte-input-and-output) defines the public behavior.  The [Byte I/O API](LeanExe/ByteIO.lean) has these signatures:

```text
abbrev ByteIO (α : Type) := BaseIO α

read (maxBytes : Nat) (timeoutNs : UInt64) : ByteIO (Except UInt32 ByteArray)
write (bytes : ByteArray) (timeoutNs : UInt64) : ByteIO UInt32
```

| Operation or rule | Required behavior |
|-------------------|-------------------|
| Read | Return up to the positive capacity.  A short read succeeds.  Empty success means EOF.  Each returned byte array retains its contents across later reads. |
| Read capacity | Zero or a capacity outside the WASM address range returns error `28`.  Allocation exhaustion follows the runtime allocator's trap behavior. |
| Write | Return zero after writing every byte, or an error after possibly writing a prefix.  An empty write succeeds. |
| Errors | A read returns an explicit `Except`; a write returns an explicit status.  The caller handles propagation.  The previous session rejected an `EIO UInt32` and `try`/`catch` design. |
| Sequencing | Every sequenced action executes once, including an action whose result is ignored.  A `let`-bound action executes when sequenced, on each sequencing. |
| Timeout | A monotonic duration in nanoseconds covers the whole operation.  Partial writes and interrupted calls retain the original deadline.  Zero allows one immediate nonblocking attempt.  Deadline addition saturates on overflow. |
| Timeout result | Expiry returns `73`.  Clock and scheduling resolution affect observed completion time. |
| Other error codes | The backend uses WASI Preview 1 numbers, including `8` for a bad descriptor, `28` for invalid input, `29` for an I/O failure, and `64` for a broken pipe. |
| Command entry | `compile-wasi-io` accepts a zero-argument `ByteIO UInt32` entry.  Its result becomes the process exit status.  Reads use stdin and writes use stdout. |
| Source boundary | Ordinary supported data types remain available.  I/O actions cannot be stored in arrays or passed as runtime function arguments.  The two opaque primitives have compiler implementations.  Native Lean execution is unavailable. |

The existing pure WASI adapters remain available for bounded stdin, argv, stdout, and stderr around pure entry functions.  General file access, user-defined host calls, concurrency, direct clock access, and system-call protocols require separate design work.

## Implementation and host

### Source map

| Component | Source and responsibility |
|-----------|---------------------------|
| Public API and examples | [Byte I/O API](LeanExe/ByteIO.lean) and [Byte I/O examples](LeanExe/Examples/ByteIO.lean).  Examples include streaming, retained buffers, errors, and action sequencing. |
| Entry recognition | [Extraction types](LeanExe/Extract/Types.lean), [pattern handling](LeanExe/Extract/Patterns.lean), and [core extraction](LeanExe/Extract/Core.lean).  `ByteIOCompilation.compileEnvironment` checks the entry type. |
| Effects and pruning | [IR definitions](LeanExe/IR/Core.lean), [effect analysis](LeanExe/IR/Effects.lean), and [value extraction](LeanExe/Extract/Values.lean).  `LocalLet.effectCall` preserves sequenced calls and their arguments. |
| I/O program representation | [Byte I/O IR](LeanExe/IR/ByteIO.lean).  Read and write occupy external runtime function indices after the extracted functions. |
| Ownership and loop emission | [Core extraction](LeanExe/Extract/Core.lean), [value extraction](LeanExe/Extract/Values.lean), and [binary emission](LeanExe/Wasm/Binary.lean).  These changes also affect pure programs. |
| WASI runtime | [Byte I/O emitter](LeanExe/Wasm/ByteIO.lean).  It emits deadline handling, read/write loops, polling, error returns, allocation, and command startup. |
| Command dispatch | [Compiler CLI](LeanExe/CLI.lean).  `compile-wasi-io` uses the existing categorized error interface. |
| Integer encoding | [LEB encoding](LeanExe/Wasm/Leb.lean), [binary emission](LeanExe/Wasm/Binary.lean), and [image emission](LeanExe/Wasm/Image/Emit.lean).  `i32.const` uses signed LEB128 after truncation and sign extension. |
| Native test host | [WASI I/O host](tools/wasi-io-host.c) and [host builder](tools/build-wasi-io-host.sh). |
| Execution tests | [Host tests](test/wasi_io_host.js), [source I/O tests](test/byte_io.js), [reference-counting tests](test/refcount.js), and [self-emission tests](test/self_emit.js). |
| Test inventory | [Aggregate execution driver](test/run_all.js) and [development requirements](DEVELOPING.md#development-workflow). |

### Changes that need broad validation

Effect analysis now retains effects in unused results, loop bodies, call arguments, and branch conditions.  Saved actions remain unevaluated until sequenced.  Effect calls lower to ordinary WASM calls while retaining their ownership information.

`forInStepOwnedTemporaries` visits conditional branches.  `releaseForInStepTemporaries` clears temporary owner slots at each iteration before collecting and releasing the owners created on that iteration.  This prevents a skipped branch from reusing an earlier iteration's pointer.

Accumulator analysis tracks fresh, preserved, and null owners.  `emitAccumulatorReleases` compares an old owner with the initial and next accumulator owners before releasing it.  Initial owners are saved after all initial expressions have been evaluated.  Result cleanup also protects enclosing-scope owner slots, including when an error path returns the initial buffer.  These rules changed several shared fold and loop emitters.

The signed `i32.const` repair fixes a separate pre-existing encoder defect: unsigned LEB128 made address 64 decode as -64.  The tests cover 63/64, 127/128, 8191/8192, both signed endpoints, and truncation of high input bits.

### Host requirements

The generated module imports six functions from `wasi_snapshot_preview1`: `fd_read`, `fd_write`, `fd_fdstat_set_flags`, `clock_time_get`, `poll_oneoff`, and `proc_exit`.

The previous session found that the pinned Wasmtime 44 CLI rejects setting nonblocking flags on its standard streams with `BADF`.  The [pinned standard-stream implementation](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/wasi/src/p1.rs) is the recorded source for that behavior.  Polling followed by an unrestricted blocking write cannot enforce the requested write timeout.

The repository host uses the pinned Wasmtime engine and implements the required WASI calls over native nonblocking stdin/stdout.  Its supported subset accepts one iovec and at most two poll subscriptions.  It preserves descriptor flags on exit.  Its tests use native pipes and a five-second watchdog for each child.  Timeout behavior requires this host or another host satisfying the same requirements.

The [WebAssembly integer encoding specification](https://webassembly.github.io/spec/core/binary/values.html#integers) is the recorded reference for the signed-constant repair.  Repository requirements and operating instructions are in [Developing LeanExe](DEVELOPING.md).

## Evidence and unresolved defects

### Recorded results

These are results reported by the previous session in the development journal.  They require reproduction on the current checkout.  Earlier encoding, host, and WAT checks also precede the final ownership audit.

| Check | Reported result | Scope |
|-------|-----------------|-------|
| Byte I/O source tests | 38 execution cases passed, plus four pure-mode rejection checks. | Binary bytes, EOF, short reads, sequencing, saved actions, helpers, invalid capacity, zero and saturated timeouts, delayed input, partial writes, blocked/broken output, and cleanup. |
| Sustained streaming | Copied 4 MiB plus 137 bytes with 4,096-byte reads. | Compared the complete output and checked allocation/free counts between iterations and after return. |
| Retained buffers | Passed skipped-iteration, timeout, and output-error cases. | Exercises preservation of the initial and previous read buffers. |
| WASI host tests | Seven cases passed. | Nonblocking readiness, EOF, bounds errors, clock expiry, binary transfer, EOF polling, and blocked output. |
| Reference counting | 41 cases passed after the final accumulator and enclosing-scope changes. | Existing allocation and ownership behavior. |
| Signed-constant checks | Boundary checks and all 75 self-emitted LEB128 cases passed. | Native and image encoders. |
| WAT/binary agreement | Thirteen cases passed during the earlier audit. | Pure compiler serialization.  The current check uses `compile` and `compile-wat`. |
| Aggregate execution | Stopped at a release-input identity mismatch. | Later constituent tests still require a complete run.  Release identity is deferred by the user. |
| Core correctness | `arraySetIfInBoundsSkipsValueTrap` trapped. | The same failure and identical binary occurred on the branch base. |
| Documentation | Reported an absolute temporary-workspace path in the WGSL review document. | Existing documentation defect. |
| Talos | Stopped during the initial Mathlib cache download after 867 of 8,747 files. | Proof checks had not begun. |

### Current ownership results

The reported `arraySetIfInBoundsSkipsValueTrap` failure does not reproduce on the resumed branch: it returns `7` with one allocation and one free.  The generated binary has SHA-256 `c732ee7c5cb2f589e6f0beeda196f4b894dc29954ee95ed8229fbe0d3a76f65e`, different from the earlier failing binary.  Its IR guards the conditional result release against enclosing owners.  This guard was added in `cd20f9cf`.  The related out-of-bounds `Array.modify` case also returns `7` with balanced allocation counts.  Both now have explicit allocation assertions in the reference-counting suite; no additional alias-rule repair was needed.

The literal leak reproduced: `"ABC".toUTF8.size` returned `3` but allocated five blocks and freed two.  A byte-I/O helper writing the literal also left allocations live after returning.  The new regression tests failed before the repair.  Literal extraction now uses one `arrayLiteralSlots` backing array, replacing nested copying updates whose intermediate arrays had no cleanup binding.  Tests cover scalar use, returned bytes, string constants and concatenation, repeated sequenced writes, and broken-output cleanup.

Fresh checks passed: 7 native host cases; 40 byte-I/O runs and four pure-mode rejections; 48 reference-counting cases; 812 accepted, 48 rejected, and 14 expected-trap core cases; 70 byte-array allocation cases; 75 self-emitted LEB128 cases; and all 13 WAT/binary comparisons.  Session logs and the pre-fix failures are retained in the task workspace's `work` directory.  The initial pure-WASI adapter run failed because Wasmtime tried to create its default cache outside the sandbox; a wrapper now selects a workspace-local cache for reruns.

The nested-loop review found a second leak: an inner loop's final fresh
buffer was missed because its result could also alias the borrowed initial
buffer.  Step cleanup now tracks that result with guards for initial owners
and enclosing results.  New cases cover normal output, EOF, zero iterations,
timeout before and after replacement, and broken output.  All 47 I/O cases,
four pure-mode rejections, and 48 reference-counting cases pass.  The core
suite also passed after the initial repair; final compiler proof validation
continues below.

### Documentation and diagnostics

The [user manual](docs/manual.md#byte-input-and-output), [overview](README.md), [compiler guide](docs/compiler.md), and [development instructions](DEVELOPING.md) now describe byte I/O, the nonblocking host, diagnostic scope, and current accumulator cleanup.  The CLI error suite passes 15 cases plus help output, including byte-I/O command shape, pure/IO/parameterized entry rejection, missing entry, and output-file failures.  All 28 ownership-report cases pass after updating three stale statement-release counts from two to three; the reports now include the guarded final loop-result owner release.  CLI and standard-comparison checks exclude only exact local-runner notices from compiler/program stderr, preserving unknown failures and other output.  Runtime reporting and WAT commands retain their existing pure-entry scope.

The documentation checker now passes all 162 maintained Markdown files after removing the obsolete temporary checkout path from the WGSL review notes.  Root `task.md` and `devnotes.md` remain outside that checker's inventory and require separate review.

The follow-up review's two P2 native-host findings are repaired. Shared stdin/stdout flags are captured before either stream changes, and the host uses Cranelift with NaN canonicalization. The host suite passes seven I/O cases and twelve shared-descriptor restorations; source tests pass 53 executions, including six binary32/binary64 NaN cases, and four pure-mode rejections. Both regressions failed before their fixes. The byte-I/O proof gate passes again with identical echo bytes and 46 standard-axiom audits. The P3 manual finding is resolved by linking the modeled-host and exact-binary proof boundary while retaining its native-host assumptions.

## Talos relationship and proof scope

Talos supplies the WebAssembly semantics used by the Lean proofs.  LeanExe emits a module, the source-driven proof tools regenerate its Talos representation, and the Lean kernel checks the behavioral theorem.  The exact-binary path additionally proves decoding, validation, and translation of the embedded binary.  The [Talos Proofs guide](proofs/talos/README.md), [verification procedure](docs/verifying.md), and [artifact format](docs/artifact-format.md) define those paths.

### Existing compiler proof checks

The immediate obligation is to recheck existing programs after the shared extraction, ownership, loop-emission, and integer-encoding changes.  A source-driven check compares a regenerated candidate with the tracked `Program.lean`, then checks the registered specification.  A changed instruction stream requires review of the new proof subject and any affected proof.

`tools/talos-proof.js check --all` is the aggregate source-driven check.  `tools/talos-artifact.js prepare <case>` explicitly refreshes a generated cache.  Handwritten edits to `Program.lean` are prohibited.  Frozen exact-artifact packages retain their own bytes and identity; any deliberate replacement requires artifact and proof review.

`tools/talos-proof.js check --all` passes on 2026-09-24: all 69 regenerated caches match, registry/import checks pass, and the complete library builds for all 68 registered complete specifications. The retained partial sequence-softmax proof also passes separately; the full sequence registration remains incomplete as before. The completed source gate covers the compiler ownership changes, including current GCD, CLOB, Euler, cached GPT-2, LEB, and tiny-model instruction streams. Public model input ranges and numerical contracts are preserved. The LEB encoder returns an existential root because buffers can be reused, with explicitly typed runtime release-counter slots. No new axiom or admitted proof term was introduced. Evidence is recorded in the journal; frozen release identity remains deferred.

### Completed non-release execution inventory on this Mac

The non-release inventory passes the runner, artifact identity/conformance/migration unit checks, proof-tool unit checks, classification, floating-point, packed-data, Euler/WASM, matched-value, ASCII, integer-map, JSON, WASI adapter, and fuzz suites.  Standard comparisons pass all 340 native Lean/Wasm cases and 62 IR interpreter cases, including the string-constant byte result affected by this repair.  The pure-WASI rerun passes 33 execution cases, two traps, nine rejections, and 16 compiles with the local cache; fuzz validation passes 56 cases.

The C comparison now passes with `CC=/opt/homebrew/bin/gcc-15 node test/euler_rusanov_c.js`.  The driver accepts GCC's documented `__GCC_IEC_559 >= 2` advertisement while preserving all runtime format, evaluation-width, layout, rounding, strict-flag, and exact-word checks.  All eight mirror rows and seven Lanyon rows match the pinned CSV, whose bytes are unchanged.  The regression manifest records updated local source identities; vendored upstream source and frozen artifacts are unchanged.  The default Mac Clang still lacks the required advertisement, so the C comparison uses the explicit `CC` override.

### Formal I/O proofs: included in completion

The separate [byte-I/O proof gate](proofs/byte-io/README.md) now specifies all six generated WASI imports using pinned Talos `HostFn`, relational contracts, and `HostEnv.Satisfies`. It proves read/write prefix effects, EOF, bounded memory changes, preservation of other store resources, nonblocking flags, monotonic clock observations, canonical two-subscription polling, and exit status. Protocol theorems preserve byte order and the original saturated deadline, characterize successful complete output, and prove termination under explicit retry-clock progress.

A separate import-bearing binary profile proves decoding, validation, and translation without changing the existing import-free profile or frozen packages. The representative 2,082-byte echo binary has SHA-256 `a4eef742abcf9f01336de122839ebbc9db18a469a70d9ee11ac7586ac4615be5`. Six kernel-checked execution theorems cover partial writes, EOF, a committed prefix before a broken pipe, retry after readiness, absolute-deadline expiry, and the exported `_start` exit. Memory ownership checks include balanced allocation/free counts. The complete maintained gate compares the bytes with fresh compiler output and audits the public theorem axioms.

These are modeled-host and concrete generated-program theorems. They are not a universal compiler-refinement proof for every I/O program. Native C, Wasmtime, and the OS remain outside the proof boundary. A final nonblocking syscall may finish after the last clock observation; no strict wall-clock return guarantee is asserted. Release identity remains deferred. Existing compiler source-proof validation is complete.

## Environment and commands

### Current checkout

The user authorized local Lean execution on this Mac.  `tools/macos-env.sh` selects the repository's Darwin runner and pinned tools.  Existing tool installations are linked into ignored `build/tools`; the pinned proof packages were copied into this checkout using APFS file clones, so proof builds cannot modify the earlier checkout's dependencies.

| Requirement | Current selection |
|-------------|-------------------|
| Lean and Lake | `leanprover/lean4:v4.34.0-rc2`, required commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.  Compiler and fixtures built successfully. |
| Talos | Materialized CodeLib revision `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`, matching the proof manifest. |
| Node | `24.13.0`; version check passed. |
| Wasmtime | Pinned `44.0.0` CLI and C API.  Both native hosts compiled here. |
| wasm-tools | `1.251.0`; version check passed. |
| Runner | ARM macOS local mode, shared lock, one Lean thread, timeout, and the repository's authorized inherited-priority fallback.  No Linux cgroups or ionice. |

`WASMTIME`, `WASMTIME_C_API`, `WASM_TOOLS`, `LEAN_WASM_EXE`, and `LEANEXE_WASI_IO_HOST` select external or built tools.  For this checkout, sourcing `../work/io-env.sh` selects the session overrides.  Reruns use the pinned Wasmtime CLI through a wrapper supplying `-C cache-config` with a writable directory under `build/cache/wasmtime`.  All Lean processes still use `tools/leanrun` serially.  No dependency versions changed.

### Execution rules

Read [Repository Instructions](AGENTS.md) and [Developing LeanExe](DEVELOPING.md) before running Lean, and use the repository runner.  The `leanrunner` skill referenced by the earlier handoff is not installed in this session.  Every direct Lean, Lake, or compiler invocation goes through `tools/leanrun`.  Standard mode enforces the shared machine-wide lock, one Lean thread, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, nice priority 10, and idle I/O priority.  Lean jobs run serially.

Use bounded command and lock waits.  A target that times out without a diagnostic requires a smaller elaboration boundary or a checked supporting lemma before another attempt.  If the required user scope or cgroup limits fail, follow the repository's approval rule.  The user explicitly authorized local Lean execution for this resumed Mac session.  `LEANRUN_LOCAL=1` is selected through the repository's macOS environment script.

The Node drivers use [the process runner](tools/run-process.js), which sends their Lean children through `tools/leanrun`.  Invoke those drivers directly.  In authorized local mode, place the variable on the driver.  Nesting runners would reacquire the same lock.

### Focused commands after setup

The initial build supplies the compiler and fixtures needed by the focused tests:

```sh
tools/leanrun --timeout 15m --lock-timeout 60 lake build lean-wasm LeanExe.Examples.ByteIO LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms LeanExe.Wasm.ImageIntegrationTest
node test/wasi_io_host.js
node test/byte_io.js
node test/refcount.js
node test/self_emit.js
tools/check-wat.sh
```

Run each command serially and record its result.  The I/O test drivers build their host.  The source I/O driver also builds its source module and compiler, compiles each fixture, and runs `wasm-tools validate` on each artifact.  The reference-counting tests use the ordinary Wasmtime host.

The documented echo example, after the build and host setup above, is:

```sh
tools/leanrun --timeout 2m --lock-timeout 60 .lake/build/bin/lean-wasm compile-wasi-io --module LeanExe.Examples.ByteIO --entry LeanExe.Examples.ByteIO.echo --out build/echo.wasm
printf 'abcd' | build/tools/leanexe-wasi-io-host build/echo.wasm
```

The compiler supports `report`, `dump-ir`, `ownership-report`, and `compile-wat` for their documented modes.  Establish each diagnostic's support for the entry under investigation.  The present `compile-wat` command follows pure compilation and rejects the effectful echo fixture.  `wasm-tools print` can inspect the compiled I/O binary.

### Broader checks

Use the [aggregate execution driver](test/run_all.js) as the inventory of required builds and tests.  It currently runs release checks before the compiler and runtime suites and has no selection option.  With release work deferred, invoke the remaining constituent checks directly in their required order and record coverage.  Report the constituent results and the aggregate's deferred status.  A change to test selection in the maintained driver is a separate implementation decision.

The affected areas include core correctness, ownership reporting, reference counting, byte-array allocation, existing WASI adapters, CLI errors, source/IR comparisons, and compiler serialization.  Complete the broader inventory after focused repairs pass.  Preserve failures and compare inherited behavior with the base revision.

```sh
tools/talos-proof.js check --all
git diff --check
tools/check-docs.js
```

Keep each repository verification tool as the first command token.  Use the checked case configuration, ordinary path arguments, and tool-prefix approvals.  Frozen artifact changes also require the focused artifact check and `tools/artifact-proof.js check-all` under the repository's development rules.  Release-identity checks remain deferred.

The current documentation checker omits root `task.md` and `devnotes.md` from its file inventory.  Review their local links and examples in addition to running that checker.  The commands above have been reviewed against the scripts.  Execution results belong in the journal when they are run.

## Completion agenda

The proposed order below preserves the scope discussed in this session.  Implementation choices that change the API, host model, supported diagnostics, proof scope, or dependencies require confirmation.

- [x] Establish the pinned local tools and authorized runner mode, then reproduce the focused I/O, host, ownership, and encoding results.
- [x] Check both reported ownership defects: preserve passing array-alias regressions and repair the reproduced string-literal leak with failing-before/passing-after tests.
- [x] Review shared ownership and effect rules across retained buffers, conditional replacements, nested loops, helper calls, ignored results, and early returns.  Repair the newly reproduced nested-loop final-buffer leak and pass 47 I/O cases, four pure rejections, and 48 reference-counting cases.
- [x] Resolve the C comparison portability gate.  Every non-release execution suite and all 13 WAT/binary checks pass.
- [x] Complete existing Talos source-driven checks, diagnose inherited failures against the base, and review every changed generated program before updating its cache or proof.
- [x] Reconcile the overview, manual, specification, compiler documentation, and development instructions.  Test the new CLI's required error behavior.
- [x] Record the resumed revision, local changes, per-command results, remaining failures, and agreed exclusions in this document and the journal.
- [x] Include formal byte-I/O host proofs, as requested by the user.
- [x] Prove the modeled host contracts and byte-transfer protocol, connect representative generated WASM to Talos execution, and record assumptions and axiom audits. The maintained gate passes all 46 public-theorem audits.

The current implementation task is complete: I/O behavior and the included ownership defects pass their execution checks, compiler source-proof validation passes, modeled byte-I/O host and protocol proofs are checked, and the documentation records their assumptions. The execution aggregate itself remains deferred because it includes release checks; all non-release execution constituents passed separately. Release identity remains deferred.

## Maintenance

After each work session, update the implementation revision, current environment observations, evidence table, next unchecked tasks, and open decisions.  Record new tests with their command, revision, result, and retained evidence path when available.  Move detailed investigation history into the development journal and keep this document focused on the current state.  The previous journal records a request for frequent commits and pushes.  Preserve reviewable changes and record the branch state when publishing authorized work.

---

# Imported drone task record — completed separately

# Drone/main integration

This branch combines the drone development record and the completed main-branch
compiler integration record. Both are preserved below; their dated validation
results describe their original revisions. Merge validation is recorded in
`devnotes.md`.

The merged compiler produces a 14,174-byte drone binary with SHA-256
`33a4f94d391edb0ef3423be32fabde4596f36c711bc9639a21a49b223ca5ef46`.
The regenerated model and updated scalar/initial-row adapters pass the fresh
artifact gate and the 3,712-job specification build. Both `compute_correct`
and `compute_safe` retain their statements and use only standard Lean axioms.
The source audit, annotation regression, 52 independent planner cases, and
12 native Lean/WASM comparisons pass. The local case-registry edit remains
unstaged; aggregate registration is separate from these focused checks.
All 13 WAT/binary comparisons and the documentation gate pass. The full Node
suite stops at main's inherited verifier-digest mismatch; the source aggregate
stops at the local registry/import mismatch. Details are in `devnotes.md`.

# Drone controller and correctness proofs

This file is the development handoff and progress log for the `drone` branch.
Update it at each meaningful proof checkpoint, then commit and push the Lean
changes and this file. The user explicitly requested frequent updates, commits
and pushes during proof development. Do not commit graphs, HTML notebooks,
binaries, downloaded toolchains, or generated build files.

## Goal and current boundary

Implement a toy terrain-following point-mass autopilot in LeanExe, compile and
run it, illustrate several terrains, and develop formal correctness proofs.
The input is an integer array of terrain elevations. The output is an integer
array `[alt0, speed0, alt1, speed1, ...]`. Minimize traversal time under simple
maneuverability constraints while maintaining a clearance corridor and beginning
and ending on the terrain. No motor, propeller, battery, attitude, drag, lift,
or detailed aerodynamic model is wanted.

Both proof milestones are complete. `WholeFlight.compute_safe` proves source
whole-flight safety for the current point-mass model. `Spec.compute_correct`
now proves terminating compiled WASM execution with exactly the source output,
and `Spec.compute_safe` transfers whole-flight safety to that result. The
3,712-job specification build and fresh artifact/proof check pass with only
standard Lean axioms. Expansion of the model follows discussion with the user.
The user declined reproducible-artifact packaging as a task priority. Keep the
current Lean-code-and-task-only commit scope.

`Output.compute_correct` proves that every nonempty accepted terrain produces
exactly 2n words encoding a feasible route, and that its exact tick/excess cost is globally minimal in
the finite graph. Separate corollaries prove on-ground stopped endpoints and
empty/rejected-input behavior. The forward/history and reconstruction helpers
are connected to the actual public entry. Checked segment theorems establish
continuous clearance, component kinematic bounds, physical-time derivatives,
exact tick timing and bounded word arithmetic. `Safety.lean` now exposes
those continuous guarantees directly for every segment of the returned output.
`Trajectory.compute_global_smooth` now assembles the actual output into a
global real-time path and proves its position derivative and continuous velocity,
including joins.  The cumulative-time intervals cover the entire flight and
agree with their local primitives.  Clearance and component speed bounds
transfer to the global coordinate functions. `WholeFlight.compute_safe` now
packages spatial clearance, speed, global velocity derivatives and acceleration
bounds, continuity, stopped ground endpoints, and the singleton case. The
compiled execution theorem now covers allocation, copying, release, all loops,
reversal, and accepted/empty/rejected input dispatch. It assumes a valid caller
heap, a borrowed input array, and sufficient allocation headroom within 64 MiB.

## Safety status and remaining risks

### Current coverage and evidence

Resumed from `b5066cd49fd1a26ecb1dc8fbc63ac923b91128ae` on 2026-09-25 in
`/home/somebody/src/leanexe`. The existing aggregate source baseline passed
(1,998 jobs). The new whole-flight theorem and expanded aggregate check also
passed (2,001 jobs), with only `propext`, `Classical.choice`, and `Quot.sound` in
the axiom audit. A fresh native run reproduced the five-point example below.
Artifact preparation now reproduces the recorded 14,198-byte WASM, and fresh
runtime checks pass for 48 accepted flights, four empty/rejected inputs, and
12 native/WASM comparisons. Scalar helpers, the square-root loop, checked
terrain reads, and height validation also have checked execution lemmas.
The complete segment-cost, packed predecessor, predecessor-scan, and
best-predecessor functions also agree with their source definitions. The final
compiled specification passed on 2026-09-26 (`drone-spec-4.log`, 3,712 jobs),
including standard-only axiom audits for `Spec.compute_correct` and
`Spec.compute_safe`. `drone-artifact-check-final.log` records fresh compiler and
verifier builds, generated-program equality checks, and the specification build.
The WASM remains 14,198 bytes with SHA256
`0c24d2c1568ca40321421d19387843d4ee81c970d53e75adcb035b32343c0942`.

| Property | Current proof coverage |
|---|---|
| Clearance | `WholeFlight.compute_throughout` proves `Corridor.height terrain (globalX terrain t) ≤ globalZ terrain t` for every time in the finite flight. `Corridor.height_on_segment` identifies the spatial interpolation of `floorAt`, retaining 100-unit interior clearance and the specified takeoff/landing ramps. |
| Speed | `WholeFlight.compute_throughout` bounds horizontal speed between 0 and 20 and vertical speed magnitude by 20 at every time in the finite flight. |
| Acceleration | `WholeFlight.compute_acceleration_away_from_joins` proves that derivatives of the actual global velocities exist with magnitudes at most 1 horizontally and 4 vertically at every flight time outside the finite set of waypoint times. `Trajectory.compute_global_acceleration_within` supplies bounded one-sided derivatives on each closed segment, including both endpoints. |
| Continuity | `Trajectory.compute_joins` and `compute_global_smooth` establish matching positions and velocities and continuous global velocity.  Acceleration may jump at joins. |
| Interval coverage | `WholeFlight.compute_normalized_cover` transfers the segment results to every physical flight time. `compute_singleton` gives zero duration and a constant stopped ground path for one-point terrain. |
| Endpoints | `WholeFlight.compute_global_endpoints` proves the global path starts at horizontal position 0 and finishes at `100*(terrain.size-1)`, on the corresponding ground heights with both velocity components zero. |
| Feasibility and input handling | `Output.compute_correct` returns an encoded feasible route for every accepted nonempty terrain, with exactly two words per point.  Separate theorems cover empty and rejected inputs. |

Fresh runtime tests cover 48 accepted WASM trajectories and four empty/rejected
inputs against an independent finite-graph planner, plus 12 native comparisons.
The earlier six exhaustive short-route optima and separate translation checks
remain historical evidence. Drivers and logs are excluded from commits under
the existing scope. The source proofs quantify over all accepted inputs within
the stated bounds, and `Spec.compute_correct` now establishes the full compiled
entry theorem, including empty and rejected inputs under its memory preconditions.

### Remaining risks

Source composition is checked in `WholeFlight.Safe` and
`WholeFlight.compute_safe`. The theorem assumes precisely `terrainBound terrain`
and a nonempty terrain. Acceleration bounds apply to ordinary derivatives
between joins and derivatives within each adjacent closed interval at a join;
the two one-sided accelerations need not agree.

Executable correctness is now checked for the generated WASM semantics.
`Spec.ExactSpecFor` requires a valid caller heap, a borrowed input layout,
and 37,580,992 bytes of allocation headroom within a 1,024-page (64 MiB)
memory limit. The conservative budget counts allocations even when the free
list can reuse storage. The result contains exactly `compute terrain`, the
terrain remains unchanged, and memory stays within the limit. The theorem
does not verify the external Wasmtime host, the machine implementation of the
WASM runtime, or physical execution of the generated trajectory.

Model assumptions: safety assumes exact piecewise-linear terrain and exact
execution of the prescribed motion with independent horizontal and vertical
acceleration.  Terrain uncertainty, tracking error, disturbances, and coupled
actuator limits require additional assumptions and proofs before those effects
enter the safety claim.  The current model permits acceleration jumps at
waypoints.  Safety applies on the finite flight interval.  The formal global
curve extends the final polynomial after arrival.

## Repository and execution environment

The current workspace has the pinned Lean release under
`build/tools/lean-4.34.0-rc2-linux`, and the proof dependencies are materialized
at the committed revisions. The user authorized local Lean execution in this
workspace. Set `LEANRUN_LOCAL=1` and `LEANRUN_TOOLCHAIN` to that directory when
using the commands below. The runner still enforces its shared lock, timeout,
single Lean thread, nice and ionice settings. The earlier machine-specific
settings below are preserved as historical context.

- Upstream: https://github.com/jsmorph/leanexe
- Initial inspection: `main` at `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`.
- Development branch: `drone`. Keep further proof work on this branch.
- Lean: pinned 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Talos/CodeLib: pinned `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.
- Mathlib: pinned `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Wasmtime: 44.0.0; wasm-tools: 1.251.0.
- The original workspace used Node 24.19.0; the full repository suite pins 24.13.0.
- Read and follow `AGENTS.md`. Every Lean, Lake and compiler invocation must go
  through `tools/leanrun`; never run them concurrently. Use bounded commands.
- The user authorized `LEANRUN_LOCAL=1` in the original workspace.  That
  authorization was specific to that environment.  Follow `AGENTS.md` for
  execution in the current checkout.
- Original local toolchain:
  `/workspace/scratch/56b924f3bc36/leanexe/build/tools/lean/lean-4.34.0-rc2-linux`.
  Use `LEANRUN_TOOLCHAIN` or the runner's `--toolchain` option to select it.
  This machine-specific path is not a portable prerequisite.
- Never retry an unchanged proof target after a silent timeout. Split the
  boundary or establish a reusable lemma first. Explicit tactic diagnostics
  should guide the next revision.

LeanExe programs are pure, first-order and monomorphic within a restricted Lean
subset. `UInt64`, bounded `Nat` indices and scalar arrays are supported. The
compiler follows reachable definitions, emits a library-mode WASM `compute`
export, and the repository's C Wasmtime host marshals the array ABI. Native Lean
execution and WASM execution are distinct checks. Signed Lean integer arithmetic
is not part of the chosen executable subset.

## Input and output contract

- 0 to 64 points, 100 horizontal units apart. Terrain is piecewise linear.
- The raw Lean entry accepts `UInt64` elevations at most 1,000,000, relative to
  a datum. Invalid raw input returns `[]`.
- A local JS convenience driver accepts signed decimal integers, subtracts the
  minimum elevation, invokes the unsigned ABI, and adds that datum back to the
  output altitudes. The accepted elevation span is at most 1,000,000.
- Output speed is instantaneous horizontal waypoint speed, not total airspeed.
  Vertical velocity is zero at all waypoints and specified between them by
  the motion primitive.
- First and last altitude equal terrain height, with horizontal speed zero.
  Each interior waypoint has at least 100 clearance.
- Empty input returns `[]`; singleton `h` returns `[h, 0]`. Two points form a
  direct rest-to-rest takeoff/landing transfer.

### Endpoint exception

Define `r[i] = terrain[i] + clearance[i]`, with clearance 0 at endpoints and 100
at every interior point. Interpolate this floor linearly in horizontal position.
This is a takeoff ramp from 0 to 100 required clearance on the first segment and
a landing ramp from 100 to 0 on the last. All other segments require 100
clearance throughout. For two points, clearance is zero over the transfer.
Exempting only the isolated endpoint instants would be inconsistent with
continuous departure from and arrival at the ground. This corridor convention
is intentional and must be preserved in the specification.

## Point-mass motion model

| Quantity | Assumption |
|---|---|
| Horizontal speed | 0 to 20 units/second; waypoint choices 0, 5, 10, 15, 20 |
| Horizontal acceleration | Absolute value at most 1 unit/second² |
| Vertical speed | Absolute value at most 20 units/second |
| Vertical acceleration | Absolute value at most 4 units/second² |
| Waypoint altitude | Floor plus 0, 25, 50, ..., 200 |
| Interior states | 9 altitude choices times 5 speeds = 45 |
| Endpoints | State 0: on the floor and stopped |
| Vertical waypoint velocity | Zero |
| Continuity | Position and velocity continuous; acceleration may jump |
| Controls | Independent net horizontal and vertical acceleration |
| Route | Monotone forward motion; braking and waypoint stops allowed |

The ideal plant can accelerate up/down and forward/backward. Planning excludes
backward excursions. There is no combined thrust budget, jerk limit, wind or
tracking error. Gravity is absorbed into commanded net vertical acceleration.
The returned waypoints plus interpolation define a feedforward autopilot, not a
feedback disturbance-rejection controller. A larger control problem could use
continuous `(x,z,vx,vz)` states and acceleration controls, receding-horizon
replanning and feedback tracking. None of those extensions are implemented.

For one 100-unit segment, let horizontal endpoint speeds be `u,v`, altitude
change `dz=z1-z0`, duration `T`, and normalized time `s=t/T`.

### Moving primitive (`u+v > 0`)

```text
T = 200/(u+v)
x(s) = x0 + 100 * (2*u*s + (v-u)*s²)/(u+v)
z(s) = z0 + dz*(3*s²-2*s³)
vx(s) = (1-s)*u+s*v
ax = (v²-u²)/200
vz(s) = dz*6*s*(1-s)/T
az(s) = dz*(6-12*s)/T²
```

Executable maneuverability tests are:

```text
|v²-u²| <= 200
3*|dz|*(u+v) <= 8000
6*|dz|*(u+v)² <= 160000
```

The clearance gap is a cubic with Bernstein coefficients:

```text
b0 = z0-r0
b1 = z0-r0 - 2*u*(r1-r0)/(3*(u+v))
b2 = z1-r1 + 2*v*(r1-r0)/(3*(u+v))
b3 = z1-r1
```

All coefficients must be nonnegative. Endpoint state bounds guarantee `b0,b3`;
the uphill/downhill branch checks the potentially negative middle coefficient.
This is a sufficient, conservative certificate for clearance over the whole
segment. Some safe cubics are rejected; this restriction belongs to the graph
whose optimum is being proved.

### Rest-to-rest primitive (`u=v=0`)

Both coordinates use `p(s)=3*s²-2*s³`, with horizontal displacement 100:

```text
T = max(25, ceil(3*|dz|/40), ceil(sqrt(3*|dz|/2))) seconds
```

Endpoint floor margins imply clearance because both coordinates share progress.
The duration obeys the component speed and acceleration limits. Its square root
uses 17 steps of binary search with bounds 0 and 65536. Such edges allow steep
terrain to be traversed slowly; zero waypoint speeds do not mean zero motion
between waypoints. Local acceptance and the all-stop whole-route witness are
proved and connected to the public computation, so every accepted nonempty
terrain has a feasible returned route.

## Optimization and representation

Dynamic programming operates on the layered 45-state graph. It minimizes the
lexicographic pair `(total traversal ticks, sum of excess waypoint altitudes)`.
The secondary cost never sacrifices time. Remaining ties retain the first
candidate in ascending predecessor order.

There are 840 ticks/second. A moving edge with `k=(u+v)/5` uses `33600/k` ticks;
`k` is in 1 through 8, and these durations are represented exactly. Rest edges
use `840*T` ticks. Rejection is represented by zero edge ticks. Unreachable row
cost is the sentinel `10^12`.

Rows pack `[time, excess, parent]` for each state into 135 scalar words. The
current public function stores a flat history of parent state numbers and
walks backwards from terminal state 0, builds reversed altitude/speed words,
and reverses the final array. Work is O(n*45²), with O(n*45) predecessor memory,
plus LeanExe array allocation/copy overhead.

Named tail-recursive helpers `validHeights`, `appendParents`, `buildHistory`
and `unwind` expose induction boundaries for the public source proof. Input
heights are checked in reverse order, with the same acceptance condition. The
redundant terminal-infinity return was removed: the checked all-stop witness
establishes a finite terminal label for every accepted nonempty input.

Bounds used by the proofs:

- Floor <= 1,000,100; altitude <= 1,000,300; speed sum <= 40.
- Relevant edge-check products are below 10 billion, hence below 2^64.
- Rest duration <= 75,023 seconds.
- Every edge cost <= 63,019,320 ticks.
- After `i` segments, reachable time <= `i*63,019,320` and excess <= `i*200`.
- For at most 63 actual segments, these costs are far below both the sentinel
  and the UInt64 modulus. Component lemmas allow a conservative 64-step bound.

Optimality is only within the finite graph, with its quantized altitude/speed
states, zero vertical velocity at nodes, primitive family, conservative
clearance test and monotone motion. Do not claim unrestricted continuous-time
physical optimality.

## Code and proof files

Executable:

- `LeanExe/Examples/Drone.lean`: the public `compute` entry and helpers.
- `test/DroneNative.lean`: native Lean CLI for raw unsigned comparison.

Proofs, under `proofs/talos/lean/Project/Drone/`:

| Module | Content and key results |
|---|---|
| `Motion.lean` | Real cubic/Bernstein clearance, vertical speed/acceleration, horizontal speed and endpoint lemmas |
| `Sqrt.lean` | `ceilSqrt_correct`: actual UInt64 search returns the least adequate square root for inputs below 2^32 |
| `Arithmetic.lean` | Actual state decoding and no-wrap bounds; `restSeconds_bounds` |
| `Edges.lean` | Guard extraction and no-wrap products; `state_edge_clearance` for every real s in [0,1] |
| `Dynamics.lean` | Actual accepted integer guards imply all real component speed/acceleration bounds |
| `Timing.lean` | `state_ticks_exact`, `rest_admitted`, `edge_cost_bound` |
| `Kinematics.lean` | First and second physical-time derivatives, horizontal progress bounds, endpoint values |
| `Selection.lean` | Actual tail-recursive scan minimum and attainment; finite result has an admitted predecessor |
| `Rows.lean` | Exact packed field representation (`advance_word`), prefix preservation and row size |
| `Costs.lean` | Exact non-wrapping predecessor sums, stored parent bound and recurrence, propagated row bounds |
| `Initial.lean` | Initial array fields, size, unique reachable state and zero-layer bounds |
| `Optimality.lean` | General layered-graph lower-bound certificate and attaining-route optimality theorem |
| `Planner.lean` | Bellman invariant, feasibility and optimum for repeated executable `advance` transitions |
| `Feasibility.lean` | All-stop route witness, finite and optimal terminal labels, exact floor decoding and terrain specialization |
| `Reconstruction.lean` | Following stored parent words yields a bounded concrete state list attaining the optimal label |
| `History.lean` | Actual input guard, flat parent-history size/indexing, correspondence with the row recurrence |
| `Output.lean` | Actual unwind loop, encoded route, `compute_correct`, invalid/empty cases and exact endpoint pairs |
| `Safety.lean` | Direct output-index interior clearance, admitted adjacent pairs, continuous segment clearance, component limits and exact duration/tick correspondence |
| `Gluing.lean` | Reusable finite-curve construction on cumulative time; matching value/derivative gluing and continuous velocity |
| `Trajectory.lean` | Returned primitive endpoints and derivatives, moving/rest joins, `compute_global_smooth` for the assembled path |
| `Acceleration.lean` | Actual global velocity derivatives and component acceleration bounds, including derivatives within closed segment intervals at joins |
| `Corridor.lean` | Spatial interpolation of the specified floor, horizontal progress bounds, and clearance at actual global horizontal position |
| `WholeFlight.lean` | `Safe` and `compute_safe`: finite flight time, universal spatial/speed bounds, global acceleration, continuity, ground endpoints and singleton behavior |
| `SourceChecks.lean` | Aggregate check and printed axiom audit for these source components |

`Planner.layers` is a reference sequence of the actual executable `initial`
and `advance` calls. `History.computed_history_valid` connects its stored
parents to `buildHistory`. `Output.unwind_words` connects the public backward
loop to the encoded feasible route. `Output.compute_correct` composes these
results with Bellman optimality for the actual returned array.

Proofs use no proof holes, custom axioms or native evaluation proof shortcuts.
The printed axiom dependencies are only the standard Lean `propext`,
`Classical.choice` and `Quot.sound`, as applicable. Do not weaken goals or add
assumptions that merely restate the desired result. Tests are evidence, never
premises of correctness theorems.

## Work completed and observed results

1. Inspected the repository, specification, compiler entry conventions, native
   and WASM runners, Talos documentation and ProofKit boundaries.
2. Designed and documented the model and the endpoint clearance corridor.
3. Implemented, built, compiled and ran the native Lean and WASM controller.
4. Exercised flat, plateau, hill and repeated-ridge terrain; generated altitude
   and speed graphs using the continuous motion equations and exact outputs.
5. Added proof components and refactored two induction boundaries without
   changing the flight model: explicit-fuel square root and named
   tail-recursive selection/row accumulators.
6. Proved the current segment, arithmetic, selection, row and DP components.
7. Saved a self-contained project notebook, and separately saved `Drone.lean`
   and the four-flight PNG at the user's request. Generated visual artifacts
   remain outside this Git commit policy.
8. Created branch `drone`; checkpoint and push Lean proof increments here.

Example:

```text
input:  [0, 20, 80, 40, 0]
output: [0, 0, 145, 10, 180, 15, 165, 10, 0, 0]
segment seconds: [20, 8, 8, 20]
total: 56 seconds = 47,040 ticks
```

Four saved 1,400-unit, 15-point routes:

| Terrain | Time in seconds | Maximum waypoint speed |
|---|---:|---:|
| Broad plateau | 107.428571... | 20 |
| Flat | 107.428571... | 20 |
| Rounded hill | 117.428571... | 20 |
| Repeated ridges | 136 | 15 |

Runtime regression passed 48 WASM trajectories, 12 native Lean comparisons,
six exhaustively enumerated short-route optima, continuous clearance and
kinematic checks, reversal/translation properties, signed CLI handling,
invalid input guards, the 64-point limit and million-unit elevation changes.
The four saved plotted outputs also match the refactored WASM exactly.

Current emitted WASM: 14,198 bytes; SHA-256:
`0c24d2c1568ca40321421d19387843d4ee81c970d53e75adcb035b32343c0942`.
The binary is not committed and is not an exact-artifact proof.
The full repo test suite and Talos artifact-proof gates have not been run for
this new controller.

## Verification and reproduction

Use a supported resource environment and the pinned toolchain. From repo root:

```sh
tools/leanrun --timeout 3m lake --dir proofs/talos/lean build Project.Drone.SourceChecks
tools/leanrun --timeout 15m lake build lean-wasm LeanExe.Examples.Drone
tools/leanrun --timeout 2m lake env lean --run test/DroneNative.lean 0 20 80 40 0
tools/leanrun --timeout 2m .lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.Drone --entry LeanExe.Examples.Drone.compute \
  --out build/drone/drone.wasm
```

Create the output directory before compiling if necessary. Download/build the
Wasmtime C host using the existing repo instructions, then invoke the unsigned
array ABI with the host's `call` subcommand. No JavaScript WASM execution is
used.  The original workspace used an authorized `LEANRUN_LOCAL=1` setting and
an explicit toolchain selection.  Follow the current environment's execution
authorization and resource policy.

The original workspace held the convenience JS driver, JS test suite, expanded
prose documentation, plots, and notebook generator.  These files were excluded
from commits under the user's Lean-code-and-task-only instruction.  Native Lean
execution and the aggregate proof command above use committed code.  Later
commits should respect that file scope unless the user changes it.

## Remaining verification plan, in order

- [x] Check the existing source baseline in the current environment with the
  pinned toolchain and required resource limits.  Run
  `Project.Drone.SourceChecks` and review its axiom audit.  Distinguish dependency
  setup from proof failures and preserve diagnostics.
- [x] Complete the public whole-flight safety theorem by composing the
  established results.  State the finite flight interval, terrain and input
  assumptions, spatial clearance, speed bounds, acceleration bounds between
  joins, continuous position and velocity, and stopped ground endpoints.
  Include the singleton case and retain the specified takeoff/landing corridor.
  Build the combined theorem and aggregate source checks.  This is the first
  safety milestone.
- [ ] Prove WASM execution agreement after the source safety milestone.
  Prepare the generated program and annotations, identify the exact binary
  being proved, and establish ABI, memory, ownership, and termination conditions.
  Prove scalar helpers first, then predecessor selection and row construction,
  parent-history construction, reconstruction and reversal, and the public
  guards and entry.  Compose a `Wasm.TerminatesWith` theorem returning the same
  words as `Drone.compute`, then transfer the source safety result to those
  words.  Check the execution theorem against the generated model and the
  identified bytes.
- [ ] Discuss expansion after the safety baseline is checked.  Choose each
  additional model assumption or controller feature with the user, then extend
  its safety statement and proof.

Keep this record current and commit/push checked Lean increments on `drone`.
Preserve the separate source and image outputs.  Existing graph optimality and
exact tick-timing results remain available for the execution proof.  Follow the
existing commit scope and preserve branch history.

## Findings and failed approaches worth preserving

- A mutable record holding multiple arrays plus nested parent arrays compiled
  but trapped in generated `release`, even on singleton input. Packed scalar
  rows and flat parent storage solved the runtime issue without compiler edits.
- An initial non-tail recursive row refactor was rejected by LeanExe. Tail
  recursive accumulators are supported and preserve stable tie breaking.
- `UInt64` numeral coercions and modular arithmetic must be reduced explicitly.
  Blind `Nat.mod_eq_of_lt` rewriting can target an inner state modulus instead
  of the outer machine-word modulus.
- Core range loops are not simply kernel-reducible at every boundary. Rewriting
  through `Std.Legacy.Range.forIn_eq_forIn_range'` and the pure-yield fold lemma
  made the initial array proof check.
- Avoid elaborator expansion of the full 45-candidate scan when comparing cost
  projections. Reduce the small `Selection.cost` wrapper explicitly first.
- Existing ProofKit offers useful scalar, array, loop and allocator lemmas,
  but not a complete ready-made shortest-path or this controller theorem.
- The global documentation checker reports an unrelated pre-existing absolute
  temporary path in `paper/wgsl-verification-report/review.md` at the inspected
  base. No unrelated fix was made.

## Checkpoint log

### 2026-09-25 — initial drone branch checkpoint

Includes the Lean executable, native runner and source-proof modules listed
above, plus this task record. Targeted executable/WASM regression passed before
this proof-only increment. The aggregate `Project.Drone.SourceChecks` target passed (1,991 build jobs,
mostly cached); the printed axiom audit contains only standard Lean axioms. The outstanding `compute` and artifact boundaries are
explicitly retained in this record. Graphs and HTML are excluded.


### 2026-09-25 — terrain feasibility checkpoint

The first checkpoint was published as `b79e90347218c0c36ad1fb66a2a37fa2f3c760dc`
on `origin/drone`. HTTPS Git write credentials were unavailable, so the checked
Git tree was published through the authenticated GitHub connector, fetched, and
matched byte-for-byte before synchronizing the local branch. Subsequent remote
updates use non-forced branch updates; preserve the previous local commit when
synchronizing equivalent GitHub-created commits.

Added `Feasibility.lean`. Lean now proves an all-stop path for any bounded floor
sequence, reachability of the terminal stopped state, and an attained optimum
at that state in the actual row recurrence. The floor decoding theorem proves
that its UInt64 addition does not wrap and gives the intended endpoint and
interior values. These results specialize to every nonempty terrain with at
most 64 elevations, each at most 1,000,000. `compute` guard/loop/reconstruction
correspondence remains unproved. The focused feasibility target passed, and
the aggregate source check includes its theorems and axiom audit.


### 2026-09-25 — stored-parent reconstruction checkpoint

The feasibility checkpoint was published as
`3eff0614bb5220861db5134c8b7585b345bdac3e`. Added `Reconstruction.lean` and checked
`parent_step`, `backtrack_correct`, and `reconstructed_optimal`. These follow
the actual predecessor words in the proved row sequence, producing a concrete
list of bounded states with exactly n+1 points. The list is feasible and attains
the globally optimal terminal label. The public function's separate flat parent
history and reversed altitude/speed output loop are not yet equated to this
reference reconstruction. That correspondence is the next implementation proof.
The aggregate source target includes the new theorems and axiom audit.


### 2026-09-25 — public source correctness checkpoint

The stored-parent checkpoint was published as
`6d1208f42d90e37c5eb3040f8f9889339f75d1ca`. Refactored the public loops into
named tail-recursive helpers supported by LeanExe. Added `History.lean` and
`Output.lean`. The aggregate `Project.Drone.SourceChecks` target passes
(1,995 jobs), including `compute_correct`, `compute_invalid`, and
`compute_endpoints`; axiom dependencies remain standard only. No proof holes
or unchecked evaluation shortcuts were introduced.

The new public entry was compiled to WASM and the full targeted drone
regression passed again: 48 WASM flights, 12 native comparisons, six exhaustive
short-route optima, continuous limit checks and input/translation cases.
Logs: `build/drone/source-proof-check.log` and
`build/drone/public-refactor-regression.log` (generated, not committed).
The graph contract is now proved for the actual source `compute`, while the
continuous whole-flight composition and exact emitted-WASM proof remain
explicit further tasks. Keep future commits restricted to Lean and this file.


### 2026-09-25 — public output continuous-safety checkpoint

The public source theorem checkpoint was published as
`263b45f1611a049f78849b8f61fa83e77b54dacc`. Added `Safety.lean`, connecting
individual output word indices to bounded states and every adjacent pair to
an admitted edge. The four public corollaries establish interior 100-unit
clearance, universal continuous segment clearance, all component maneuverability
bounds, and exact tick/duration correspondence. These are kernel proofs over
all accepted inputs and all real normalized segment times, not sampled checks.
The focused target and aggregate source target pass with standard axioms only.

No executable behavior changed in this proof increment, so the previously
passed runtime suite and the rechecked four graph outputs remain applicable.
Graphs/HTML remain outside commits. The exact-WASM theorem and a packaged
global real-time path remain future work; neither is claimed by this checkpoint.


### 2026-09-25 — global trajectory and velocity continuity checkpoint

Resumed from published commit `1e56a01f2bcdc335c90e2e4771678d7b870f1701` after
the transient checkout had been cleared. Restored branch `drone`, the exact
pinned Lean release (version/commit checked) and pinned proof dependencies.
The bounded cache restore made progress to 96% before its time limit; a second
bounded call restored the remaining files. The initial archive extraction had
ownership-setting warnings in this managed workspace; file extraction and the
pinned Lean version check succeeded. Future extractions should use
`tar --no-same-owner`.

Added `Gluing.lean` and `Trajectory.lean`. The generic `stitch_smooth` theorem
constructs one finite curve on cumulative physical time and proves its
specified derivative and continuous velocity from local derivatives and matching
endpoints. The public `compute_joins` and `compute_global_smooth` instantiate
that result for the actual returned drone words, including stopped/moving
transitions and the singleton constant path. Position and velocity are
continuous at internal joins; no second-derivative claim is made there.
The focused trajectory target and aggregate source checks pass, with only
standard Lean axioms. Executable code is unchanged.

Proof-development findings: unfold partially applied coordinate definitions
before rewriting branch conditions. Separate branch simplification from index
arithmetic and default list-index simplification, so a guard is not rewritten
into a syntactically different expression before its hypothesis applies.
The generic derivative gluing proof combines derivatives within the left and
right half-lines and uses continuity only for the velocity gluing step.

Prepared a local unfinished `drone` case in `proofs/talos/cases.json` for the
next exact-artifact step (`complete: false`, annotations enabled, source module
`LeanExe.Examples.Drone`, entry `LeanExe.Examples.Drone.compute`, Lean namespace
`Project.Drone`). Its future behavior target is `Project.Drone.Spec.compute_correct`;
that target is not yet proved. The JSON registry edit is deliberately outside
commits under the user's Lean-code-and-task-only instruction.


### 2026-09-25 — cumulative interval and global safety checkpoint

The global smoothness checkpoint was published as
`3e55d65e225782b241a2a97421e89f0e6369ef94`. Added monotonic cumulative clocks,
interval coverage, and `stitch_on_segment`: the assembled curve equals the
intended primitive on each whole closed interval. Public corollaries connect
all four actual global coordinates to local primitives and transfer continuous
clearance and speed bounds to the global functions. The aggregate source check
passes; axiom dependencies remain standard only. Executable source is unchanged.

Started `tools/talos-artifact.js prepare drone`. Restored the pinned native
verifier's dependencies, reusing build caches only after matching their exact
Git revisions. Its default optimized C compilation of the large generated
emitter was slow and was explicitly interrupted (exit 130) to complete source
proof checks first. The next attempt uses a temporary local `moreLeancArgs =
["-O0"]` in the verifier/interpreter package configuration. This changes native
build optimization, not Lean definitions, kernel checking, or proof assumptions.
Record the emitted artifact digest and check it against the prior 14,198-byte
artifact before claiming artifact reproduction. Do not mark the unfinished
behavior theorem or exact-byte decoder identity as proved merely from generation.

### 2026-09-25 — safety-first scope and status review

Reviewed `41a97a6e80ac90e503e981ecd7052c2b489619e9` and confirmed that the remote
`drone` branch still named that revision.  Work in this checkout through the
review consisted of source inspection and planning.  Fresh Lean and runtime
checks remain pending here.  Earlier passing checks are recorded above.

The user set the first milestone to a checked whole-flight safety proof under
the current point-mass assumptions, followed by expansion from that baseline.
Updated the current status, evidence, risks, and work order to put source
composition and fresh checking first, WASM execution agreement second, and
model expansion after discussion.  The user declined reproducible-artifact
packaging as a priority.  This checkpoint changes the task record.

### 2026-09-25 — whole-flight source safety checkpoint

Resumed `drone` from `b5066cd4` in `/home/somebody/src/leanexe`. Installed the
pinned Lean 4.34.0-rc2 release and verified compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Materialized the pinned Talos,
mathlib, and supporting proof dependencies. The user's permission to execute
Lean locally authorizes `LEANRUN_LOCAL=1` here; all Lean and Lake commands used
`tools/leanrun` sequentially with bounded timeouts.

A session interruption left empty cache traces and truncated cached outputs.
Ordinary cache retrieval removed affected archives without repairing the empty
destination traces. A separately downloaded archive extracted correctly into
a fresh directory; forcing retrieval and extraction with `cache get!` repaired
the selected dependency closure. The initial aggregate run then reached its
three-minute limit while rebuilding supporting tactic libraries, with progress
diagnostics and no drone proof error. A separate `Project.Drone.Motion` build
completed that dependency boundary, followed by a successful original aggregate
source check (1,998 jobs). Setup failures and the interrupted build were not
treated as failures of the existing proof statements.

Added three proof modules. `Corridor.lean` uses the existing finite-curve
construction on 100-unit spatial intervals, proves that it interpolates
`floorAt`, and identifies normalized primitive progress with global horizontal
position. `Acceleration.lean` transports primitive velocity derivatives onto
the actual global velocity functions using agreement on each closed interval.
This yields bounded derivatives within each segment at both endpoints and
ordinary derivatives in the interior, without requiring acceleration to agree
across a join. `WholeFlight.lean` proves the global ground endpoints, normalized
time coverage, and bounds at every time in the finite flight, then packages
them in `WholeFlight.Safe` and `WholeFlight.compute_safe`. Its acceleration
corollary quantifies directly over all flight times outside the finite set of
waypoint times. Singleton terrain has zero duration and a constant stopped
ground path.

The focused modules and `Project.Drone.SourceChecks` passed (2,001 aggregate
jobs). The expanded printed axiom audit, including `WholeFlight.compute_safe`,
contains only the standard `propext`, `Classical.choice`, and `Quot.sound`.
There are no added proof holes, axioms, or native evaluation proof shortcuts.
Initial diagnostics were namespace resolution and endpoint index/coercion
normalization issues; no specification or input assumption was weakened.

Fresh native execution of `test/DroneNative.lean 0 20 80 40 0` returned
`[0, 0, 145, 10, 180, 15, 165, 10, 0, 0]`, matching the recorded example.
The executable planner was unchanged. The broader historical native/WASM
regression suite and artifact gates were not rerun for this proof-only increment.

Local evidence is retained in `build/logs/`: `cache-repair.log`,
`source-baseline-complete.log`, the focused proof logs (including failed
attempts), `source-whole-flight.log`, and `native-example.log`. These logs,
dependencies and toolchain files remain ignored local state. This checkpoint
contains only Lean proofs and this handoff. The first safety milestone is now
complete; exact compiled-WASM execution agreement remains the next proof task.

### 2026-09-25 — artifact generation recovery and annotation repair

Continued from `a669b528` toward WASM execution agreement. Installed Node
24.13.0, wasm-tools 1.251.0, and the checked Wasmtime 44.0.0 C API archive in
ignored local build directories. The user installed the missing C headers;
the repository's Wasmtime C host then built with the pinned Lean distribution's
Clang, using its builtin-header include directory together with the system
headers. No project runtime source changed.

The verifier's generated `Emit.c` crashed in bundled Clang 22.1.4 at `-O0`
(`alloc-token`) and `-O1` (`always-inline`). A focused build succeeded with
`moreLeancArgs = ["-O0", "-Xclang", "-disable-llvm-passes"]` in the ignored
Talos verifier package. The interpreter package retains the local `-O0`
setting. These flags affect native build optimization only. The compiler's
`Extract.Values` module also failed once while saving its `.olean`, then passed
on a focused bounded rebuild. Failure logs and compiler crash reproducers were
preserved locally.

Artifact preparation exposed an actual annotation bug in `directCallResults`:
`List.take resultCount` can yield a shorter suffix at the end of a branch, and
`mapM` on that suffix can succeed without a complete set of result stores.
The emitter now checks the suffix length before describing a complete local
result bundle. A call without that bundle keeps the stack-result annotation.
Focused regression cases cover no stores, a partial two-result bundle, and a
complete reversed stack-to-local bundle.

`tools/talos-artifact.js prepare drone` passes after that change. Its generated
`Program.lean` and `AnnotationMatches.lean` describe the real artifact. Both
before and after the annotation fix, the WASM has 14,198 bytes and SHA-256
`0c24d2c1568ca40321421d19387843d4ee81c970d53e75adcb035b32343c0942`, exactly
matching the earlier artifact. A fresh Wasmtime run returns
`[0, 0, 145, 10, 180, 15, 165, 10, 0, 0]` for the recorded example. A local
regression driver checks 48 accepted flights and four empty/rejected inputs
against an independent finite-graph planner; all pass, including 64-point
terrains and the maximum allowed height range. Runtime testing is supporting
evidence, not the missing execution theorem.

The first generated-annotation Lean build reached its five-minute limit while
building the broader interpreter dependency closure. It reported dependency
segfaults and a missing compiled linter declaration, before reaching drone proof
checking. A full forced cache restore is replacing the incomplete mixed mathlib
cache. Its first attempt was blocked by sandbox DNS and was stopped; the
approved network retry downloaded all 8,747 files and is extracting them.
`ExecutionScalar.lean` is being developed against the emitted functions, but
its Lean checks, the generated annotation checks, and native comparison harness
remain pending at this point. The full WASM execution and safety-transfer
milestone remains open. The local case registry stays outside commits.

The full forced cache extraction completed successfully. The corrected
`test/direct_call_annotations.lean` passes, and the generated native harness
passes all 12 native/WASM comparisons. This verified compiler-annotation
checkpoint includes `Binary.lean`, that focused regression, and this handoff.
The generated model and in-progress scalar proof files await their own Lean
verification before being committed. No instruction bytes changed.

### 2026-09-25 — interpreter dependency isolation

After restoring the full cache, a fresh `Project.Drone.SourceChecks` build
passed all 2,001 jobs again, including the whole-flight theorem and its
standard-axiom audit (`build/logs/source-after-cache-repair.log`). The restored
interpreter semantics module also builds successfully. The first scalar/model
aggregate then exhausted its eight-minute limit in `Interpreter.Wasm.SmallStep`,
before reaching the new drone proofs.

Divided that dependency into diagnostic boundaries instead of repeating the
unchanged target: executable definitions checked in seconds, and the full
inductive step relation checked separately with profiling. A simplification
trial for the scalar-float bridge lemmas passed but offered little improvement
and was not retained. A focused full dependency build uses sequential
elaboration and progress instrumentation only; its semantic definitions and
theorem statements/bodies are unchanged. The pending drone proof modules cover
scalar helpers, the square-root loop, and checked terrain reads. They remain
unverified development files until the dependency build allows their checks.

The instrumented `SmallStep` dependency build completed successfully in 760
seconds, with all five checkpoints reached. No proof rewrite or semantic
change was needed. Its profile records most time in simplification, tactic
execution, and processing recursive proof declarations. The prepared further
split was therefore not applied. The scalar/model aggregate is now rebuilding
the remaining interpreter proof modules against that checked dependency.

The generated drone `Program.lean` and all ten scalar execution lemmas now
check. The lemmas cover the three Choice projections, lexicographic choice,
distance, altitude, speed, both constants, and the unreachable sentinel, with
unchanged stores and only standard Lean axioms. Initial failures in these
drafts were proof scripting, typed-control normalization, and Nat/UInt64
conversion obligations; their final statements have no added assumptions.

The first annotation check exposed missing result-type metadata in the shared
`ScalarTransition.Expr.program` description. Its generated `and`/`or` branches
must carry an i32 result, while division/remainder guards and value branches
carry i64. Updated the shared description and its semantic proof using the
existing typed-control compatibility theorem. The generated drone annotation
identities now check by reflexivity, including the complete square-root loop;
no generated drone file or WASM instruction was hand-edited. All generic scalar
transition proofs also pass. Logs are `drone-model-scalar-5.log` (failed shared
proof attempt) and `drone-model-scalar-6.log` (passing drone and generic targets).

The same aggregate attempted two existing annotation examples but exhausted
its three-minute budget while building `FixedArrayAllocator`, before checking
those examples. Those regression checks remain pending; the successful drone
and shared scalar targets are not evidence that the entire aggregate passed.
Next checks are the bounded square-root loop and the checked terrain read.

Published the model/scalar checkpoint as `eec06de5`. The next focused aggregate
passes both `ExecutionSqrt.lean` and `ExecutionRead.lean`
(`build/logs/drone-sqrt-read-4.log`, 3,363 jobs). The square-root invariant ties
the current fuel and interval to the original source result; fuel decreases
on search steps and the completion flag decreases the measure on early exit.
It proves arbitrary UInt64 inputs and any representable fuel, not just the
17-step wrapper. The terrain-read theorem uses `UInt64Array.At`, an in-range
index, checked-load semantics, the stored length, and overflow-free index
increment to establish the exact source `floorAt` result with unchanged memory.
Both modules' axiom audits contain only the three standard Lean axioms.
Their earlier failed attempts are retained in the numbered local logs.

Published the square-root/read checkpoint as `843f3e6f`. Checked
`ExecutionValidation.validHeights_exact` against the actual input-validation
loop, including zero fuel, normal fuel decrease, early rejection, and the
borrowed-array ownership bookkeeping. Its store is unchanged. Checked
`ExecutionRest.restSeconds_exact`, preserving intermediate operand-stack values
across the repeated square-root calls with `TerminatesWith.append_args`.
The four duration comparisons use the source UInt64 maximum definition;
simplifying comparison hypotheses into different order relations too early
prevented their later use, so the final proof preserves those hypotheses.

Also checked `ExecutionPredecessorRead.predecessor_readTime`: the emitted
checked multiplication, checked array access, and precise resulting frame for
the first packed-row load. It is a prefix theorem, not the full predecessor
specification. `ExecutionEdgePrefix.edgeTicks_entry` checks the shared entry
setup and initial distance call. All four modules have standard-only axiom
audits. Their local logs include `drone-rest-validation-4.log`,
`drone-rest-edges-4.log`, `drone-read-edge-rest.log`, and
`drone-edge-prefix-rest-4.log`; aggregates that include a later failed or
timed-out target are not recorded as fully passing runs.

The full segment-cost tactic search reached its time budget without a
diagnostic. Split the duration theorem, rest/moving cases, and common entry
prefix instead of rerunning the same target unchanged. The rest case still
timed out after the prefix split, so a separate body theorem now uses explicit
call boundaries rather than searching through alternative callee rules.
Its check and the moving-case proof remain pending. The existing external
annotation examples remain pending behind the allocator dependency as recorded
above. No executable instructions or source input assumptions changed.

### 2026-09-25 — edge branch and arithmetic checkpoint

Published the validation/read-prefix checkpoint as `76e8c330`. Added and checked
`ProofKit.ConstIf.wp_constIf`, which handles constant-valued Boolean branches
without duplicating the caller's postcondition, and
`ProofKit.CheckedNatAdd.guard_spec`, which discharges the emitted overflow guard
from a representable Nat sum. Their axiom audits contain only standard axioms.
`Drone.EdgeSource.edgeTicks_eq` gives a checked non-monadic equation for the
source segment cost. `ExecutionEdgeRestBody` and `ExecutionEdgeRest` now prove
the complete emitted rest-to-rest segment-cost case. The final body check takes
about four seconds, and the public wrapper checks in two seconds.

The unrestricted moving-case tactic still exceeded its bounded runtime after
several control-flow reductions. A no-progress simplification could roll back
a preceding branch split; fixing that exposed the remaining nested arithmetic.
The next decomposition uses the already-checked `ScalarTransition.Expr`
framework for that arithmetic suffix, with an explicit evaluation lemma before
reconnecting it to the emitted body. That suffix, the moving-case theorem,
and the full predecessor theorem remain unverified development files. A generic
WP congruence experiment is also local and has not established a performance
benefit yet. No source behavior, instruction bytes, or input bounds changed.

Evidence: `build/logs/const-if-1.log`, the passing `CheckedNatAdd` target in
`edge-source-add-rest-1.log`, and the passing rest wrapper in
`drone-edges-compact-1.log`. Those latter aggregates contain other failed targets
and are not recorded as wholly passing runs. Subsequent tail attempts and
moving-case timeouts remain in their numbered local logs.

The emitted moving branch and complete `ExecutionEdges.edgeTicks_exact` now
check. `ExecutionEdgeTailModel` describes the arithmetic suffix using the shared
scalar-expression language; the `change` step in the execution theorem checks
its identity with the actual emitted suffix. `ExecutionEdgeTail` evaluates that
descriptor using the established `U64State` bridge. Explicit Option-bind and
constructor simplification, together with the seven semantic guard cases, avoids
the earlier unproductive generic simplification. The evaluation proof checks in
13 seconds and the moving execution proof in 5.3 seconds. The experimental WP
congruence rule was removed from imports and kept only as an ignored diagnostic;
the final proof does not require it.

`ExecutionPredecessor.predecessor_exact` also passes, covering both checked
packed-row reads, all altitude/speed/edge calls, the reachability guard, and the
exact three-word Choice result, with unchanged memory. Its assumptions are the
array representation, both row accesses in range, and a representable target.
The check takes 7.6 seconds. The aggregate
`build/logs/drone-predecessor-1.log` passes all 3,379 jobs, with standard-only axiom
audits. Predecessor scanning and the allocating array loops remain open.

The user explicitly authorized up to 12 GB of RAM for Lean on this machine.
Local runner mode still has no enforced cgroup memory cap; keep one Lean process
and bounded timeouts, and monitor memory against that ceiling. Recent drone
checks use about 4 GB resident memory. The earlier 4/6 GB standard-mode settings
are not active in this authorized local mode.

The scan proof now has checked entry, frame/invariant, and first-candidate
prefix lemmas. `scanPrefix_spec` checks the source-index increment and overflow
guard, copied arguments, actual predecessor call, and resulting comparison
stack in about four seconds. The first failed frame comparison was an
elaboration problem: normalize list append and the two representations of the
UInt64 index before matching the continuation. The instruction prefix itself
was already reducing successfully.

The combined scan-step proof still exceeded its bounded runtime, so its time
comparison cases were split into separate modules. `scanStep_time_lt` now
checks in 18 seconds, with only standard axioms (`drone-scan-time-1.log`).
The branch tactic stops at the continuation instead of trying more instruction
rules there, and uses explicit Boolean reductions. The equal-time branch needs
the UInt64-specific irreflexivity theorem; the generic order theorem did not
rewrite that comparison. The remaining cases, complete scan, and best-choice
wrapper are still being checked. Allocation/release adaptation and the
previously pending held-out annotation regressions remain open.

All scan cases now pass: equal-time in 58 seconds and the remaining unequal-time
case in 19 seconds. Their composition checks in 2.9 seconds, the complete
`scanPredecessors_exact` loop theorem in 5.3 seconds, and
`bestPredecessor_exact` in 3.8 seconds. The aggregate
`build/logs/drone-scan-best-8.log` passes all 3,388 jobs. All axiom audits contain
only standard Lean axioms. The loop theorem quantifies over representable
targets and packed predecessor rows covering the requested source range,
preserves the store, returns the exact three source Choice words, and proves
termination by decreasing fuel. The source-index overflow guard and borrowed
array ownership bookkeeping are included. Peak observed resident memory stayed
near 4.3 GB. Allocating array loops and the full compiled entry remain open.

Published the scan/best checkpoint as `8dcce121`. Split the unchanged allocator
definitions and frame helpers into `FixedArrayAllocatorBase.lean`, leaving its
execution theorem in `FixedArrayAllocator.lean`. The base checks in 4.6 seconds;
the focused execution check passes in 93 seconds (`allocator-region-1.log`,
3,345 jobs). The formerly blocked annotation regressions now both pass:
`Project.TinyGpt2Seq.AnnotationMatches` and
`Project.SequenceSoftmax.AnnotationMatches` (`scalar-held-out-2.log`, 3,362 jobs).
This closes the held-out regression gap for the shared scalar control-type
change. Drone heap allocation/release adaptations are next; their initial check
also needs the existing shared runtime/heap proof dependencies to be built.

Published the allocator/regression checkpoint as `c404f1a2`. The initial heap
aggregate built the uncached runtime and existing heap dependencies, then reached
its ten-minute limit before the final targets. Split the generic word-buffer
finishing lemma into `HeapWordsFinishBase.lean`, preserving the old public
release theorem through its original import. The drone allocation and release
adaptations now check in about three seconds each. They use the actual drone
module and release function 29, including free-list reuse and memory growth.

Added checked empty-array memory/ownership lemmas, exact word-array capacity
arithmetic, and preservation of borrowed arrays across allocation, writes, and
release. The borrowed representation matters for the actual host ABI:
`tools/wasmtime-host.c` allocates terrain through the raw-buffer allocator and
writes its length and words, without changing the header to internal-array kind.
The input-preservation assumptions therefore do not require that internal kind.
The empty-array proof was divided at the memory-write boundary after a bounded
aggregate expired; its two final checks take about three seconds each.

The first empty-array axiom audit exposed an inherited native `bv_decide` axiom
through `Mem.read64_write64_same`. Replaced that use in all six locations in
`ProofKit.FixedArrayResult` with the existing kernel-checked
`ProofKit.Memory.read64_write64`. The allocator, empty, singleton, and pair
result audits now contain only standard Lean axioms
(`build/logs/allocator-result-axioms.log`). The new heap, borrowed-array, empty
array, and capacity lemmas also have standard-only audits. Both held-out
annotation regressions pass again after this shared change.

`WordArrayPush.program` describes the common fifteen-scratch-slot push sequence.
`Drone.ArrayPushShape` checks by reduction that all three pushes in the emitted
advance loop match it exactly. Those are instruction-identity lemmas; the full
shared push execution proof and the allocating controller loops remain open.
The aggregate `build/logs/drone-array-foundations-2.log` passes all 3,489 jobs,
including the retained Euler release theorem and both annotation examples.
`drone-array-memory-1.log` separately passes the borrowed-input and empty-memory
lemmas. Earlier failed and timed-out runs remain in their numbered local logs.

The shared array-push execution theorem now passes. `WordArrayPushFrame` models
the fifteen scratch slots; separate preparation, capacity, header installation,
and copy/append lemmas each check in roughly three seconds. The complete drone
`word_push_spec` composes them with the existing free-list allocator, returns
the exact pushed array and pointer, preserves the borrowed source, and restores
the heap and new-buffer ownership invariants. Its write-range result also lets
callers preserve unrelated live arrays. Both fresh allocation and free-list
reuse are covered. `build/logs/drone-push-3.log` passes all 3,484 jobs, and every
new axiom audit contains only standard Lean axioms.

The small failed iterations were local elaboration issues: slot zero needs an
explicit frame lookup, store addresses need the numeric 32-bit modulus exposed,
and UInt64 capacity equality must be converted to a natural-number bound. No
silent timeout occurred in this checkpoint. The full allocating controller
loops and compiled compute/safety transfer remain open; source and earlier
scalar/scan execution proofs remain checked.

Published the shared push theorem as `2396ddba`. The budgeted push wrapper now
reuses `OutputBudget` to account for allocation bytes, physical pages, and the
module's memory cap while preserving every previously live borrowed/owned word
array. The emitted empty-array allocation sequence also has an execution
theorem, checked instruction matches in `advance` and `initial`, and a budgeted
wrapper. The initial budget build populated existing output-map dependencies;
its final diagnostics were two redundant tactics, not resource exhaustion.

The parent-history loop now has checked packed-parent reads and both cleanup
cases. `append_read_spec` covers state increment, multiplication by three,
offset addition, and checked load. The cleanup proofs distinguish an initial
borrowed buffer from a tracked buffer that must be released. Both cases check
in about eight seconds. `PreservesWords` records caller-owned and borrowed
arrays across allocations/releases; the complete `append_step_spec` uses it
to keep the caller's live memory intact and proves the next loop state and
remaining budget. `build/logs/drone-append-step-3.log` passes all 3,532 jobs;
all new dependency audits contain only standard Lean axioms. The terminating
parent-history loop, other allocating loops, and compiled compute theorem are
still open.

Published the budget/parent-step checkpoint as `11a0dfa2`. The complete
`appendParents_exact` function proof now passes (`drone-append-3.log`, 3,531
jobs, 4.5 seconds for the final theorem). It proves source agreement and
termination with decreasing fuel, exact owned-array return values, preservation
of the caller's live arrays, nonaliasing of the new result after a nonempty
append, and the remaining allocation/page budget. The entry and loop invariant
are separate from the step theorem. All audits remain standard-only. The next
allocating function is the row-building advance loop, combining best-choice
scanning with three pushes per state.

The entire row-building `advanceLoop_exact` and its `advance_exact` wrapper
now pass. Choice selection covers ordinary states and the final-layer stopped
state restriction; preparation checks target increment; the three pushes
preserve every caller-live array and have exact allocation budgets; both
borrowed and tracked old-row cleanup cases pass. The loop proves termination,
source agreement, owned results, and nonaliasing/preservation.

The first combined three-push proof reached its elaboration heartbeat limit.
Splitting off `advance_two_push_spec` reduced the final two/three-push checks
to about four seconds each. Some large instruction-shape reductions also
needed the existing 32,768 recursion-depth setting. The wrapper now has
separately checked entry and finish lemmas; its earlier heartbeat failures
also followed a shadowed `previous` binder (allocator scratch word versus
source array), which is fixed. Read the first diagnostic before the later
normalization errors. The final wrapper check takes 3.1 seconds.

`build/logs/drone-advance-5.log` passes all 3,572 jobs, with standard-only
axiom audits. The row loop itself checks in 4.5 seconds and the complete step
in 4.7 seconds. Observed Lean RSS was about 4.1 GB plus 0.9 GB for Lake, below
the user's 12 GB ceiling. Initial-row construction, full history construction,
route unwinding/reversal, and the compiled compute/safety transfer remain open.

The complete compiled initial-row constructor now checks in `initial_exact`.
The source range fold is characterized by `initialRows`; each emitted loop
step chooses the exact initial cost, performs three budgeted pushes, releases
the previous tracked row, and advances its state without overflow. The loop
terminates after 45 states. The wrapper allocates and finally releases its
empty seed while preserving every caller-live array and returning a fresh,
owned array equal to the source `initial`.

The large loop step was divided into preparation, one/two/three pushes,
cleanup, and a small invariant. A shared `RangeGuard` lemma handles the
emitted unsigned range exit without expanding the following body. Early
cleanup failures exposed missing nonzero-root assumptions and an unresolved
`br_if` condition; the checked proof makes those conditions explicit. The
entry proof also needed explicit allocator scratch normalization. Failed
runs are retained. `build/logs/drone-initial-3.log` passes all 3,595 jobs;
the loop checks in 3.6 seconds and the final wrapper in 3.1 seconds. All new
axiom audits contain only standard Lean axioms. Full history construction,
route unwinding/reversal, and the compiled compute/safety theorem remain open.

`buildHistory_exact` now verifies the complete compiled history constructor.
The emitted loop reads adjacent terrain floors, detects the last layer,
allocates a seed, executes the checked row solver, appends all 45 parents,
and advances its parameters. Its invariant proves termination, exact source
agreement, preservation of live arrays, fresh nonempty results, and the
remaining allocation/page budget. The emitted ownership trackers remain zero
through this wrapper; its budget conservatively includes every allocation.

The append-call setup hit a 200,000-heartbeat elaboration limit. Splitting
its parameter preparation into a separate lemma resolved that boundary.
An additional checked `owned_root_ne_zero` lemma prevents Lean from expanding
an entire source row computation just to project an allocation's root bound.
The combined step then checks in 3.4 seconds. `NatSub.guard_spec` now exposes
saturated subtraction at an already-evaluated branch, for history reads and
the forthcoming unwind loop. Failed runs remain in `build/logs`.
`build/logs/drone-history-5.log` passes all 3,600 jobs, and every new axiom
audit is standard-only. Route unwinding/reversal and final compiled
compute/safety transfer remain open.

The compiled route-unwind step is now checked end to end. It emits speed and
altitude with two preserved, budgeted pushes; reads the parent through checked
saturated subtraction, multiplication, addition, and array access; decrements
the terrain index; and releases the tracked prior output while preserving
terrain, history, and caller-live arrays. `drone-unwind-step-1.log` passes all
3,572 jobs, with the composed step checking in 3.9 seconds and standard-only
axioms. Explicit scratch values and checked-index arguments avoid the
metavariable/normalization failures seen in earlier parent-read attempts.

`ParentBounds.computed_parent` independently proves that every stored parent
is below 45, without additional terrain assumptions. `WordArrayGenerateLoop`
provides a checked framed UInt64 array-fill loop using `PrefixAt`, needed for
the emitted reverse-copy. These checks are recorded in
`drone-parent-bounds-2.log` and `word-array-generate-2.log`. The terminating
unwind loop, reversal wrapper, and compiled compute/safety transfer remain
open; reverse-read/copy files are still being checked and are not part of
this verified checkpoint.

The compiled unwind loop now terminates with the exact source accumulator
and a reserved reversal budget (`drone-unwind-loop-2.log`). The shared
reverse read/copy loop and the allocator-backed `word_reverse_budget_spec`
also check, preserving caller-live arrays and returning a fresh owned array
equal to the input's reverse. `drone-reverse-budget-3.log` passes all 3,590
jobs with standard-only axioms. A frame normalization failure was resolved
by rewriting only the length-header store, preserving the scratch equality
needed by the copy lemma. The unwind return wrapper and final compiled
compute/safety transfer remain open.

`unwind_exact` now proves termination and exact source agreement for the
complete compiled reconstruction function, including allocation, reversal,
and return. `drone-unwind-2.log` passes 3,597 jobs; the wrapper checks in
3.1 seconds with standard-only axioms. The loop invariant now preserves
the two zero scratch slots needed at the reversal boundary. Separately
checked frame, preparation, and return lemmas keep that boundary small.
The nested WASM branch continuations require an explicit extensional
equality; treating their code as plain concatenation was insufficient.

Top-level composition exposed an ABI specialization still to adjust: the
public compute passes terrain with owner zero, while the current history
and unwind entry lemmas use its pointer as owner. Their read-only terrain
frames will be specialized to the actual borrowed-input convention before
completing the public compute and safety transfer proofs.

History and unwind entry proofs now use compute's actual borrowed-terrain
ABI (owner zero, pointer nonzero). The history target checked in
`drone-borrowed-terrain-1.log`; that aggregate rebuild reached its overall
three-minute limit after successfully checking the history and unwind
cleanup modules. Verification was split at new checked compute-call helpers
before the focused unwind target, which passes in
`drone-borrowed-unwind-1.log` (3,597 jobs).

`drone-compute-calls-2.log` checks the initial-row setup, history call,
unwind setup, and unwind call against the actual emitted entry code. These
small CPS boundaries preserve the frame fields needed for composition.
All audited axioms remain standard. The forward/accepted-input composition,
public dispatch, concrete allocation bound, and safety transfer are next.

The compiled execution/safety milestone is complete. `compute_forward_spec`
and `compute_reconstruct_spec` compose the checked helpers into the accepted
branch. `compute_guard_spec`, `compute_validate_spec`, and
`compute_reject_spec` cover length/height validation and both empty-result
paths. `Execution.compute_exact` proves termination and exact source output
for the public one-pointer ABI, preserving caller-live arrays and the
remaining allocation budget. The checked cost formula bounds every accepted
input up to 64 points by 37,580,992 allocated bytes.

`Project.Drone.Spec.compute_correct` exposes the complete compiled contract
with a 64 MiB memory limit and intact borrowed terrain. `Spec.compute_safe`
combines that exact memory result with `WholeFlight.Safe` under precisely the
existing accepted, nonempty terrain assumptions. Both audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The final check is recorded
in `drone-spec-4.log` (3,712 jobs); the specification module checks in 3.1 seconds.
The public entry needed an explicit final-instruction boundary after its
nested branch continuations, plus ordinary Bool/Nat simplification of the
source dispatch. No admitted obligations or native decision axioms were added.

`tools/talos-proof.js check drone` also passes fresh generation/equality and
proof checks in `drone-artifact-check-final.log`. The sandbox initially blocked
the driver's Git subprocess with EPERM, so the authorized check ran outside
the sandbox. Its final status text still reflects the locally staged registry's
legacy `complete: false` flag; the specification target itself passes. Registry,
driver, generated-build and packaging changes remain outside the requested
Lean-code-and-task-only commit scope. The generated WASM hash is unchanged,
so the earlier independent runtime comparisons remain applicable. No model
expansion or additional physical assumptions were introduced.

---
