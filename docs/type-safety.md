# Independent core type safety

Track 1 establishes operational type safety for an independent first-order core.
The work is on `typesafety`, starting from compiler revision
`a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`.  The [working state](../task.md)
owns the current agenda, open decisions, and resume notes.  The
[journal](../plans/type-safety-journal.md) records proof and verification history.
The [coverage ledger](type-safety-coverage.md)
tracks each documented operation family, including derived APIs not yet proved.

## What soundness means here

Operational type soundness relates a language's typing rules to that language's
execution rules. A compiler-correctness theorem is not a premise or prerequisite
of this result. The checked core below already has a complete type-safety theorem
for its own syntax and semantics.

Four subjects must remain distinct:

| Subject | Obligation |
|---------|------------|
| Lean source logic | The source uses Lean's dependent theory and the assumptions in its environment. This work does not prove Lean's logical consistency. |
| Runtime-language type safety | Prove preservation and progress for independently defined typing and execution rules. |
| Adequacy of the language model | Account for the constructs and intended behavior of the language being specified. A related calculus is not automatically an adequate model. |
| Compiler correctness | Prove that extraction and compilation respect the specified language. These are separate translation theorems. |

The full runtime-language theorem remains open because its independent language
definition and metatheory are incomplete. The missing compiler proof is a
different obligation, not the reason the full language theorem is unfinished.

## Language and execution

The core has Unit, Bool, bounded natural numbers, 8/32/64-bit unsigned words, products, binary sums,
variables, let bindings, conditionals, projections, complete product patterns,
Unit elimination, sum and natural case analysis, bounded-natural operations, and direct first-order
calls with arbitrary finite argument lists, persistent homogeneous arrays, and
nominal recursive data with strict construction and exhaustive matching.
Expressions, values, and machine states are ordinary untyped data. Separate
inductive judgments describe their types. Natural literals and natural values
must be below `2^64` when typed. Addition and multiplication check overflow;
subtraction saturates; division by zero yields zero and remainder by zero yields
the dividend. Min/max and equality/order comparisons are also defined. Successor,
predecessor, and Boolean-to-natural conversion are transparent derived forms.
Words carry explicit widths and canonical bounded values. Word addition,
subtraction, and multiplication are modular. Division/remainder use unsigned
arithmetic with the specified zero-divisor conventions; min/max and comparisons
are unsigned. Explicit conversions normalize when narrowing and preserve values
when widening. Wrong-width operands are rejected by typing and checked by the
runtime rules. Word operations introduce no new failure terminal. Bitwise
AND/OR/XOR use a finite structural definition with proved arithmetic per-bit
semantics. Complement is derived XOR with the width mask. Shift counts are
reduced modulo the word width; right shifts are logical/unsigned.

Evaluation is a deterministic, left-to-right call-by-value machine with explicit
lexical environments and continuations. Pairs and call arguments are strict;
only the selected conditional or sum branch executes. A let binding or sum-case
payload is prepended to the lexical environment at variable index zero. Calls
start with a fresh environment: index zero denotes the first argument, index one
the second, and so on. Suspended continuations retain the caller bindings they
need. These conventions specify this core, not Lean's imported-expression format.

`natCase` evaluates its scrutinee once. Zero enters its branch without a new
binding; successor enters its branch with the predecessor at index zero. Both
branches must have the same type, and the profile requires use of the predecessor.

`split` prepends the left and right product fields in that order. `unitCase`
introduces no binder. The syntactic relevance profile requires every introduced
binding to occur in its scope and rejects `fst`/`snd` recursively. Repeated use is
allowed; a use in one conditional branch suffices. This is neither a linearity
discipline nor a claim of semantic necessity. `ProfileTyped` and
`ProfileProgramTyped` require both ordinary typing and these admission checks.

Function bodies are checked against fixed declaration and signature tables.
`ProgramTyped` requires well-formed declarations and signatures, and exactly one
body per signature, checked under its parameter types and the same global tables.
Calls must supply exactly the declared argument
types and arity. Self-recursion and mutual recursion are permitted; program
typing assumes neither termination nor execution safety.

Successful addition and multiplication return their mathematical result. Overflow
records the operation and both operands. `Terminal` admits only a final return
or overflow of two bounded operands whose tagged sum/product is at least `2^64`. Missing
variables or functions and ill-shaped eliminations have no transition and are
not permitted failures. Their exclusion is a substantive part of progress.

Arrays contain finite homogeneous sequences whose lengths are below `2^64`.
The language provides explicitly typed empty construction, size, and checked
get, set, push, and append. The checked operations return `inl unit` for an invalid
index or unrepresentable new length, and `inr payload` for success. All operands
evaluate left to right, including a set replacement when the index is invalid.
These errors are ordinary typed data; they introduce no new terminal failure.
Arrays here are persistent values, with no physical heap or allocation model.

Nominal declarations list constructors and their ordered field types. Every
nominal reference must name a declaration, including references under arrays,
products, and unused sum alternatives. Self-recursion and mutual recursion are
allowed; formation checks indices without unfolding recursive declarations.
Empty datatypes are permitted, but an empty match must declare a well-formed
result type. The type grammar has no negative field positions. Values are finite
inductive trees; no theorem asserts that every declared type has a value.

Constructor fields evaluate left to right. Matching requires one typed branch
per declared constructor, exact field arities, and syntactic use of every pattern
field in the profile. Runtime matching checks nominal identity and selected
arity, then prepends the fields to the captured environment. Exhaustiveness is
a static typing property. No source-recursion recognizer is used by these rules.

This evaluation strategy belongs to this core. Connecting demand-based LeanExe
extraction to it requires a separate theorem. The core does not import the
extractor, diagnostic IR evaluator, emitter, or Talos.

## Proved results

The principal closed-term theorem, `closed_type_safety`, has the shape:

```lean
ProgramTyped declarations program signatures →
ExprTyped declarations signatures [] expr τ →
Steps program (initial expr) final →
StateTyped declarations signatures final τ ∧ ¬ Stuck program final
```

`Steps` denotes any finite sequence of actual machine steps, including zero
steps. `Stuck` means no successor and no permitted terminal outcome. Thus every
finite execution prefix remains well typed and ends in a state that either can
step, returns a value of the declared result type, or records justified overflow.
The general `type_safety` theorem also covers open expressions and suspended
computations supplied with well-typed environments and continuations.

| Theorem | Guarantee |
|---------|-----------|
| `preservation` | Every actual step from a typed state preserves the overall result type. |
| `progress` | Every typed state is terminal or has a successor. |
| `type_safety`, `closed_type_safety` | Every reachable state remains typed and cannot be stuck. |
| `return_type` | A completed execution returns a value of its original result type. |
| `overflow_is_justified` | A reached overflow contains bounded operands whose tagged mathematical sum/product exceeds the representation. |
| `step_deterministic` | Two successors of the same state are equal. |
| `profile_type_safety`, `profile_return_type`, `profile_overflow_is_justified` | The corresponding execution guarantees for admitted profile programs. |
| `declarationsWellFormed_iff`, `signaturesWellFormed_iff` | The corresponding Boolean checks accept exactly well-formed declaration/signature tables. |
| `ExprTyped.wellFormed`, `ArgsTyped.wellFormed` | Typed expressions/arguments have formed types under formed ambient tables and contexts. |
| `ValueTyped.wellFormed`, `EnvTyped.wellFormed`, `StateTyped.wellFormed` | Value/environment types are formed; admitted-program runtime states have formed result types, including overflow states. |
| `BranchesTyped.length`, `BranchesTyped.lookup` | Exact branch coverage and declared field arity/type at every selected constructor. |

The profile module also proves exact characterizations of its binding and
argument checks. `programAdmissible_lookup` establishes that each declared
function has an admitted body using every parameter index. These Boolean checks
do not replace ordinary type checking, and relevance is not a runtime invariant.

The array module proves exact failure conditions and successful result/length
characterizations. Successful set reads back the replacement at the selected
index and preserves every other read. Push and append preserve element order,
with separate lookup laws for the old and appended regions. Primitive typing
lemmas preserve homogeneous contents and representable lengths; the extended
machine proofs use these lemmas for every array continuation frame.

The proof first constructs a typed successor for each expression and continuation
frame, using typed lookup and canonical forms. This gives progress and one-step
preservation for the independently defined executable transition function.
Induction over execution then establishes safety for every finite prefix.
Environment extension and lookup replace syntactic substitution in this machine
presentation. No premise assumes one of these safety conclusions.

## Implementation and verification

| Module | Content |
|--------|---------|
| [Formation.lean](../LeanExe/TypeSafety/Formation.lean) | Types, nominal declarations, formation judgments, and exact Boolean checker characterizations. |
| [NatOperations.lean](../LeanExe/TypeSafety/NatOperations.lean) | Pure bounded-natural operations, exact result/failure laws, comparison laws, and bounded outcomes. |
| [BitOperations.lean](../LeanExe/TypeSafety/BitOperations.lean) | Structural finite-bit computation, arithmetic per-bit correctness, bounds, reconstruction, and bit extensionality. |
| [WordOperations.lean](../LeanExe/TypeSafety/WordOperations.lean) | Explicit-width arithmetic/conversions, bitwise identities and complement, and masked-shift laws. |
| [Core.lean](../LeanExe/TypeSafety/Core.lean) | Syntax, extrinsic expression and program typing, typed environments, lookup, and canonical forms. |
| [ArrayValues.lean](../LeanExe/TypeSafety/ArrayValues.lean) | Pure checked array operations, failure/result/length/read laws, and primitive typing. |
| [Machine.lean](../LeanExe/TypeSafety/Machine.lean) | Executable transitions, typed frames and continuations, state typing, and determinism. |
| [Safety.lean](../LeanExe/TypeSafety/Safety.lean) | Progress, preservation, finite-execution safety, result typing, and overflow justification. |
| [Profile.lean](../LeanExe/TypeSafety/Profile.lean) | Syntactic admission checks, their characterizations, and profile safety. |
| [Typing.lean](../LeanExe/TypeSafety/Typing.lean) | Total inference, exact admission checks, type uniqueness, and checker-to-safety corollaries. |
| [BoolDerived.lean](../LeanExe/TypeSafety/BoolDerived.lean) | Strict Boolean source expansions, typing/inference/relevance equations, staging and truth-table execution proofs. |
| [ValueEquality.lean](../LeanExe/TypeSafety/ValueEquality.lean) | Total raw value/list comparison and exact equality laws, used by the source equality transition. |
| [EqualityFlags.lean](../LeanExe/TypeSafety/EqualityFlags.lean) | Constructive monotone Boolean-table saturation and its proved iteration bound. |
| [EqualityTypes.lean](../LeanExe/TypeSafety/EqualityTypes.lean) | Independent equality-domain judgments, formation, exact terminating admission checker. |
| [Renaming.lean](../LeanExe/TypeSafety/Renaming.lean) | Capture-avoiding traversal, pointwise algebra, context transport, typing preservation and weakening. |
| [RenamingProfile.lean](../LeanExe/TypeSafety/RenamingProfile.lean) | Exact free-occurrence images, protected-prefix use, relevance invariance, and profile typing transport. |
| [RenamingEnvironments.lean](../LeanExe/TypeSafety/RenamingEnvironments.lean) | Exact raw environment lookup correspondence and arity-preserving branch lookup. |
| [RenamingDynamics.lean](../LeanExe/TypeSafety/RenamingDynamics.lean) | Raw frame/state correspondence, exact step-result matching, both finite-trace directions, and return/overflow/stuck-reachability equivalences. |
| [Continuations.lean](../LeanExe/TypeSafety/Continuations.lean) | Continuation extension, exact finite boundary decomposition, and return/overflow/stuck sequencing equivalences. |
| [Execution.lean](../LeanExe/TypeSafety/Execution.lean) | First-step decomposition, inversion at no-successor endpoints, and exact first-operand sequencing laws. |
| [TypeSafety.lean](../LeanExe/TypeSafety.lean) | Independent import target. |

Run the maintained [verification gate](../tools/type-safety.js):

```sh
tools/type-safety.js check
```

The gate checks the version against `lean-toolchain`, builds only the independent
`LeanExe.TypeSafety` target, checks [26 core examples](../test/type_safety.lean),
[41 profile examples](../test/type_safety_profile.lean),
[46 array examples](../test/type_safety_arrays.lean),
[57 nominal-data examples](../test/type_safety_data.lean),
[65 typing-checker examples](../test/type_safety_typing.lean),
[73 bounded-natural examples](../test/type_safety_naturals.lean),
[73 word examples](../test/type_safety_words.lean),
[49 bitwise/shift examples](../test/type_safety_bits.lean),
[35 natural-case examples](../test/type_safety_nat_case.lean),
[47 Boolean examples](../test/type_safety_booleans.lean),
[25 raw equality examples](../test/type_safety_value_equality.lean),
[38 equality-domain examples](../test/type_safety_equality_domain.lean),
[35 source equality examples](../test/type_safety_structural_equality.lean),
[26 renaming examples](../test/type_safety_renaming.lean),
[27 renaming-profile examples](../test/type_safety_renaming_profile.lean),
[17 environment-correspondence examples](../test/type_safety_renaming_environments.lean),
[26 renaming-execution examples](../test/type_safety_renaming_dynamics.lean), and
[29 continuation/execution examples](../test/type_safety_continuations.lean). It audits the
transitive axiom dependencies of all 411 declared theorems across the twenty
development modules. The maintained list includes helper proofs as well as the
main safety results.
Missing audit results or any axiom other than `propext` fail the gate.
Behavior checks and the audit run with warnings treated as errors. The examples
exercise lexical capture, both sum branches, branch selection, strict pairs,
addition boundaries, malformed states, argument order, exact arity, fresh callee
environments, caller continuation restoration, and a typed recursive self-loop.
They complement the universal theorems by checking the intended semantics.
Profile examples additionally cover two-field binding order, lexical shifts,
Unit elimination, ignored fields and parameters, nested projections, duplicate
uses, and uses confined to an unselected branch.
Array examples exercise invalid and boundary indices, persistent updates,
nested arrays, left-to-right failure order, captured replacement environments,
array parameters, heterogeneous-value rejection, and malformed array frames.
Nominal examples cover mutual/empty/cyclic declaration formation, malformed
hidden types, exact field/branch coverage, empty elimination, runtime result
formation, field binding order, raw mismatches, and a typed recursive list sum.
Typing examples cover exact inferred types, malformed unused ambient entries,
whole-program alignment, recursive programs, and combined relevance admission.
Natural-operation examples cover representation boundaries, tagged failures,
saturation, division/remainder by zero, comparisons, strict operand order,
captured environments, malformed states, and a recursive countdown program.
Word examples distinguish modular arithmetic from bounded-natural overflow, test
unsigned comparison and conversion boundaries, reject width mismatches in both
source admission and raw execution, and compose words with arrays/data/calls.
Bitwise examples cover exact patterns, complement, masked counts, unsigned right
shifts, operand order, rejection, and function composition. Closed 64-bit traces
use a test-local elaborator recursion-depth limit of 4096; they remain ordinary
kernel-checked proofs, without native evaluation certificates. Natural-case
examples cover predecessor bounds, nested/captured scopes, static checking of
unselected branches, relevance, and recursive calls.

The complete gate passed on 2026-09-24 with exact Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Each audited theorem depends on no
axioms or only Lean's standard propositional extensionality axiom, `propext`.
There are no proof holes, added axioms, unsafe definitions, or native-evaluation proof shortcuts in
these modules. This remains a proof checked by Lean's kernel and standard
foundation, not a proof of the kernel's consistency.

Every Lean invocation goes through `tools/leanrun` with a timeout and the shared
process lock. The user explicitly authorized local execution without systemd
cgroups in the ongoing proof conversation, using `LEANRUN_LOCAL=1`; the complete
2026-09-24 checks below used that mode. Other sessions retain the default resource
policy in the [repository instructions](../AGENTS.md) unless separately authorized.
An explicitly installed pinned toolchain can be selected with `LEANRUN_TOOLCHAIN`.

## Boundary and next work

This result does not establish termination, absence of arithmetic overflow,
source extraction correctness, ownership safety, or WebAssembly correctness.
There is no claim that existing accepted LeanExe programs have been translated
into this core. Raw binary64, Option/Except
combinators, additional array operations, byte arrays, dependent indexed data, physical heaps, and
compiler-specific recursion recognizers remain outside the language proved here.

Sum introductions now explicitly state the other alternative's type:
`inl otherTy payload` and `inr otherTy payload`. This removes the unspecified
summand from the source syntax; runtime values remain unannotated. Expression types are now proved unique (`ExprTyped.unique`).
`inferRaw_iff` characterizes the raw declarative judgment exactly;
`infer_eq_some_iff` additionally requires well-formed declarations, signatures,
and context. `programWellTyped_iff` and the profile checker characterizations
give exact executable admission criteria. `checked_type_safety` and
`profile_checked_type_safety` establish safety of every finite execution from
accepted closed entries under accepted programs. The checks terminate by
structural recursion on finite syntax; this does not assert program termination.

The [runtime-language contract](runtime-language.md) adopts strict evaluation and
a syntactic relevance profile for machine-written programs. It deliberately
restricts the language rather than adding deferred computation to reproduce the
current compiler's treatment of unused expressions. The profile requires used
binding introductions and complete product patterns; its occurrence checker is
separate from ordinary typing. The compiler does not yet enforce these rules.

The [working agenda](../task.md#current-agenda) records the next proofs,
open design decisions, and remaining language families.  Every extension needs
complete typing and execution rules or a proved expansion, with the corresponding
formation, progress, preservation, executable admission, and uniqueness results.
The [coverage ledger](type-safety-coverage.md) records each family's status.

Extraction-preserves-typing and compiler refinement are separate tracks. They
use the language definition and transfer its results to implementation artifacts;
they do not block completion of the language's own soundness theorem. Physical
ownership implementation should likewise be distinguished from a declarative
ownership/effect discipline, whose soundness is a language-level question.


## Raw structural comparison boundary

`valueEq_eq_true_iff` and `valuesEq_eq_true_iff` characterize equality of the
complete finite raw value or value list. This includes tags, widths, nominal
identities, constructors, field order, and lengths. These are mathematical
operation laws, not source admission or compiler-correctness results. The
comparison accepts raw malformed values as inputs; it does not validate them.
The strict source expression `structEq` requires homogeneous operands in the
independent `EqTy` domain. Its typing, evaluation frames, formation, safety,
relevance, exact inference, and type uniqueness are checked. The domain checker
is exact: `equalitySupported_iff` states
that the checker returns true exactly for the inductively specified domain.


`EqualityCheck.saturate_stable` proves that a monotone, length-preserving
transformer on Boolean tables stabilizes from the all-false table within the
table length. Its proof uses a direct count of true entries. This generic
iteration bound and the equality-specific checker correspondence are checked.
Source-expression integration with the full metatheory is also checked.
`step_structEq_true_iff` and `step_structEq_false_iff` characterize the final
comparison step for arbitrary raw values and continuations.


## Checked renaming and weakening

`Expr.rename` lifts the variable map beneath each binder prefix. Expression,
argument-list, and branch-list congruence, identity, and composition are proved
using pointwise map laws. `RenamingTyped` states forward preservation of typed
context lookups. It lifts beneath one or multiple binders and supports inserting
an arbitrary context. `ExprTyped.rename`, `ArgsTyped.rename`, and
`BranchesTyped.rename` preserve the original result/argument types.
`ExprTyped.weaken` and `weakenUnder` cover insertion before the context or beneath
a preserved prefix.

These are raw typing and syntax results. Public admission still requires
formation of the inserted context. Relevance preservation is checked below.
Operational correspondence is proved under the separate environment relation
below; signature-changing program transformations remain separate obligations.
A forward context map alone does not imply inference
equivalence for originally ill-typed expressions.


`uses_rename_iff` gives the exact existential image of free occurrences under
any map; argument and branch lists have corresponding laws. Protected prefix
indices each have exactly themselves as a preimage under a lifted map. Hence
`parametersUsed_rename_liftN` preserves usage of that prefix, and
`admissible_rename` (with list counterparts) proves exact Boolean invariance of
internal relevance. `ProfileTyped.rename` and `.weaken` combine those results
with typing preservation. None of these results makes newly inserted parameters
used, proves a signature change safe, or establishes runtime equivalence.


`EnvCorresponds mapping source target` requires equality of every raw lookup,
including missing entries, after applying the map. Its identity, empty,
composition, lifting, prefix, and insertion laws are checked.
`renameBranches_lookup` preserves selected position, arity, and absence.
These support laws use no axioms. They are independent of type-context transport:
a raw sum value may inhabit more than one sum type.

`FrameCorresponds`, `KontCorresponds`, and `StateCorresponds` relate raw
configurations. Each suspended frame retains its own map and corresponding
environment; stored values and metadata agree exactly. Fresh calls use identical
argument lists and unchanged program bodies, under the identity map.
`StateCorresponds.step` relates the actual optional successor results, including
absence on both sides. Terminality and stuckness are equivalent; the overflow
terminal predicate is unchanged.

`steps_forward` and `steps_backward` transfer arbitrary finite traces using the
same oriented relation, without assuming an inverse variable map. The public
`rename_returns_iff`, `rename_overflows_iff`, and `rename_reaches_stuck_iff` compare
expressions under corresponding environments and initially empty continuations.
They give equivalence of each exact returned value, each exact tagged overflow
record, and finite stuck reachability. No typing, termination, injectivity, or
compiler assumption appears in these theorems. The same program table is used
on both sides.


## Checked continuation decomposition

`State.appendKont` appends a suffix to existing evaluation/return frames and
leaves overflow records unchanged. `step_appendKont_of_not_boundary` gives exact
optional-step correspondence under `¬ ReturnBoundary state`, where the boundary
is exactly an empty-stack return. `Step.appendKont` and `Steps.appendKont`
preserve successful transitions and finite traces without that extra premise.
`steps_appendKont_decompose` splits any finite combined trace into a source
prefix that has not reached the value-return boundary, or a source return
followed by a continuation trace.

`appendKont_returns_iff` characterizes exact returned values through an
intermediate source value. `appendKont_overflows_iff` and
`appendKont_reaches_stuck_iff` distinguish failure before a source return from
failure afterward in the continuation. All statements are raw, same-program
facts without typing or termination premises. Overflow-record reachability does
not remove the separate validity condition in `Terminal`.


`Steps.head_iff` decomposes a finite execution at its first transition.
`steps_from_no_step_iff` characterizes executions beginning at a state with no
successor. Given a known first step and a no-successor endpoint,
`steps_iff_of_step_to_no_step` removes or restores that step using determinism.
The `sequence_returns_iff`, `sequence_overflows_iff`, and
`sequence_reaches_stuck_iff` corollaries combine first-step inversion with the
continuation equations. Their premises include the actual operand transition;
they impose no typing or termination assumption.
