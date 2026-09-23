# Independent core type safety

Track 1 establishes operational type safety for an independent first-order core.
The work is on `typesafety`, starting from compiler revision
`a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`. The root [development plan](../plan.md)
owns the remaining work; the [journal](../plans/type-safety-journal.md) records
proof and verification history.

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

The core has Unit, Bool, bounded natural numbers, products, binary sums,
variables, let bindings, conditionals, projections, complete product patterns,
Unit elimination, sum case analysis, checked addition, and direct first-order
calls with arbitrary finite argument lists, persistent homogeneous arrays, and
nominal recursive data with strict construction and exhaustive matching.
Expressions, values, and machine states are ordinary untyped data. Separate
inductive judgments describe their types. Natural literals and natural values
must be below `2^64` when typed; addition uses this bounded-natural interpretation,
not modular unsigned arithmetic.

Evaluation is a deterministic, left-to-right call-by-value machine with explicit
lexical environments and continuations. Pairs and call arguments are strict;
only the selected conditional or sum branch executes. A let binding or sum-case
payload is prepended to the lexical environment at variable index zero. Calls
start with a fresh environment: index zero denotes the first argument, index one
the second, and so on. Suspended continuations retain the caller bindings they
need. These conventions specify this core, not Lean's imported-expression format.

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

A successful addition returns the mathematical sum. An overflowing addition
terminates with both operands recorded. `Terminal` admits only a final return
or overflow of two bounded operands whose sum is at least `2^64`. Missing
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
| `overflow_is_justified` | A reached overflow contains bounded operands whose mathematical sum exceeds the representation. |
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
| [Core.lean](../LeanExe/TypeSafety/Core.lean) | Syntax, extrinsic expression and program typing, typed environments, lookup, and canonical forms. |
| [ArrayValues.lean](../LeanExe/TypeSafety/ArrayValues.lean) | Pure checked array operations, failure/result/length/read laws, and primitive typing. |
| [Machine.lean](../LeanExe/TypeSafety/Machine.lean) | Executable transitions, typed frames and continuations, state typing, and determinism. |
| [Safety.lean](../LeanExe/TypeSafety/Safety.lean) | Progress, preservation, finite-execution safety, result typing, and overflow justification. |
| [Profile.lean](../LeanExe/TypeSafety/Profile.lean) | Syntactic admission checks, their characterizations, and profile safety. |
| [Typing.lean](../LeanExe/TypeSafety/Typing.lean) | Total inference, exact admission checks, type uniqueness, and checker-to-safety corollaries. |
| [TypeSafety.lean](../LeanExe/TypeSafety.lean) | Independent import target. |

Run the maintained [verification gate](../tools/type-safety.js):

```sh
tools/type-safety.js check
```

The gate checks the version against `lean-toolchain`, builds only the independent
`LeanExe.TypeSafety` target, checks [26 core examples](../test/type_safety.lean),
[41 profile examples](../test/type_safety_profile.lean),
[46 array examples](../test/type_safety_arrays.lean),
[57 nominal-data examples](../test/type_safety_data.lean), and
[65 typing-checker examples](../test/type_safety_typing.lean). It audits the
transitive axiom dependencies of all 120 declared theorems across the seven
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

The complete gate passed on 2026-09-23 with exact Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Each audited theorem depends on no
axioms or only Lean's standard propositional extensionality axiom, `propext`.
There are no proof holes, added axioms, unsafe definitions, or native-evaluation proof shortcuts in
these modules. This remains a proof checked by Lean's kernel and standard
foundation, not a proof of the kernel's consistency.

Every Lean invocation goes through `tools/leanrun` with a timeout and the shared
process lock. The user explicitly authorized local execution without systemd
cgroups for this development session, using `LEANRUN_LOCAL=1`. That authorization
does not change the default resource policy for other sessions. An explicitly
installed pinned toolchain can be selected with `LEANRUN_TOOLCHAIN`.

## Boundary and next work

This result does not establish termination, absence of arithmetic overflow,
source extraction correctness, ownership safety, or WebAssembly correctness.
There is no claim that existing accepted LeanExe programs have been translated
into this core. Fixed-width modular operations, other arithmetic, additional
array operations, byte arrays, dependent indexed data, physical heaps, and
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

The independent language agenda is:

1. Specify declarations, type formation, binders, execution order, sharing, and
   explicit permitted failures. Replace schematic fold and recursion families
   with complete rules, or define and justify their expansion into core forms.
2. Extend abstract values and primitive semantics to the intended language:
   fixed-width integers, remaining natural operations, arrays, bytes, nominal
   structures and variants, recursive data, and collection/control operations.
   Primitive signatures alone are insufficient; prove primitive progress and
   preservation for the defined behavior.
3. Prove the corresponding canonical forms, binding lemmas, state invariants,
   preservation, progress, and reachable-state safety in checked increments.
4. Give runtime counter reads and explicit release their own abstract-state and
   admissibility rules if included in the language claim. Ordinary array typing
   alone does not express permission to release or exclude use after release.
5. Preserve the checked algorithmic typing correspondence and type uniqueness
   with every language extension. Keep termination and successful, failure-free
   execution as separate results.

The first persistent-array increment is checked. Additional collection forms
such as replication, slicing, folds, and early-exit loops still require complete
rules or proved expansions into this core. Growth must preserve representable
lengths or return a specified failure. Monomorphic nominal recursive data is now
checked, as are explicit sum annotations and algorithmic typing. The next
increment specifies the remaining bounded-natural operations and their failure
conditions, then extends the checked semantics and metatheory.

Extraction-preserves-typing and compiler refinement are separate tracks. They
use the language definition and transfer its results to implementation artifacts;
they do not block completion of the language's own soundness theorem. Physical
ownership implementation should likewise be distinguished from a declarative
ownership/effect discipline, whose soundness is a language-level question.
