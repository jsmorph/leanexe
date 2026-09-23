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
calls with arbitrary finite argument lists, and persistent homogeneous arrays.
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

Function bodies are checked against a fixed signature table. `ProgramTyped`
requires exactly one body per declared signature, checked under its parameter
types and the same global table. Calls must supply exactly the declared argument
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

This evaluation strategy belongs to this core. Connecting demand-based LeanExe
extraction to it requires a separate theorem. The core does not import the
extractor, diagnostic IR evaluator, emitter, or Talos.

## Proved results

The principal closed-term theorem, `closed_type_safety`, has the shape:

```lean
ProgramTyped program signatures →
ExprTyped signatures [] expr τ →
Steps program (initial expr) final →
StateTyped signatures final τ ∧ ¬ Stuck program final
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
| [Core.lean](../LeanExe/TypeSafety/Core.lean) | Syntax, extrinsic expression and program typing, typed environments, lookup, and canonical forms. |
| [ArrayValues.lean](../LeanExe/TypeSafety/ArrayValues.lean) | Pure checked array operations, failure/result/length/read laws, and primitive typing. |
| [Machine.lean](../LeanExe/TypeSafety/Machine.lean) | Executable transitions, typed frames and continuations, state typing, and determinism. |
| [Safety.lean](../LeanExe/TypeSafety/Safety.lean) | Progress, preservation, finite-execution safety, result typing, and overflow justification. |
| [Profile.lean](../LeanExe/TypeSafety/Profile.lean) | Syntactic admission checks, their characterizations, and profile safety. |
| [TypeSafety.lean](../LeanExe/TypeSafety.lean) | Independent import target. |

Run the maintained [verification gate](../tools/type-safety.js):

```sh
tools/type-safety.js check
```

The gate checks the version against `lean-toolchain`, builds only the independent
`LeanExe.TypeSafety` target, checks [26 core examples](../test/type_safety.lean),
[41 profile examples](../test/type_safety_profile.lean), and
[46 array examples](../test/type_safety_arrays.lean). It audits the transitive
axiom dependencies of seven core results, all 13 profile theorems, and all 32
array operation and list-typing theorems: 52 audits in total.
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
array operations, byte arrays, general recursive data, physical heaps, and
compiler-specific recursion recognizers remain outside the language proved here.

Unannotated sum introductions can have multiple typings because the unused
summand is not specified. Progress and preservation hold for every given typing
derivation; type uniqueness and principal inference are not claimed. A future
checker needs a deliberate annotation or bidirectional-checking design.

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
5. State algorithmic type-checking results against these declarative rules.
   Keep termination and successful, failure-free execution as separate results.

The first persistent-array increment is checked. Additional collection forms
such as replication, slicing, folds, and early-exit loops still require complete
rules or proved expansions into this core. Growth must preserve representable
lengths or return a specified failure. Recursive nominal declarations and an
algorithmic typing discipline remain separate foundational work items.

Extraction-preserves-typing and compiler refinement are separate tracks. They
use the language definition and transfer its results to implementation artifacts;
they do not block completion of the language's own soundness theorem. Physical
ownership implementation should likewise be distinguished from a declarative
ownership/effect discipline, whose soundness is a language-level question.
