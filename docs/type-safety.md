# Independent core type safety

Track 1 establishes operational type safety for an independent first-order core.
The work is on `typesafety`, starting from compiler revision
`a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`. The root [development plan](../plan.md)
owns the remaining work; the [journal](../plans/type-safety-journal.md) records
proof and verification history.

## Language and execution

The core has Unit, Bool, bounded natural numbers, products, binary sums,
variables, let bindings, conditionals, projections, case analysis, checked
addition, and direct first-order calls with arbitrary finite argument lists.
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
| [Machine.lean](../LeanExe/TypeSafety/Machine.lean) | Executable transitions, typed frames and continuations, state typing, and determinism. |
| [Safety.lean](../LeanExe/TypeSafety/Safety.lean) | Progress, preservation, finite-execution safety, result typing, and overflow justification. |
| [TypeSafety.lean](../LeanExe/TypeSafety.lean) | Independent import target. |

Run the maintained [verification gate](../tools/type-safety.js):

```sh
tools/type-safety.js check
```

The gate checks the version against `lean-toolchain`, builds only the independent
`LeanExe.TypeSafety` target, checks [26 semantic examples](../test/type_safety.lean),
and audits the transitive axiom dependencies of all seven public theorems listed
above. Missing audit results or any axiom other than `propext` fail the gate.
Behavior checks and the audit run with warnings treated as errors. The examples
exercise lexical capture, both sum branches, branch selection, strict pairs,
addition boundaries, malformed states, argument order, exact arity, fresh callee
environments, caller continuation restoration, and a typed recursive self-loop.
They complement the universal theorems by checking the intended semantics.

The complete gate passed on 2026-09-23 with exact Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Each audited theorem depends only on
Lean's standard propositional extensionality axiom, `propext`. There are no proof
holes, added axioms, unsafe definitions, or native-evaluation proof shortcuts in
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
into this core. Fixed-width modular operations, other arithmetic, arrays, byte
arrays, general recursive data, physical heaps, and compiler-specific recursion
recognizers remain outside the language proved here.

Unannotated sum introductions can have multiple typings because the unused
summand is not specified. Progress and preservation hold for every given typing
derivation; type uniqueness and principal inference are not claimed. A future
checker needs a deliberate annotation or bidirectional-checking design.

The next core extension is abstract persistent arrays, with explicit decisions
about bounds failures and evaluation order before adding the typing rules and
proof cases. A separate extraction-preserves-typing theorem must connect accepted
source declarations to the independent core; operational correspondence must
also justify the relationship between extraction's demand behavior and this
core's strict evaluation. Heap representation and compiler simulation can then
state their own invariants against that source semantics.
