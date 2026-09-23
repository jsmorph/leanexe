# Independent core type safety

Track 1 develops a mechanized operational type-safety result for an independent
first-order core. The work is on `typesafety`, starting from compiler revision
`a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`. The root [development plan](../plan.md)
owns the remaining work.

## Scope

The first core has Unit, Bool, bounded natural numbers, products, binary sums,
variables, let bindings, conditionals, projections, case analysis, and checked
addition. Expressions and values are untyped syntax with separate typing
judgments. Natural literals and natural values must be below `2^64` when typed.

Evaluation will use a left-to-right call-by-value machine with explicit lexical
environments and continuations. Variable zero is the most recent binding.
Environment lookup and continuation-typing lemmas take the role of substitution
lemmas in this presentation. A successful addition returns the mathematical sum;
overflow is a named terminal failure. Missing variables and ill-shaped operands
have no transition and must be excluded by progress, rather than converted into
an accepted failure.

This evaluation strategy belongs to this core. Connecting demand-based LeanExe
extraction to it requires a separate theorem. The core does not import the
extractor, diagnostic IR evaluator, emitter, or Talos.

## Checked implementation

| Module | Content |
|--------|---------|
| [Core.lean](../LeanExe/TypeSafety/Core.lean) | Untyped syntax, extrinsic typing, typed environments, lookup, and canonical forms. |
| [Machine.lean](../LeanExe/TypeSafety/Machine.lean) | Executable step function, typed frames and continuations, configuration typing, and determinism. |
| [Safety.lean](../LeanExe/TypeSafety/Safety.lean) | Preservation, progress, finite-execution safety, result typing, and overflow justification. |
| [TypeSafety.lean](../LeanExe/TypeSafety.lean) | Independent import target. |

The initial core and its safety proofs passed `lake build LeanExe.TypeSafety`
through the repository runner on exact Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, on 2026-09-23. Focused behavioral
examples and the automated axiom audit are the next verification milestone.

## Theorem boundary

The proved result is that every configuration reachable from a well-typed
expression in a matching environment remains well typed and either can step,
returns a value of its result type, or reaches the specified addition-overflow
failure. The proof establishes type preservation and progress for the actual
core transitions, rather than assuming them as primitive-operation contracts.

Direct function calls, fixed-width modular arithmetic, arrays, general recursive
data, physical heaps, ownership analysis, source extraction, and WebAssembly
lowering are outside this first milestone. Type safety alone does not assert
termination, absence of arithmetic overflow, compiler correctness, or logical
consistency of Lean. There is no claim that existing accepted LeanExe programs
have been translated into this core.

## Verification policy

Use the exact toolchain in `lean-toolchain`. Every repository verification command
uses `tools/leanrun`; Lean processes remain serialized. The user authorized local
Lean execution without systemd cgroups for the current development session, so
the runner's explicit `LEANRUN_LOCAL=1` mode is permitted for this session. This
does not change the repository's default resource policy for other sessions.

Proof checks must report their actual result. A source checkpoint is not a
kernel-checked theorem until the relevant target succeeds. The completed gate
will build this independent target, check behavioral examples, and audit the
public theorem dependencies for proof holes and unexpected axioms.
