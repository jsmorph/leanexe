# Restricted Lean to Talos module correctness

Compile ordinary restricted Lean definitions to Talos `Wasm.Module` values.
Prove that the generated module preserves the original Lean computation.
Include recursive functions, ordinary bounded loops, and byte memory. Floating
point and GPU are excluded. I/O is deferred. The existing verified encoder owns
the module-to-binary step.

Work on `correct`; commit and push checked increments. Run focused Lean targets
through `tools/leanrun` in the user's authorized local mode, one process at a time.

## Checked implementation

- `LeanExe/Core/Program.lean` defines the internal statement language and execution
  relation: assignment, sequencing, conditions, loops, direct recursive calls,
  and primitive state operations.
- `Project/Core/Correctness.lean` proves execution preservation in Talos for every
  source evaluation and invocation, including recursive call trees and loops.
- `LeanExe/Core/Extract.lean` compiles ordinary Lean definitions and generates
  kernel-checked correspondence proofs using their unfolding equations and
  functional induction. The original function is named in each theorem.
- `Project/Core/Compiler.lean` returns a Talos module with native correctness,
  module validity, and encoder readiness. Source bounds, call signatures, and
  binary size limits are checked automatically.
- `LeanExe/Core/Memory.lean` provides ordinary `StateM ByteArray UInt64` read,
  write, size, and growth. Reads outside memory return zero; writes outside
  memory do nothing. Growth appends zero bytes or reports failure without
  changing memory. Addresses and values are UInt64; writes retain the low byte.
- `Project/Core/MemoryRuntime.lean` supplies four proved Talos implementations.
  `MemoryCompiler.lean` composes them with generated native state certificates.
  Its theorem preserves the original Lean return value and all final bytes.
- The initial sixteen zero-filled pages of the generated memory module satisfy
  the representation theorem. General inputs use page-aligned byte arrays of at
  most 4 GiB and the module's 65536-page growth limit.
- `LeanExe/Core/NativeLoop.lean` proves ordinary finite range iteration agrees
  with an internal loop, given the generated guard and body correspondence.
  Termination follows from the range length, without a separate termination
  assumption.
- `NativeRangeFunction.lean` proves the concrete generated range helper. The
  frontend connects ordinary `for` expressions to this helper, including nested
  loops, recursive helper calls inside loops, and recursion after a loop.
- `Project/Core/Frontend.lean` exposes `Frontend.compile` and
  `Frontend.compileState`. Each produces an actual named Talos module and its
  `entry`, `correct`, `valid`, and `ready` declarations. It requires no source
  annotations, custom syntax, or registration.

## Checked examples

`LeanExe/Core/Examples.lean` generates certificates for arithmetic, let,
conditionals, Euclidean recursion, two-call non-tail recursion, named helper
composition, shared helpers, Boolean comparison against false, and a constant
with no arguments.

`LeanExe/Core/StateExamples.lean` generates certificates for byte sums, copying,
growth with size, recursive writes, a zero-argument state program, and a
read-dependent branch that writes different bytes in its two branches.

`LeanExe/Core/LoopExamples.lean` generates certificates for ordinary pure and
stateful loops, nested loops, loops calling recursive helpers, and recursion
after a loop.

`Project/Core/Examples.lean` and `Project/Core/StateExamples.lean` instantiate
complete native-to-Talos correctness and module acceptance. Recursive writes
also have a theorem starting from the generated module's actual initial store.
Their checked axiom dependencies are `propext`, `Classical.choice`, and
`Quot.sound`; no admitted proof or custom axiom is used.

`Project/Core/FrontendExamples.lean` checks the public entry points on original
recursive and stateful Lean definitions. `Project/Core/LoopExamples.lean` checks
pure and stateful loops through that interface and checks all three loop/recursion
compositions through the complete compiler. All generated modules carry native
correctness, validity, and encoder readiness. These checks pass with the same
three standard axiom dependencies.

## Supported boundary

Ordinary monomorphic Lean definitions use UInt64 parameters, runtime bindings,
and results; stateful definitions return `StateM ByteArray UInt64`. Arithmetic,
bit operations, conditions, let, do, named helpers, and terminating self-recursion
are supported. Data can be represented explicitly in words and byte memory.

Ordinary bounded loops use `[:bound.toNat]`, start at zero, advance by one, and
carry one mutable UInt64 accumulator. There is no early break. Mutual recursive
groups and calls from a loop body back to its enclosing function are rejected;
loops may call independently recursive helpers. Unsupported syntax or a failed
correspondence proof causes compilation to fail.

See `LeanExe/Core/README.md` for usage, memory assumptions, and the precise proof
boundary. The theorem establishes successful Talos execution with sufficient
finite fuel; it does not impose a fixed execution budget.

## Status

The restricted compiler is proved from original Lean computation to the emitted
Talos module. The ordinary-loop connection, dynamic state conditions, and
complete module checks all pass. No compiler-proof work remains for the subset
specified above. I/O remains deferred; floating point and GPU remain excluded.

Focused validation:

```sh
tools/leanrun --timeout 60 lake build LeanExe.Core.StateExamples LeanExe.Core.LoopExamples
tools/leanrun --timeout 60 lake -d proofs/talos/lean build Project.Core.FrontendExamples Project.Core.LoopExamples Project.Core.StateExamples Project.Core.Examples
```

The existing verified encoder owns the subsequent binary step. Do not add source
syntax, registration mechanisms, proof archives, or unrelated tooling.
