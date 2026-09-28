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

## Checked examples

`LeanExe/Core/Examples.lean` generates certificates for arithmetic, let,
conditionals, Euclidean recursion, two-call non-tail recursion, named helper
composition, shared helpers, Boolean comparison against false, and a constant
with no arguments.

`LeanExe/Core/StateExamples.lean` generates certificates for byte sums, copying,
growth with size, recursive writes, and a zero-argument state program.

`Project/Core/Examples.lean` and `Project/Core/StateExamples.lean` instantiate
complete native-to-Talos correctness and module acceptance. Recursive writes
also have a theorem starting from the generated module's actual initial store.
Their checked axiom dependencies are `propext`, `Classical.choice`, and
`Quot.sound`; no admitted proof or custom axiom is used.

## Remaining work

1. Finish native proof generation for conditions depending on a value read from
   memory. The `updateByte` example currently exposes this missing case.
2. Connect ordinary bounded `for` loops to the frontend. The generic semantic
   proof passes, but extraction and generated body proofs are still being added.
3. Check pure and stateful looping examples through generated certificates,
   module validity/readiness, and native-to-Talos correctness.
4. Review the resulting restricted dialect and theorem statements, update this
   file with the exact supported boundary, and push the finished work.

Do not describe the compiler as complete before the ordinary-loop connection
and the dynamic state-condition case pass. Do not add source syntax,
registration mechanisms, proof archives, or unrelated tooling.
