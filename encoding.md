# Verified WASM Encoding

## Goal

Implement and prove a WASM binary encoder for the Talos modules produced by
LeanExe.  The required coverage follows LeanExe's compiler output: scalar
integer and floating-point operations, structured control, direct calls,
function imports, globals, exports, and 32-bit linear memory.

Define an independent Lean relation `Encodes m bytes` from the official
[WASM binary specification](https://webassembly.github.io/spec/core/binary/index.html).
Prove that encoding a valid module within the format's size limits succeeds
and produces bytes representing that module.  Compose this theorem with
behavioral proofs about the input module.

## Implementation

The proof proceeds through integer encodings, types, instructions, function
bodies, sections, and complete modules.  Include all instructions in
[the compiler's instruction type](LeanExe/Wasm/Instr.lean), the legacy scalar
emitter, and the function imports used by WASI and ByteIO.  Check vector
counts, indices, UTF-8 byte lengths, body and section sizes, and total local
counts before narrowing integers.

The specification and correctness theorem must preserve the module's function
signatures, indices, local types, control annotations, memory, globals, and
exports.  State representation and size premises independently of encoder
success.  Prove acceptance as well as correctness of successful results.

Use the independent binary rules to connect output bytes to Talos's module
representation.  Run Lean through `tools/leanrun` and audit the public theorems
for axioms.  Test representative compiler output, imports, floating-point
operations, nested control, multiple function results, and integer boundaries.

## Completion

- [x] Define and review the independent binary specification.
- [x] Implement the encoder for LeanExe's emitted WASM.
- [x] Prove correctness and acceptance under independent premises.
- [x] Prove that valid inputs produce valid binaries.
- [x] Connect behavioral proofs to the represented output module.
- [x] Test representative modules and boundary cases.
- [x] Check the complete development in Lean and audit its axioms.

The [encoder documentation](proofs/talos/lean/Project/Encoding/README.md) describes
the API, premises, trusted specification, and test command.  The development
journal records the checks and dependency-build failures.
