# LeanExe Language Specification

## Purpose

LeanExe defines a restricted executable subset of Lean 4 for extraction to WebAssembly.  Lean remains the parser, elaborator, type checker, and proof checker.  The compiler consumes checked declarations from a Lean environment and rejects declarations outside the supported subset.

The subset targets traditional pure programming first: validators, parsers, encoders, finite decision procedures, and deterministic byte-oriented transforms.  The design also reserves a path for modeled effects, including a restricted `IO` fragment.  Effect support must enter the core IR explicitly, because an extracted Wasm module cannot inherit Lean’s runtime behavior without making that runtime part of the trusted base.

## Status Terms

| Status | Meaning |
| ------ | ------- |
| Implemented | The repository contains code that accepts or emits this feature today. |
| Reported | The repository can inspect checked Lean declarations and classify this feature, but it does not compile it. |
| Planned | The design admits the feature, but the implementation does not accept it. |
| Rejected | The feature is outside the intended subset unless this document changes. |

Current implementation is narrow.  It compiles `LeanExe.Examples.AsciiDigits.validate : ByteArray -> Bool` through a hand-written core IR path and emits a standalone Wasm validator.  It also compiles `LeanExe.Examples.Collatz.steps : UInt64 -> UInt64` through a hand-written Wasm path with a `10000`-step fuel bound.  The generic report imports arbitrary built modules through `lean-wasm report --module <module> --entry <name>`.

## Source Boundary

The compiler reads checked Lean declarations from a Lean environment.  It does not parse Lean syntax, elaborate terms, resolve overloads, or trust source text.  A declaration enters the compiler only after Lean has accepted the module that contains it.

An entry point is a named Lean constant with a closed type after specialization.  The compiler computes the runtime-relevant dependency graph from the entry point’s checked value and type.  Proof-only dependencies may be erased, but executable dependencies must either compile or receive an exact rejection reason.

The current report imports compiled `.olean` modules through Lean’s module loader.  It expands declarations whose root namespace matches the imported module root and records other dependencies as an external frontier.  This frontier prevents the first report from recursively expanding Lean’s standard library and names every external constant that blocks generic extraction.

## Values and Types

| Lean feature | Intended support | Current implementation |
| ------------ | ---------------- | ---------------------- |
| `Unit` | Planned | Reported only |
| `Bool` | Implemented | Implemented for the demo validator |
| `UInt8` | Implemented | Implemented for the demo validator |
| `UInt32` and `UInt64` | Planned | `UInt64` implemented for the Collatz demo path and otherwise reported only |
| `Nat` | Planned for bounded static use | Reported only |
| `ByteArray` | Implemented | Implemented for `ByteArray -> Bool` entry shape |
| Structures | Planned | Reported only |
| Simple inductives | Planned | Reported only |
| `Option` | Planned | Reported only |
| `Except` | Planned | Reported only |
| `Array` | Planned with explicit layout rules | Reported only |
| `String` | Planned only after byte-oriented APIs stabilize | Reported only |
| Propositions and proofs | Intended for erasure | Proofs are used in Lean and omitted from Wasm emission |
| Type parameters | Planned through monomorphization | Reported only |
| Typeclasses | Planned through static specialization | Reported only |

`Nat` needs careful treatment because Lean’s `Nat` is unbounded, while the first Wasm target uses fixed-width machine integers and explicit memory.  The subset may admit `Nat` in proofs, sizes, indices, and compile-time constants before it admits general unbounded runtime arithmetic.  Any accepted runtime `Nat` operation must state its representation and overflow behavior.

## Terms

| Lean term form | Intended support | Current implementation |
| -------------- | ---------------- | ---------------------- |
| Variables and local lets | Planned | Reported only |
| Named calls | Planned | Reported in the dependency graph and hard-coded for the demo paths |
| Constructors | Planned | Reported only |
| Projections | Planned | Reported only |
| Pattern matching | Planned | Lowered only for the demo range check path |
| `if` expressions | Planned | Reported only |
| Structural recursion | Planned with termination evidence from Lean | Reported only |
| Tail recursion over buffers or arrays | Planned | Reported only |
| Higher-order arguments | Planned later with escape restrictions | Rejected for compilation |
| General closures | Planned later | Rejected |
| Quotients and proof irrelevance dependencies | Rejected for executable content | Rejected |
| `unsafe` definitions | Rejected | Rejected |
| Opaque executable constants | Rejected unless implemented as primitives | Rejected |

The first accepted term language should resemble a first-order functional IR rather than Lean’s full expression language.  It should contain variables, lets, calls, constructors, projections, case analysis, loops, and primitive byte and integer operations.  Each accepted Lean construct must translate to that IR without consulting Lean runtime objects at execution time.

## Effects

| Effect form | Intended support | Current implementation |
| ----------- | ---------------- | ---------------------- |
| Pure functions | Implemented in the demo path | Implemented for `ByteArray -> Bool` |
| `Option` and `Except` | Planned as explicit result values | Reported only |
| Panic or partial operations | Rejected unless eliminated or modeled | Rejected for compilation |
| Lean `IO` | Planned later as an explicit capability subset | Reported only |
| File access | Planned later under explicit host imports | Reported only |
| Environment variables | Planned later under explicit host imports | Reported only |
| Time and randomness | Planned later only with modeled nondeterminism | Reported only |
| Concurrency | Rejected for the first effectful subset | Rejected |
| Arbitrary FFI | Rejected | Rejected |

Initial `IO` support should be small and explicit.  A future effectful IR should represent operations such as reading a file, writing bytes, reading an environment variable, or returning an error as operations with declared host imports.  The compiler must reject hidden runtime access, ambient nondeterminism, and capabilities that the Wasm module signature does not declare.

## Dependency Classification

The extractor classifies each reachable declaration from the entry point.  Runtime declarations contain executable content that affects the output value.  Proof declarations inhabit propositions or erased fields and may appear in the checked environment without entering the Wasm program.

The report must name every rejected declaration and the first unsupported construct found in it.  Useful rejection reasons include opaque constant, unsupported primitive, unsupported type, higher-order value escape, unspecialized polymorphism, typeclass argument that cannot be specialized, unsupported recursor, unsupported effect, `unsafe` declaration, and runtime environment dependency.  A rejection reason is part of the user-facing API and should remain stable enough for tests.

The current report implements module loading, entry lookup, root-namespace dependency expansion, external frontier classification, entry-shape classification, and effect detection for `IO`, `EIO`, `BaseIO`, and `Task`.  It reports polymorphic declarations, typeclass instance dependencies, library operations, numeric literals, decidable propositions, and bounded `Nat` use as pending extraction work.  It rejects `unsafe`, `partial`, opaque executable constants, axioms in executable dependency graphs, quotients, higher-order arguments, unsupported effects, and external constants without a LeanExe primitive.

## Current Wasm ABI

The current validator module exports one linear memory, `alloc`, `reset`, and `validate`.  The host writes input bytes into memory, calls `validate(ptr, len)`, and receives `0` or `1`.  The arena begins at byte offset `4096` and resets per call.  The current Collatz module exports `collatz_steps(n: i64) -> i64` and uses no linear memory.

Structured outputs are planned after `Except` and simple inductive values enter the core IR.  Pointer-length pairs should encode byte output, while arena-allocated tagged layouts should encode small inductives and parser results.  Host imports must remain explicit in the Wasm module.

## Correctness Obligations

The compiler should maintain separate correctness claims for extraction, proof erasure, specialization, lowering, and Wasm emission.  The current repository proves a small source-to-core equality for the demo validator and a lowering lemma for the byte-range validator.  It also tests the emitted Wasm against Lean evaluation through a differential harness.

Future proofs should compose toward `compile_correct`, relating the modeled Wasm execution to the checked Lean function for accepted entry points.  The final theorem should state the trusted base: Lean’s kernel and admitted axioms, the formal semantics of the modeled Wasm subset, the emitter if unverified, the host ABI, the Wasm runtime, and the underlying platform.  Browser, Wasmtime, or Wasmer execution should not be described as formally verified unless the proof includes that runtime.
