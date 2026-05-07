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

Current implementation is narrow.  It compiles `LeanExe.Examples.AsciiDigits.validate : ByteArray -> Bool` through a hand-written core IR path and emits a standalone Wasm validator.  It also has a generic checked-declaration compiler for a first scalar, array, and read-only byte-buffer fragment: monomorphic first-order functions over `UInt64`, `Bool`, bounded `Nat`, `Array UInt64`, and `ByteArray` parameters; internal `UInt8`, `UInt32`, product, and `Option` values over first-fragment values; numeric literals; primitive `UInt64` arithmetic and bitwise operations; boolean equality, unsigned comparisons, negation, short-circuiting conjunction and disjunction; `if`; local `let` expressions over first-fragment value types; lazy inlining for nonrecursive project-local helper calls; demand summaries for strict project-local calls; zero-argument declarations used as constants; array literals, allocation, and replication; array length reads; array reads, writes, pushes, pops, appends, and extracts; copy-on-write array update; `ByteArray.size`; `ByteArray.get!`; and a restricted tail-recursion shape over a decreasing `Nat` fuel argument.  `LeanExe.Examples.AsciiDigits.validateGeneric`, `LeanExe.Examples.ByteArrayPrograms`, `LeanExe.Examples.Collatz`, `LeanExe.Examples.Arithmetic`, `LeanExe.Examples.IntMap`, `LeanExe.Examples.ArraySemantics`, `LeanExe.Examples.Correctness`, `LeanExe.Examples.Let`, and `LeanExe.Examples.Prime` compile through `lean-wasm compile --module <module> --entry <entry> --out <path>`.  The generic report imports arbitrary built modules through `lean-wasm report --module <module> --entry <name>`.

## Source Boundary

The compiler reads checked Lean declarations from a Lean environment.  It does not parse Lean syntax, elaborate terms, resolve overloads, or trust source text.  A declaration enters the compiler only after Lean has accepted the module that contains it.

An entry point is a named Lean constant with a closed type after specialization.  The compiler computes the runtime-relevant dependency graph from the entry point’s checked value and type.  Proof-only dependencies may be erased, but executable dependencies must either compile or receive an exact rejection reason.

The current report imports compiled `.olean` modules through Lean’s module loader.  It expands declarations whose root namespace matches the imported module root and records other dependencies as an external frontier.  The frontier prevents the report from recursively expanding Lean’s standard library and distinguishes implemented primitives from dependencies that still block generic extraction.

## Values and Types

| Lean feature | Intended support | Current implementation |
| ------------ | ---------------- | ---------------------- |
| `Unit` | Planned | Reported only |
| `Bool` | Implemented | Implemented for the demo validator and represented as `0` or `1` in the generic Wasm fragment |
| `UInt8` | Implemented | Implemented for the demo validator and as an internal generic scalar for `ByteArray.get!`, `UInt8` literals, `UInt8.ofNat`, `UInt8.toNat`, `UInt8.toUInt32`, `UInt8.toUInt64`, local lets, project-local helper parameters and results, comparisons, wrapping addition, subtraction, multiplication, `&&&`, `|||`, `^^^`, bitwise complement, and shift operations; `UInt8` entry parameters and results are rejected |
| `UInt32` and `UInt64` | Planned | `UInt64` implemented for the first generic compiler fragment, including wrapping arithmetic, `min`, `max`, `land`, `lor`, `xor`, `&&&`, `|||`, `^^^`, `~~~`, `shiftLeft`, `shiftRight`, `<<<`, `>>>`, `UInt64.ofNat`, `UInt64.toNat`, `UInt64.toUInt8`, `UInt64.toUInt32`, unsigned comparisons, and Lean-compatible division and remainder at zero divisors; `UInt32` is implemented as an internal scalar with literals, `UInt32.ofNat`, `UInt32.toNat`, `UInt32.toUInt8`, `UInt32.toUInt64`, comparisons, wrapping arithmetic, bitwise operations, shifts, `min`, and `max`, while `UInt32` entry parameters and results are rejected |
| `Nat` | Planned for bounded static use | Implemented for fuel arguments, array sizes, and array indices represented as Wasm `i64`; general unbounded runtime arithmetic is unsupported |
| `ByteArray` | Implemented | Implemented in the hand-written validator path and as a read-only generic entry parameter represented by pointer and length ABI slots; construction, mutation, append, slices, and byte-array results are rejected at the generic function type boundary |
| Products | Planned as structured values | Implemented internally for products whose fields are first-fragment values; product entry parameters and product entry results are rejected |
| Structures | Planned | Reported only |
| Simple inductives | Planned | Reported only |
| `Option` | Planned | Implemented internally for first-fragment payload values, including construction, matching, `getD`, `elim`, `map`, `bind`, `isSome`, and `isNone`; `Option` entry parameters and `Option` entry results are rejected |
| `Except` | Planned | Reported only |
| `Array` | Planned with explicit layout rules | Implemented only for `Array UInt64` in the generic fragment, with literals from literal `List.toArray`, `Array.replicate`, `Array.size`, `Array.isEmpty`, indexed reads, `back!`, `getD`, `set!`, `push`, `pop`, `append`, `extract`, length metadata, bounds traps, and copy-on-write update |
| `String` | Planned only after byte-oriented APIs stabilize | Reported only |
| Propositions and proofs | Intended for erasure | Proofs are used in Lean and omitted from Wasm emission |
| Type parameters | Planned through monomorphization | Reported only |
| Typeclasses | Planned through static specialization | Reported only |

`Nat` needs careful treatment because Lean’s `Nat` is unbounded, while the first Wasm target uses fixed-width machine integers and explicit memory.  The subset may admit `Nat` in proofs, sizes, indices, and compile-time constants before it admits general unbounded runtime arithmetic.  Any accepted runtime `Nat` operation must state its representation and overflow behavior.

Runtime `Nat` values in the current fragment use the same `i64` representation as other scalar values.  Runtime `Nat` literals must be below `2^64`; larger literals are rejected rather than truncated unless they are consumed directly by a fixed-width conversion such as `Nat.toUInt64`.  `Nat` subtraction follows Lean’s saturating semantics: `a - b` returns `0` when `a < b`.  `Nat.succ` uses the checked addition path, and `Nat.pred` uses the saturating subtraction path.  `Nat.toUInt64` preserves the bounded runtime representation and lowers large literals modulo `2^64`.  `Nat` addition and multiplication trap when the result exceeds the bounded representation.  `Nat.min` and `Nat.max` lower through unsigned comparisons over the bounded representation.  Programs that rely on arbitrary-precision runtime `Nat` results are outside the current subset.

`UInt32` is an internal scalar type in the current fragment.  The generic fragment represents it as an `i64` constrained to `0..2^32-1`, and exported entries still reject `UInt32` parameters and results.  `UInt32` literals and `UInt32.ofNat` lower modulo `2^32`, `UInt32.toNat`, `UInt32.toUInt64`, and `UInt8.toUInt32` preserve the constrained representation, and `UInt64.toUInt32` masks to 32 bits.  `UInt32.toUInt8` masks to eight bits.  `UInt32` addition, subtraction, and multiplication mask their result to 32 bits.  `UInt32` left shifts mask the shift amount modulo 32 and then mask the result to 32 bits; right shifts mask the shift amount modulo 32.

## Terms

| Lean term form | Intended support | Current implementation |
| -------------- | ---------------- | ---------------------- |
| Variables and local lets | Implemented for the first fragment | Variables and local `let` expressions compile for `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, `ByteArray`, `Array UInt64`, and supported product and `Option` values |
| Named calls | Planned | Nonrecursive project-local helper calls are inlined lazily; remaining supported first-fragment calls are emitted when required |
| Constructors | Planned | Product construction and `Option.none`/`Option.some` construction are implemented internally; other constructors are reported only |
| Projections | Planned | Product `.1` and `.2` projections are implemented internally; other projections are reported only |
| Pattern matching | Planned | Implemented for `Bool` and `Option` values in the generic path and for the demo range check path |
| `if` expressions | Planned | Implemented for supported first-fragment result types |
| Structural recursion | Planned with termination evidence from Lean | Implemented for the current tail-recursion shape over a decreasing `Nat` fuel argument, with explicit base and early-exit result expressions |
| Tail recursion over buffers or arrays | Planned | Implemented for `ByteArray` and array parameters carried through the supported fuel-recursion shape |
| Higher-order arguments | Planned later with escape restrictions | Rejected for compilation |
| General closures | Planned later | Rejected |
| Quotients and proof irrelevance dependencies | Rejected for executable content | Rejected |
| `unsafe` definitions | Rejected | Rejected |
| Opaque executable constants | Rejected unless implemented as primitives | Rejected |

The first accepted term language should resemble a first-order functional IR rather than Lean’s full expression language.  It should contain variables, lets, calls, constructors, projections, case analysis, loops, and primitive byte and integer operations.  Each accepted Lean construct must translate to that IR without consulting Lean runtime objects at execution time.

Local `let` support preserves Lean’s lexical de Bruijn scope with lazy extractor bindings.  A let-bound expression is extracted only when the body demands it, so `let x := bad; (x, y).2` returns `y` without evaluating `bad`, matching Lean evaluation.  Let-bound values may use nested lets, arrays, branches, calls, products, and `Option` values when their types remain inside the first fragment.  Product and `Option` values exist only inside the extractor; product projection and `Option` matching lower by selecting demanded scalar expressions, and the Wasm ABI still exposes only `i64` scalar or pointer values.

Product construction follows Lean’s projection behavior: projecting one field does not force extraction or evaluation of the unused field.  This matters for partial terms such as `(bad, x).2`, where Lean returns `x` without evaluating `bad`.  Product-valued entry parameters and product-valued entry results are rejected until the Wasm ABI has a structured-value representation.

`Option` construction uses an extractor-level tag and payload.  Matching an `Option` value lowers to a conditional over the tag, and only the selected branch contributes to the emitted scalar expression.  `Option.getD`, `Option.elim`, `Option.map`, `Option.bind`, `Option.isSome`, and `Option.isNone` lower through the same tag and payload representation.  `Option.getD` and `Option.elim` evaluate default expressions only for `none`, `Option.map` and `Option.bind` evaluate their functions only for `some`, and tag tests do not evaluate a `some` payload.  The payload of `some bad` is not evaluated when the `some` arm ignores it, and the `some` arm is not evaluated for `none`.  `Option` values cannot cross the current Wasm ABI.

Nonrecursive project-local helper calls are inlined into the caller with lazy argument thunks.  Helpers may use internal `UInt8` parameters and results, represented as scalar Wasm slots, even though exported entries cannot expose `UInt8` in the current ABI.  Strict project-local calls that remain as Wasm calls use demand summaries before their arguments are emitted.  For each helper, the extractor records parameters that the helper may demand and parameters that it must demand when its result is demanded; argument trap analysis expands project-local helper calls through the may-demand summary.  A strict call is rejected when an argument may trap and the callee does not must-demand that parameter.  Recursive summaries are conservative: the fuel parameter is must-demanded, carried parameters are may-demanded, and more precise carried-parameter demand remains planned.

Boolean conjunction and disjunction lower with Lean-compatible short-circuiting.  The emitted Wasm must not evaluate the right-hand side of `true || rhs` or `false && rhs`, because the skipped expression may contain a partial operation such as an out-of-bounds array access.  Proposition-level `And`, `Or`, and `Not` lower for supported conditions with the same branch behavior.  `LT.lt`, `LE.le`, `GT.gt`, and `GE.ge` lower to unsigned `i64` comparisons for `UInt64` and for bounded `Nat` values already admitted into the fragment.  Scalar equality propositions over `Bool`, `UInt8`, `UInt64`, and bounded `Nat` lower to scalar equality.  `Decidable.decide` lowers supported decidable comparisons, scalar equalities, and proposition connectives to `Bool`.  `UInt64` division and remainder follow Lean’s checked behavior at zero divisors: `x / 0` returns `0`, and `x % 0` returns `x`.

The supported recursive loop shape has one decreasing `Nat` fuel parameter followed by first-fragment carried values.  The base arm compiles to the result used when fuel reaches zero.  The successor arm may either tail-call the same recursive handle or use `if cond then exitValue else recursiveCall`; in the latter case, the emitted loop returns `exitValue` when `cond` holds before fuel reaches zero.  The extractor rejects non-tail recursion and successor arms whose recursive branch is not the `else` branch of that shape.

## Arrays

The current generic fragment represents `Array UInt64` as an `i64` byte offset into Wasm linear memory.  The pointer addresses an array header.  Offset `0` stores the length as `i64`, and element `i` is stored at byte offset `8 * (i + 1)`.  Array literals lower when Lean elaborates them as `List.toArray` over a literal `List UInt64`; general `List` values remain unsupported.  `Array.replicate n v` allocates the header and `n` eight-byte cells from a module-global bump pointer; zero replication uses zero-initialized memory, while nonzero replication emits a fill loop.

`Array.size` lowers to a header load, and `Array.isEmpty` compares that size with zero.  `Array.get!Internal`, `GetElem?.getElem!`, and `Array.back!` lower to a bounds check followed by `i64.load`.  If the index is out of bounds, the emitted Wasm executes `unreachable`, matching the panic behavior of ordinary Lean execution for `a[i]!` and empty `back!`.  `Array.getD` evaluates the array and index once, returns the loaded element when the index is in bounds, and evaluates the default branch only when the index is out of bounds.  `Array.set!` evaluates its array, index, and value arguments, checks the index, allocates a fresh array, copies every cell, writes the replacement element, and returns the new pointer.  `Array.push` allocates a fresh array with length `oldLen + 1`, copies the old cells, writes the new element at `oldLen`, and returns the new pointer.  `Array.pop` returns the original pointer for an empty array; otherwise, it allocates a fresh array with length `oldLen - 1` and copies the retained prefix.  `Array.append` evaluates both arrays once, allocates a fresh array with length `left.size + right.size`, copies the left cells first, and copies the right cells after them.  `Array.extract` evaluates the array, start, and stop once, clamps stop to the source length, returns an empty array when the effective stop is not greater than start, and otherwise copies the selected slice.  Existing aliases therefore continue to observe the old array.

Resizing, polymorphic arrays, nested arrays, and arrays of structures or inductives are unsupported.  The copy-on-write lowering is semantically conservative and slow.  A future linear array optimization must have a checker that rejects aliasing patterns before using in-place update.

## Byte Arrays

The generic fragment represents an entry `ByteArray` parameter as two Wasm `i64` parameters: a byte pointer and a byte length.  Inside the extractor, that pair remains one structured value, so a Lean function still has one `ByteArray` parameter and helper calls receive the same source-level value.  `ByteArray.size` returns the length slot, `ByteArray.isEmpty` compares that length with zero, and `ByteArray.get! input index` and `input[index]!` lower to a bounds check followed by `i32.load8_u` and zero extension to the fragment’s scalar `i64` representation.

`ByteArray.get!` produces an internal `UInt8` value.  The generic fragment represents that value as an `i64` constrained to `0..255`.  `UInt8` literals and `UInt8.ofNat` lower modulo `256`, matching Lean’s checked semantics, and `UInt8.toNat` is representation-preserving inside the bounded `Nat` fragment.  `UInt8` addition, subtraction, and multiplication mask their result to eight bits.  `UInt8` left shifts mask the shift amount modulo eight and then mask the result to eight bits; right shifts mask the shift amount modulo eight.  `UInt8` division and remainder use the same zero-divisor behavior as Lean: `x / 0` returns `0`, and `x % 0` returns `x`.

The current support is read-only.  Hosts write input bytes into exported memory before calling the entry function; generic modules export `alloc(len)` and `reset()` so the host can place byte inputs in the same bump arena used by compiled array allocation.  `LeanExe.Examples.AsciiDigits.validateGeneric : ByteArray -> Bool` exercises this path through `lean-wasm compile`; the older `validate` declaration remains the proof-oriented source for the hand-written validator path.

## Effects

| Effect form | Intended support | Current implementation |
| ----------- | ---------------- | ---------------------- |
| Pure functions | Implemented in the demo and generic paths | Implemented for scalar, array, product, `Option`, and read-only `ByteArray` fragments described above |
| `Option` and `Except` | Planned as explicit result values | `Option` implemented internally for pure first-fragment code; `Except` reported only |
| Panic or partial operations | Rejected unless eliminated or modeled | Array bounds failures are modeled as Wasm traps; general panic remains unsupported |
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

The current validator module exports one linear memory, `alloc`, `reset`, and `validate`.  The host writes input bytes into memory, calls `validate(ptr, len)`, and receives `0` or `1`.  The arena begins at byte offset `4096` and resets per call.  Generic CoreWasm modules export one 16-page linear memory, `alloc(len : i64) -> i64`, `reset()`, and the requested entry function.  Their arena also begins at byte offset `4096`.  Entry short names `memory`, `alloc`, and `reset` are reserved by the runtime ABI and are rejected.  Scalar values, booleans, bounded `Nat` values, and array pointers cross the ABI as `i64`, while a `ByteArray` parameter crosses as two `i64` values, `ptr` and `len`.

Flattened parameters keep source order: a `ByteArray` parameter contributes its `ptr` and `len` slots at its source position, and scalar parameters stay in their source positions around those two slots.  The byte-array allocation harness tests byte-array parameters before and after scalar parameters.  Structured outputs are planned after `Except` and simple inductive values enter the core IR.  Pointer-length pairs should encode byte output, while arena-allocated tagged layouts should encode small inductives and parser results.  Host imports must remain explicit in the Wasm module.

## Correctness Obligations

The compiler should maintain separate correctness claims for extraction, proof erasure, specialization, lowering, and Wasm emission.  The current repository proves a small source-to-core equality for the demo validator and a lowering lemma for the byte-range validator.  The first generic compiler fragment does not yet prove source-to-IR equivalence.  The repository tests the emitted Wasm against Lean evaluation through direct Wasmtime runs, generic ByteArray WAST checks, and the validator differential harness.

Future proofs should compose toward `compile_correct`, relating the modeled Wasm execution to the checked Lean function for accepted entry points.  The final theorem should state the trusted base: Lean’s kernel and admitted axioms, the formal semantics of the modeled Wasm subset, the emitter if unverified, the host ABI, the Wasm runtime, and the underlying platform.  Browser, Wasmtime, or Wasmer execution should not be described as formally verified unless the proof includes that runtime.
