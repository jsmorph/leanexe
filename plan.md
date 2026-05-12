## Plan: Verified Lean-to-Wasm Extraction Compiler

Build a compiler that takes **checked Lean definitions** from a restricted executable subset and emits **portable WebAssembly**.  The goal is not to replace Lean’s general compiler.  The goal is to compile selected Lean programs, especially parsers, validators, serializers, protocol checkers, and finite decision procedures, into small Wasm modules with a clear correctness story.

The central claim should be:

```lean
theorem compile_correct :
  ∀ input,
    WasmModel.run (compile f) input = f input
```

This theorem may initially target an internal Wasm-like IR rather than raw Wasm, but the architecture should preserve the path toward direct Wasm validation.

## Scope

Use Lean as the frontend.  Do not parse or elaborate Lean independently.  The compiler should read already checked Lean declarations from the Lean environment, compute the transitive dependency graph of an entry function, reject unsupported constructs, erase noncomputational content, specialize definitions, and lower the accepted program into a small typed IR.

The first supported programs should be pure, closed functions over first-order data.  The initial entry-point shape should be something like:

```lean
def validate : ByteArray → Bool
def parse : ByteArray → Except Error Result
def encode : Input → ByteArray
```

The first release should not support arbitrary `IO`, Lean runtime reflection, `unsafe`, concurrency, arbitrary FFI, dynamic environment access, or general higher-order runtime behavior.

## Accepted subset

Start with a deliberately narrow subset.

| Feature                                                   | Initial support                   |
| --------------------------------------------------------- | --------------------------------- |
| `Bool`, fixed-width integers, `UInt8`, `UInt32`, `UInt64` | Yes                               |
| `ByteArray` or an equivalent byte-buffer abstraction      | Yes                               |
| Structures                                                | Yes                               |
| Simple inductives                                         | Yes                               |
| Pattern matching                                          | Yes                               |
| Structural recursion                                      | Yes, restricted                   |
| Tail recursion over buffers or arrays                     | Yes                               |
| Propositions and proofs                                   | Erased                            |
| Type parameters                                           | Monomorphized                     |
| Typeclasses                                               | Specialized when statically known |
| `Option`, `Except`, small result types                    | Yes                               |
| Arrays/slices                                             | Limited, explicit representation  |
| Strings                                                   | Later, unless byte-oriented       |
| Higher-order functions                                    | Later                             |
| General closures                                          | Later                             |
| Full Lean `IO`                                            | No                                |
| `unsafe`                                                  | No                                |
| Runtime reflection                                        | No                                |
| Arbitrary FFI                                             | No                                |

Unsupported declarations must fail with exact diagnostics.  The compiler should say which declaration blocks extraction and why: opaque constant, unsupported primitive, unspecialized polymorphism, higher-order value escape, unsupported recursor, unsupported effect, or runtime environment dependency.

## Near-term language support agenda

The next work should broaden ordinary programming support while keeping extraction correctness explicit.  The first target is monomorphic, nonrecursive user-defined inductives, because they generalize the prior special handling for `Option` and `Except`.  This gives source-defined result types, error types, tokens, states, and small enums a principled representation in the extractor.

| Order | Work | Purpose | Completion criteria |
| ----- | ---- | ------- | ------------------- |
| 1 | Monomorphic, nonrecursive user inductives | Add source-identified sum types with constructors, proof-erased constructor fields, and generated matcher support | Constructors, pattern matches, ignored-payload laziness, proof-field erasure, and returned tagged values pass Lean-versus-Wasmtime tests |
| 2 | Unified sum representation | Replace special-case `Option` and `Except` handling with the same source-identified inductive path | `Option`, `Except`, and user-defined sums no longer share anonymous runtime shapes, and `Except Unit α` works when payload types are supported |
| 3 | Tagged result ABI | Let exported functions return supported inductives rather than forcing traps or ad hoc scalar encodings | The Wasm ABI documents tags, payload layout, multi-value flattening, and host decoding for supported sums |
| 4 | Structured parameters | Accept supported structures and small inductives as entry parameters | The ABI flattens input records and tagged sums in source order, with exact rejection reasons for unsupported fields |
| 5 | Arrays with richer elements | Extend `Array` beyond `Array UInt64` to supported scalar, structure, and small-inductive element types | One-cell scalar arrays are specified and tested; structure and small-inductive arrays have fixed-width literal, replication, read, safe-read, default-read, write, modification, mapping, push, pop, append, extract, insertion, erasure, swapping, reversal, and returned-pointer support |
| 6 | Internal recursive inductives | Add monomorphic self-recursive data values with arena pointers at strict boundaries | Constructors, matches, branch values, helper values, and a fuel-recursive list traversal pass Wasm tests; public recursive ABI, mutual recursion, arrays of recursive values, and GC remain planned |
| 7 | Broader recursion shapes | Expand beyond the current fuel-tail-recursion form to structural recursion over arrays and simple inductives | Accepted recursion shapes have exact syntactic and semantic checks, with tests for non-tail rejection and Lean-equivalent execution |
| 8 | Owned byte output and strings | Add owned `ByteArray` results before admitting `String` | First byte-output slices are implemented for `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, `ByteArray.push`, `ByteArray.append`, proof-indexed `ByteArray.set`, trapping `ByteArray.set!`, `ByteArray.copySlice`, `ByteArray.toUInt64LE!`, `ByteArray.toUInt64BE!`, scalar-accumulator `ByteArray.foldl`, `ByteArray.findIdx?`, byte-array slices, and pointer-length results.  `String`, UTF-8 policy, and broader byte-array operations remain planned. |
| 9 | Restricted `IO` | Add explicit host imports for small byte-oriented effects after pure output is stable | The IR represents each effect explicitly, the Wasm module declares its imports, and hidden runtime access remains rejected |

Correctness remains the gate for each expansion.  Each feature must update `spec.md`, add accepted and rejected examples, compare Lean execution with Wasmtime for representative programs, and keep rejection reasons exact.  Features that require unresolved ABI or memory-layout decisions should stay planned until those decisions are written down.

Current progress: the first implementation slice for monomorphic, nonrecursive user inductives now supports constructors, generated matcher extraction, proof-erased constructor fields, nullary enums, local helper values, branch-selected values, exported tagged results, and flattened tagged entry parameters.  Monomorphic self-recursive inductives now work as internal values with lazy local constructors and arena pointers at strict boundaries; the correctness corpus covers a `UInt64` list, nested matches, branch-selected recursive values, a fuel-recursive traversal, and a direct list-shaped structural recursion helper.  `Option` and `Except` now use source-identified internal representations, so `Except Unit α` works for supported payloads and neither built-in sum shares an anonymous runtime shape.  Public `Option` and `Except` parameters and results use the same tagged multi-value ABI as user-defined inductives.  Arrays now cover one-cell scalar element types and a fixed-width multi-slot layout for monomorphic structures and small tagged values, including copy-on-write replication, reads, default reads, writes, modifications, mapping, scalar-accumulator folds, `find?`, `findIdx?`, `any`, `all`, `filter`, pushes, pops, appends, extracts, insertions, erasures, swaps, and reversals.  The restricted Nat-fuel recursion path now carries and returns supported structures and tagged values, not only scalar values, and it can carry recursive inductive pointers for traversal.  Its recursive step may stage computations through local `let` bindings before the tail call or before the immediate tail-call `if`, and the correctness corpus now includes a byte parser that carries cursor state in a structure.  `ByteArray` parameters and results use a pointer-length ABI; `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, slices, copy-on-write `push`, copy-on-write `append`, append notation, proof-indexed copy-on-write `set`, trapping copy-on-write `set!`, value-level `copySlice`, fixed-width `UInt64` decoding, scalar-accumulator `foldl`, and `findIdx?` support small byte-output and byte-processing programs in the arena memory model.  `AsciiString` now has bytewise equality, prefix testing, and byte-containment helpers in addition to validation, indexing, append, and extract.  The integer-map example now uses a `Slot` structure and `Table` structure over `Array Slot`, and the regression harness runs it with Wasmtime.

## Go-level expressiveness milestone

A useful milestone is the ability to write deterministic, first-order programs in Lean with roughly the same everyday programming tools that Go programmers use for parsers, validators, encoders, protocol logic, and command-line transforms.  This does not mean copying Go's runtime model.  The milestone should cover records, sum types, loops, mutable local state patterns, arrays, slices, bytes, explicit errors, and small libraries, while excluding goroutines, channels, reflection, unsafe pointers, arbitrary FFI, and ambient runtime services.

| Area | Current gap | Milestone criterion |
| ---- | ----------- | ------------------ |
| Control flow | The extractor accepts a restricted tail-recursion shape over `Nat` fuel, including local step lets before the tail call or tail-call `if`; list-shaped structural recursion over internal recursive inductives; scalar-accumulator `ByteArray.foldl`; scalar-accumulator `Array.foldl`; yield-only pure `Id.run` `for` loops over `ByteArray` and fixed-width arrays; `ByteArray.findIdx?`; and array scans through `Array.find?`, `Array.findIdx?`, `Array.any`, `Array.all`, and `Array.filter` over fixed-width arrays.  Early returns, breaks, range loops, structural recursion over branching data, and recursive descent through arrays are absent. | Lean programs can express common loops over counters, byte buffers, arrays, and simple inductives in accepted source forms, with exact rejection for unsupported recursion. |
| Mutable local state | The supported source style remains expression-oriented, with pure array updates and local shadowing.  Go-style code often uses counters, cursors, accumulators, and state variables as the normal form. | The subset accepts Lean encodings of local mutable state that elaborate to checked, first-order terms with predictable extraction and no hidden Lean runtime dependency. |
| Data types | Structures, user-defined inductives, `Option`, and `Except` now work as local values, parameters, and returned values when their runtime fields fit the current ABI.  Monomorphic self-recursive inductives work internally but do not cross the public ABI.  Arrays of structured values now cover the fixed-width operations listed above, while polymorphic data types, mutual recursion, arrays of recursive values, and recursive public values remain missing. | Supported structures, small inductives, recursive internal values, `Option`, and `Except` can appear according to one documented representation, with public ABI limits stated explicitly. |
| Memory model | The current memory model has arena allocation and copy-on-write arrays for one-cell scalar element types, plus fixed-width structure and tagged arrays for literals, replication, reads, default reads, writes, modifications, mapping, filtering, pushes, pops, appends, extracts, insertions, erasures, swaps, reversals, and returned pointers.  It now supports pointer-length `ByteArray` results, arena-owned `ByteArray.mk` from `Array UInt8`, arena-owned `ByteArray.push`, arena-owned `ByteArray.append`, and arena-owned proof-indexed `ByteArray.set`, but it still lacks aliasing rules for faster updates. | The compiler has explicit layouts for supported arrays and slices, a documented ownership model for returned buffers, and correctness tests for reads, writes, copies, aliases, and returned memory. |
| Strings and bytes | The compiler supports `ByteArray` input, slices, pointer-length `ByteArray` results, `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, copy-on-write `ByteArray.push`, copy-on-write `ByteArray.append`, append notation through `++`, proof-indexed copy-on-write `ByteArray.set`, trapping copy-on-write `ByteArray.set!`, value-level `ByteArray.copySlice`, `ByteArray.toUInt64LE!`, `ByteArray.toUInt64BE!`, scalar-accumulator `ByteArray.foldl`, and `ByteArray.findIdx?`.  It does not support `ByteArray.foldlM`, `USize` byte operations, string values, string parsing, string construction, or a UTF-8 policy. | Byte output works before strings, and string support enters only after allocation, ownership, encoding, and validation rules are specified. |
| Maps | The subset has no built-in or generic map type.  A hand-written open-addressed integer map now compiles from ordinary subset code using structures, arrays, and fuel-recursive loops. | A small standard map library can be written without special compiler support, with documented collision, deletion, capacity, and key-type limits. |
| Errors | Go programs rely on explicit error returns.  The nearest Lean form is `Except`; exported `Except` parameters and results now work when payload fields fit the current ABI, while broader error payload types remain limited by the current layouts. | Exported functions can return tagged success or error values with source-defined error types and host-decodable result layout. |
| Functions | Higher-order arguments and closures are rejected.  This blocks callbacks, visitors, and adapters, although many first-order programs can proceed without them. | The first Go-level milestone can remain first-order, but the plan should keep a later escape-restricted function-value design open. |
| Polymorphism | Type parameters and typeclass instance dependencies are reported rather than compiled.  This blocks generic library code, although monomorphic programs can still be useful. | Monomorphic library instances compile today, and later monomorphization and typeclass specialization have specified acceptance and rejection rules. |
| Packages and dependencies | The report can inspect dependencies, but there is no broad accepted library subset across multi-file programs. | Multi-module Lean programs compile when every runtime dependency is inside the subset, and diagnostics name the first unsupported declaration and construct. |
| `IO` | No Lean `IO` compiles.  Go-level command-line usefulness eventually needs explicit access to input, output, files, arguments, environment variables, and exit status. | Restricted `IO` is represented in the IR through declared host imports, after pure byte output and tagged error results are stable. |
| Concurrency | Goroutines, channels, timers, and scheduling are absent. | Concurrency stays outside the first Go-level milestone, because it requires a larger runtime and proof model. |
| Reflection and unsafe features | Runtime reflection, unsafe pointers, and arbitrary FFI are rejected. | These features remain outside the milestone unless the project later defines a separate unsafe or unverifiable mode. |

The shortest path to this milestone is the same path as the near-term agenda: user-defined inductives, unified sums, tagged results, structured parameters, richer arrays and slices, owned byte output, broader recursion, and restricted `IO`.  That sequence supports useful deterministic programs before the compiler takes on runtime services.  Each step should leave behind a small source program that looks like normal application code rather than a compiler test case.

## Architecture

### 1. Lean frontend integration

Implement a Lake tool or Lean executable that accepts:

```bash
lean-wasm build MyApp.lean \
  --entry MyApp.validate \
  --out ./build/validate.wasm
```

The tool should invoke Lean’s normal elaboration and checking.  It should then inspect the checked environment and collect all runtime-relevant declarations needed by the entry point.

Outputs at this stage:

```text
extraction graph
accepted declarations
rejected declarations with reasons
erased/proof-free representation
```

### 2. Extractable core IR

Define a small typed IR in Lean.  It should be closer to a first-order functional language than to Wasm at first.

It should contain:

```text
types: units, booleans, fixed-width integers, products, sums, byte arrays, arrays
terms: variables, lets, calls, constructors, projections, case, loops, primitive ops
effects: initially none, later explicit error/result effects
```

This IR is the first formal boundary.  Prove or prepare to prove that extraction from checked Lean declarations into this IR preserves behavior for the accepted subset.

### 3. Optimization and specialization

Keep optimizations simple and proof-friendly.

Initial passes:

```text
proof erasure
dead argument elimination
monomorphization
typeclass specialization
constant folding
pattern-match compilation
tail-recursion-to-loop conversion
simple inlining
data-layout selection
```

Each pass should either be small enough to prove correct or designed for translation validation.

### 4. Wasm-shaped IR

Lower the typed core IR into a structured-control IR close to WebAssembly.  This IR should model:

```text
functions
locals
blocks
loops
branches
loads and stores
linear memory
numeric operations
calls
imports and exports
```

Avoid modeling the whole Wasm ecosystem.  Model only the Wasm subset the compiler emits.

### 5. Memory model

Use linear memory with arena allocation for the first implementation.

Per call:

```text
host writes input into linear memory
compiled function runs
compiled function allocates inside an arena
compiled function returns scalar or pointer-length result
arena resets after call
```

This avoids early reference counting, tracing GC, and object finalization.  It is suitable for parsers, validators, encoders, and bounded computations.

Later options:

```text
region allocation
escape-analysis-driven stack allocation
reference counting
Wasm GC, only after the core compiler is stable
```

### 6. Wasm emitter

Emit a `.wasm` module from the Wasm-shaped IR.  The initial host ABI should be minimal.

Example exports:

```text
memory
alloc
reset
validate(ptr: i32, len: i32) -> i32
parse(ptr: i32, len: i32) -> i32
```

Result conventions should be explicit.  For example, `0` for false/error, `1` for true/success, or pointer-length pairs for structured outputs.

Avoid hidden host dependencies.  Imports should be explicit and few.

## Correctness strategy

Use a staged assurance model.

### Stage 1: differential testing

Before proving the compiler, build a reliable test harness.

For generated modules:

```text
run Lean source function on input
run Wasm module on same input
compare outputs
fuzz inputs
run regression corpus
run boundary-value tests
```

This gives immediate engineering value and catches representation errors.

### Stage 2: formal source-to-core extraction

Define semantics for the extractable Lean subset or for the extracted core IR.  Prove that extraction preserves the behavior of accepted declarations.

Target theorem:

```lean
theorem extract_correct :
  ∀ x, Core.eval (extract f) x = f x
```

### Stage 3: verified IR passes

Prove correctness of each simple pass:

```lean
theorem erase_correct
theorem specialize_correct
theorem inline_correct
theorem match_compile_correct
theorem loop_lowering_correct
```

When proof cost is too high, use translation validation: the pass emits a certificate that Lean checks.

### Stage 4: Wasm model correctness

Define a Lean model of the emitted Wasm subset.  Prove that lowering from the Wasm-shaped IR to the Wasm model preserves behavior.

Target theorem:

```lean
theorem wasm_lower_correct :
  ∀ x, WasmModel.run (lower core) x = Core.eval core x
```

### Stage 5: final statement

Compose the theorems:

```lean
theorem compile_correct :
  ∀ x, WasmModel.run (compile f) x = f x
```

The remaining trusted base is then:

```text
Lean kernel and axioms used
formal semantics of the modeled Wasm subset
Wasm emitter correctness, unless separately verified
actual Wasm runtime compliance
host ABI correctness
hardware and operating system
```

State this boundary explicitly.  Do not claim the final browser, Wasmtime, or Wasmer execution is formally verified unless that runtime is part of the proof.

## First milestone

Build a verified or validation-ready compiler for:

```lean
def validate : ByteArray → Bool
```

The demonstration program should be a real parser or validator with a nontrivial Lean theorem:

```lean
theorem validate_sound :
  validate input = true → WellFormed input
```

Deliverables:

```text
Lean source validator
extraction report
generated Wasm module
host runner
fuzz harness comparing Lean and Wasm
initial core IR semantics
first proof sketches or completed proofs for proof erasure and pattern-match lowering
```

## Second milestone

Support:

```lean
def parse : ByteArray → Except ParseError Ast
```

Add simple inductive outputs, structured results, arena-allocated ASTs, and pointer-length result encoding.

Deliverables:

```text
Wasm AST layout
host decoder
round-trip tests
Lean/Wasm differential tests
translation certificate for selected examples
```

## Third milestone

Prove the core compiler path for the first subset.

Deliverables:

```text
formal semantics for core IR
formal semantics for emitted Wasm subset or Wasm-shaped IR
proved extraction correctness for accepted first-order definitions
proved lowering correctness for pattern matches, calls, constructors, projections, and loops
one end-to-end compile_correct theorem for a real validator
```

## Engineering principles

Keep the accepted language small.  The compiler’s strength is a narrow semantic target, not broad Lean compatibility.

Reject unsupported code precisely.  A useful failure mode is better than unsound generated code.

Avoid the Lean runtime in the Wasm output.  The output should be a small, standalone module with explicit memory and host ABI.

Prefer byte-oriented APIs first.  Strings, Unicode, arbitrary maps, and rich standard-library behavior can wait.

Keep the generated Wasm deterministic.  Avoid host nondeterminism unless explicitly modeled.

Use Wasm as the semantic target, not as a disguised runtime for arbitrary Lean objects.

## Summary

The project should be handed off as:

**Build a restricted, verification-oriented Lean-to-Wasm extractor.  Use Lean for parsing, elaboration, type checking, and proofs.  Accept only a closed first-order executable subset.  Erase proofs, specialize definitions, lower to a small typed IR, then to a modeled Wasm subset with arena allocation.  Start with byte-array validators and parsers.  Provide differential testing immediately and build toward a composed theorem showing that the Wasm model computes the same function as the checked Lean source.**
