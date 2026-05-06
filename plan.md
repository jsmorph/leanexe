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
