## Plan: Verified Lean-to-WASM Extraction Compiler

Build a compiler that takes **checked Lean definitions** from a restricted executable subset and emits **portable WebAssembly**.  The goal is not to replace Lean’s general compiler.  The goal is to compile selected Lean programs, especially parsers, validators, serializers, protocol checkers, and finite decision procedures, into small WASM modules with a clear correctness story.

The central claim should be:

```lean
theorem compile_correct :
  ∀ input,
    WasmModel.run (compile f) input = f input
```

This theorem may initially target an internal WASM-like IR rather than raw WASM, but the architecture should preserve the path toward direct WASM validation.

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
| 3 | Tagged result ABI | Let exported functions return supported inductives rather than forcing traps or ad hoc scalar encodings | The WASM ABI documents tags, payload layout, multi-value flattening, and host decoding for supported sums |
| 4 | Structured parameters | Accept supported structures and small inductives as entry parameters | The ABI flattens input records and tagged sums in source order, with exact rejection reasons for unsupported fields |
| 5 | Arrays with richer elements | Extend `Array` beyond `Array UInt64` to supported scalar, structure, and small-inductive element types | One-cell scalar arrays are specified and tested; structure and small-inductive arrays have fixed-width literal, replication, read, safe-read, default-read, write, modification, mapping, push, pop, append, extract, insertion, erasure, swapping, reversal, and returned-pointer support |
| 6 | Internal recursive inductives | Add self-recursive data values and monomorphic recursive instances with arena pointers at strict boundaries | Constructors, matches, branch values, helper values, a fuel-recursive list traversal, direct structural traversal over one or more direct recursive fields, source-defined list helpers that return recursive values, generated `Array`-child traversal, monomorphic `List` construction and traversal over supported internal element layouts, expression-position `List.length`, list append notation through `++`, `List.reverse`, `List.map`, `List.filter`, and `List.foldr`, explicit and top-level closed `List.foldl`, closed structural predicates such as direct `List.any` and `List.all`, and limited direct-lambda `List` library calls pass WASM tests; public recursive ABI, mutual recursion, arbitrary well-founded recursion, broader hidden carried arguments, broader expression-position `List` APIs, and GC remain planned |
| 7 | Broader recursion shapes | Expand beyond the current fuel-tail-recursion form to structural recursion over arrays and simple inductives | Accepted recursion shapes have exact syntactic and semantic checks, with tests for non-tail rejection and Lean-equivalent execution |
| 8 | Owned byte output and strings | Add owned `ByteArray` results before admitting runtime `String` | First byte-output slices are implemented for `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, `ByteArray.push`, `ByteArray.append`, proof-indexed `ByteArray.set`, trapping `ByteArray.set!`, `ByteArray.copySlice`, `ByteArray.toUInt64LE!`, `ByteArray.toUInt64BE!`, `ByteArray`-accumulator loops, `ByteArray`-accumulator folds, structured-accumulator `ByteArray.foldl`, `ByteArray.foldlM` through `Option` and `Except`, `ByteArray.findIdx?`, byte-array slices, pointer-length results, and restricted compile-time ASCII `String` expressions consumed by `toUTF8`, `length`, `isEmpty`, and equality.  Runtime `String`, UTF-8 decoding, and broader byte-array operations remain planned. |
| 9 | Restricted `IO` | Add explicit host imports for small byte-oriented effects after pure output is stable | The IR represents each effect explicitly, the WASM module declares its imports, and hidden runtime access remains rejected |

Correctness remains the gate for each expansion.  Each feature must update `spec.md`, add accepted and rejected examples, compare Lean execution with Wasmtime for representative programs, and keep rejection reasons exact.  Features that require unresolved ABI or memory-layout decisions should stay planned until those decisions are written down.

  Current progress: the first implementation slice for monomorphic, nonrecursive user inductives now supports constructors, generated matcher extraction, proof-erased constructor fields, nullary enums, local helper values, branch-selected values, exported tagged results, and flattened tagged entry parameters.  User-defined structures and nonrecursive user inductives now carry concrete runtime type parameters in their layouts, so examples such as `Box UInt64`, `PairBox UInt64 Bool`, and `ParamResult UInt64 Point` compile through constructors, projections, matches, helper parameters, helper results, entry parameters, entry results, and fixed-width arrays.  First-order polymorphic helpers over supported concrete instantiations now inline-specialize at call sites when static type, proof, or direct-lambda arguments appear among supported runtime arguments; this covers helpers such as `Box α -> α`, `PairBox α β -> α`, `ParamResult ε α -> Bool`, `CheckedPayload α -> α`, `genericApplyWithSeed 10 value (fun item => ...)`, and `decodeRequiredField fields name (fun raw => decodeArray (fun item => decodeItem item) raw)` without adding shared generic runtime functions, closure allocation, or typeclass dispatch.  Monomorphic self-recursive inductives now work as internal values with lazy local constructors and arena pointers at strict boundaries; the correctness corpus covers a source-defined `UInt64` list, nested matches, branch-selected recursive values, a fuel-recursive traversal, direct structural recursion over list-shaped and branching constructors, source-defined `List` helpers for length, append, reverse, and fold-right-style traversals, an expression-AST evaluator, and recursive tree descent through an `Array` child field.  Internal fixed-width structures and nonrecursive tagged values may contain recursive-inductive pointer fields, and arrays of those values are covered by tests for folds and searches.  Internal mutual recursive inductive families now classify each family member as a heap-recursive value, so constructors may refer to another member directly or through fixed-width arrays.  Ordinary mutual structural traversals over recursive-family members now compile through Lean's generated `WellFounded.Nat.fix` over nested `PSum`, including recursive descent through direct fields and fixed-width array folds over attached array elements.  The recursive-inductive representation now also carries concrete runtime type parameters, so ordinary monomorphic `List` construction, matching, helper calls, direct structural recursion, generated `Array.attach` fold recursion, explicit-accumulator `List.foldl` helpers, top-level closed `List.foldl` bodies with one hidden accumulator, closed structural predicates for direct `List.any` and `List.all`, monomorphic helper calls to `List.map`, `List.filter`, `List.find?`, `List.foldl`, `List.any`, and `List.all`, and direct expression-position `List.length`, list append notation through `++`, `List.reverse`, `List.map`, `List.filter`, and `List.foldr` compile through the same heap-recursive path when callbacks are direct lambdas and results are first-order values.  The comparison corpus covers those list operations over `UInt64`, structures, nonrecursive tagged values, `ByteArray`, `Option UInt64`, `Option ByteArray`, and `Except ByteArray UInt64`.  `Option` and `Except` now use source-identified internal representations, so `Except Unit α` works for supported payloads and neither built-in sum shares an anonymous runtime shape.  Public `Option` and `Except` parameters and results use the same tagged multi-value ABI as user-defined inductives.  `Except` do-notation coverage now includes helper calls that contain accepted cursor loops, structured ok results, nonrecursive tagged ok results, byte-array ok results, monadic loops over accepted collections, and short-circuiting that skips later trapping computations.  Public `UInt8` and `UInt32` parameters and results now use one `i64` slot and normalize at the public boundary to their fixed-width ranges.  Arrays now use an explicit value-layout model: scalar elements occupy one slot, `ByteArray` elements occupy owner, pointer, and length slots, nested arrays occupy owner and pointer slots, products and fixed-width structures or tagged values occupy their flattened slot count, and recursive inductive values occupy one pointer slot in internal arrays.  Array allocation now records child-pointer masks for fixed-width element layouts, and array-copying operations retain recursive children, `ByteArray` owners, and `Array` owners when they share elements with a new array.  The correctness corpus covers nested-array literals, `Array ByteArray` literals, updates, pushes, folds, maps, searches, equality over scalar arrays, nested arrays, byte-array arrays, arrays of structures containing byte arrays, arrays of structures containing array fields, arrays of products, and public entry parameters and results for `Array ByteArray`, `Array (Array UInt64)`, arrays of `Option ByteArray`, arrays of `Except ByteArray ByteArray`, arrays of source-defined tagged values containing `ByteArray`, structures containing `Array ByteArray`, nonrecursive tagged values containing `Array ByteArray`, arrays of structures containing `ByteArray`, and arrays of structures containing array fields.  Public arrays of recursive inductive values remain rejected.  Pure `Id.run do` blocks now support ordinary mutable local assignments over scalars, structures, structures containing `ByteArray` or internal `Array` fields, fixed-width arrays, `Option`, and `Except`, including nested conditionals, matches, `if let` forms, and sparse generated matches for `Option` and nonrecursive user inductives that Lean lowers through local continuation lambdas and `PUnit` sequencing.  Generated `Option` matchers used as conditions and generated `Except` match helpers with leading type and motive parameters are recognized by locating the typed scrutinee, so specialized transparent helpers can reuse ordinary generated matches instead of compiling function-valued motives.  Inline-only helper dependencies now contribute their supported callees to the compiled function set, while the helper itself remains specialized at the call site.  Generated structure matchers can bind flattened nested single-constructor accumulator fields, which covers the `MProd` destructuring Lean emits after loops with several mutable locals.  Checked loops over `ByteArray`, fixed-width arrays, `Std.Legacy.Range`, and source `while` loops lowered through `Lean.Loop` now work in `Id`, `Option`, and `Except ε` when the accumulator type is supported.  Those loops support multiple mutable locals, nested accepted loops, indexed byte-array reads, mutable byte-array output, mutable array updates, `break`, `continue`, and conditional skip-or-exit forms before later assignments in the same loop body.  `Option` and `Except` loop iterations stop after `none`, `Except.error`, or `ForInStep.done`, so later iteration code is not evaluated.  Direct `Array.foldl`, `Array.foldr`, and `ByteArray.foldl` now use the same internal accumulator layout for direct-lambda folders, including `ByteArray` accumulators and structures that contain `ByteArray` fields.  The compiler releases replaced heap-valued accumulator owner slots after the first iteration in those folds and accepted loops when the next accumulator owner is proven fresh and the body has not already released the old slot.  Heap-result functions now release fresh nonrecursive owner slots, currently `ByteArray` and `Array`, after result materialization when those owners are absent from returned heap roots and borrowed root expressions; recursive heap-result temporaries remain conservative.  The restricted Nat-fuel recursion path now carries and returns supported structures and tagged values, not only scalar values, and it can carry recursive inductive pointers for traversal.  Its recursive step may stage computations through local `let` bindings before the tail call or before the immediate tail-call `if`, and the correctness corpus now includes a byte parser that carries cursor state in a structure.  Non-exported helper functions use internal parameter and result layouts, preserving products and other internal-only multi-slot values across real WASM calls.  `ByteArray` parameters and results use a pointer-length ABI; `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, equality, slices, copy-on-write `push`, copy-on-write `append`, append notation, proof-indexed copy-on-write `set`, trapping copy-on-write `set!`, value-level `copySlice`, fixed-width `UInt64` decoding, `ByteArray`-producing loops, `ByteArray`-accumulator folds, structured-accumulator `foldl`, and `findIdx?` support small byte-output and byte-processing programs in the arena memory model.  `AsciiString` now has bytewise equality, prefix testing, and byte-containment helpers in addition to validation, indexing, append, and extract.  The integer-map example now uses a `Slot` structure and `Table` structure over `Array Slot`, and the test harness runs it with Wasmtime.

Current JSON decode progress: the JSON AST now has an `Except ByteArray` decoder helper layer for required typed fields, exact field sets, unsigned-integer arrays, required-field decoding through a direct decoder lambda, generic array decoding through a direct decoder lambda, parse, and render.  `LeanExe.Examples.JsonTypedDecode` decodes a JSON object into a source-defined request structure, computes checked aggregate values, and runs through the WASI `Except` adapter.  `LeanExe.Examples.JsonObjectArrayDecode` decodes a JSON object whose `items` field is an array of source-defined item structures, computes a checked weighted aggregate, and runs through the same WASI adapter.  This keeps JSON decoding as ordinary Lean library code over the recursive AST rather than adding JSON-specific compiler behavior.

Current program-output progress: WASI command mode accepts a zero-argument `ByteArray` entry, wraps it in `_start`, and writes the returned bytes to stdout through `wasi_snapshot_preview1.fd_write`.  It also accepts a bounded stdin-to-stdout mode for pure `ByteArray -> ByteArray` entries, reading stdin through `fd_read` up to an explicit byte limit before calling the Lean entry.  The error-aware stdin mode accepts `ByteArray -> Except ByteArray ByteArray`, writes `Except.ok` payloads to stdout with success, writes `Except.error` payloads to stderr, and calls `proc_exit 1`.  The argv mode accepts `Array ByteArray -> Except ByteArray ByteArray`, reads WASI argv through `args_sizes_get` and `args_get`, skips `argv[0]`, and applies the same stdout, stderr, and exit-status behavior.  These modes give byte-producing programs observable command-line behavior under Wasmtime without compiling Lean `IO`.  Streaming input, files, and environment variables remain planned.

## Ownership diagnostics

`lean-wasm ownership-report --module M --entry E` now prints each extracted function's result type, result owner slots, helper-result fresh-owner offsets, compiler-inserted releases, returned owner expressions, fold accumulator release offsets, and explicit `LeanExe.Runtime.release` expressions.  The first test cases cover `Option ByteArray`, `Except UInt64 ByteArray`, and `Option ByteOutputState` loop-output counters, plus `JsonTreeCommand.makeTree`, including a source-level release expression in `insertOwned`.  The structured monadic-result demand bug is fixed by preserving a materialized multi-slot fold result as one atomic local assignment when later code reads only a subset of its slots.

Recursive heap cleanup now follows a conservative policy.  Ordinary result cleanup releases nonrecursive owners such as `ByteArray` and `Array`, while recursive heap temporaries may leak unless the source program calls `LeanExe.Runtime.release` at an explicit ownership boundary or the value is a replaced accumulator under a supported fold or loop rule.  Unknown recursive ownership means retain or leak, never compiler-inserted release.

## Go-level expressiveness milestone

A useful milestone is the ability to write deterministic, first-order programs in Lean with roughly the same everyday programming tools that Go programmers use for parsers, validators, encoders, protocol logic, and command-line transforms.  This does not mean copying Go's runtime model.  The milestone should cover records, sum types, loops, mutable local state patterns, arrays, slices, bytes, explicit errors, and small libraries, while excluding goroutines, channels, reflection, unsafe pointers, arbitrary FFI, and ambient runtime services.

| Area | Current gap | Milestone criterion |
| ---- | ----------- | ------------------ |
| Control flow | The extractor accepts a restricted tail-recursion shape over `Nat` fuel, including local step lets before the tail call or tail-call `if`; direct structural recursion over internal recursive inductives with one or more direct recursive fields; expression-position structural recursion with supported first-order post-arguments; generated well-founded recursion for `Array` child descent; direct `ByteArray.foldl`, `ByteArray.foldlM`, `Array.foldl`, `Array.foldr`, and `Array.foldlM` with supported internal accumulators, including `ByteArray` and structures that contain `ByteArray` fields; monadic folds through `Option` and `Except` that stop at the first failure tag; checked loops over `ByteArray`, fixed-width arrays, ranges, and `Lean.Loop` source `while` loops in `Id`, `Option`, and `Except` with the same accumulator rule; nested accepted loops; `break` and `continue` in those accepted loops; short-circuiting after `none` or `Except.error`; byte-array indexing inside cursor loops; mutable array updates inside accepted loops; `ByteArray.findIdx?`; and array scans through `Array.find?`, `Array.findIdx?`, `Array.any`, `Array.all`, and `Array.filter` over fixed-width arrays.  Early returns, general `break` or `continue` outside the accepted loop shape, course-of-values recursion, and arbitrary well-founded recursion are absent. | Lean programs can express common loops over counters, byte buffers, arrays, and simple inductives in accepted source forms, with exact rejection for unsupported recursion. |
| Mutable local state | The subset accepts pure `Id.run do` mutable local assignments over supported first-order values, including nested conditionals, matches, `if let` forms, sparse generated matches over `Option` and nonrecursive user inductives, the local continuations Lean generates for assignment sequencing, flattened generated matchers over nested accumulator structures, and state records containing `ByteArray` or internal `Array` fields.  Parser-style code can now combine mutable cursors, byte reads, byte output, mutable array updates, and explicit status values.  Go-style code often uses counters, cursors, accumulators, and state variables as the normal form, and the remaining gaps are broader source shapes rather than the basic mutable-local model. | The subset accepts Lean encodings of local mutable state that elaborate to checked, first-order terms with predictable extraction and no hidden Lean runtime dependency. |
| Data types | Structures, user-defined inductives, `Option`, and `Except` now work as local values, parameters, and returned values when their runtime fields fit the current ABI.  Monomorphic self-recursive inductives, internal mutual recursive inductive families, mutual structural traversals over recursive-family members, and monomorphic recursive instances such as `List α` work internally when `α` has a supported internal layout, but they do not cross the public ABI.  Recursive pointers may appear inside internal fixed-width structures and nonrecursive tagged payloads, including arrays of those values, while unspecialized polymorphic data, broader mutual recursive functions, arbitrary well-founded recursion, and recursive public values remain missing. | Supported structures, small inductives, recursive internal values, `Option`, and `Except` can appear according to one documented representation, with public ABI limits stated explicitly. |
| Memory model | The current memory model has arena allocation, copy-on-write arrays, `ByteArray` elements with owner-pointer-length layout, nested arrays with owner-pointer layout, products, fixed-width structure and tagged arrays for literals, replication, reads, default reads, writes, modifications, mapping, filtering, pushes, pops, appends, extracts, insertions, erasures, swaps, reversals, and returned pointers.  It now supports pointer-length `ByteArray` results, arena-owned `ByteArray.mk` from `Array UInt8`, arena-owned `ByteArray.push`, arena-owned `ByteArray.append`, arena-owned proof-indexed `ByteArray.set`, public arrays with fixed-width heap-reference fields, reference-counted release through recursive children, `ByteArray` owners, nested-array owners, compiler-emitted release for nonrecursive array and byte-array owner slots proven fresh by IR ownership summaries, compiler-emitted release for replaced heap-valued accumulators after the first iteration in supported folds and pure loops, recursive heap allocation that retains borrowed children while transferring proven-fresh children, and preserved source-level `Runtime.release` ownership boundaries.  Recursive temporaries in ordinary result cleanup are deliberately conservative, because leaks are preferable to incorrect computation.  It still lacks aliasing rules for faster updates, broader ownership analysis for heap-pointer results, and a public ABI for recursive heap graphs. | The compiler has explicit layouts for supported arrays and slices, a documented ownership model for returned buffers, and correctness tests for reads, writes, copies, aliases, and returned memory. |
| Strings and bytes | The compiler supports `ByteArray` input, slices, pointer-length `ByteArray` results, `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, copy-on-write `ByteArray.push`, copy-on-write `ByteArray.append`, append notation through `++`, proof-indexed copy-on-write `ByteArray.set`, trapping copy-on-write `ByteArray.set!`, value-level `ByteArray.copySlice`, `ByteArray.toUInt64LE!`, `ByteArray.toUInt64BE!`, `ByteArray`-producing pure loops, `ByteArray`-accumulator `Array.foldl` and `Array.foldr`, structured-accumulator `ByteArray.foldl`, `ByteArray.foldlM` through `Option` and `Except`, `ByteArray.findIdx?`, and compile-time ASCII `String` expressions for fixed text.  It does not support `USize` byte operations, runtime string values, string parsing, string construction from runtime data, UTF-8 decoding, or Unicode semantics. | Byte output and fixed ASCII syntax are available; runtime text remains a planned design problem with explicit encoding and validation rules. |
| Maps | The subset has no built-in or generic map type.  A hand-written open-addressed integer map now compiles from ordinary subset code using structures, arrays, and fuel-recursive loops. | A small standard map library can be written without special compiler support, with documented collision, deletion, capacity, and key-type limits. |
| Errors | Go programs rely on explicit error returns.  The nearest Lean form is `Except`; exported `Except` parameters and results now work when payload fields fit the current ABI, while broader error payload types remain limited by the current layouts. | Exported functions can return tagged success or error values with source-defined error types and host-decodable result layout. |
| Functions | Higher-order arguments and closures are rejected when they survive as runtime values.  Direct lambdas are accepted only when the extractor can specialize them into first-order code, which now covers selected array and byte-array operations, `Array.foldr`, `Array.foldlM` and `ByteArray.foldlM` through `Option` and `Except`, monomorphic `List.map`, `List.filter`, `List.find?`, `List.foldl`, `List.any`, and `List.all` helper calls over supported internal element layouts, direct expression-position structural recursion with supported first-order carried values, and transparent helper specialization when the direct-lambda argument appears among supported runtime arguments.  Escaping functions and unsupported hidden carried runtime arguments remain unsupported. | The first Go-level milestone can remain first-order, but the plan should keep a later escape-restricted function-value design open. |
| Polymorphism | Concrete type arguments now specialize supported user-defined structures, nonrecursive inductives, and recursive inductive families.  First-order polymorphic helpers can inline-specialize at concrete supported call sites when static type, proof, and direct-lambda arguments appear among supported runtime arguments.  Shared generic runtime functions, escaping polymorphic values, and typeclass-driven runtime dispatch remain unsupported, so broad generic library code still needs explicit specialization work. | Monomorphic library instances compile today, and later broader function monomorphization and typeclass specialization have specified acceptance and rejection rules. |
| Packages and dependencies | The report can inspect dependencies, but there is no broad accepted library subset across multi-file programs. | Multi-module Lean programs compile when every runtime dependency is inside the subset, and diagnostics name the first unsupported declaration and construct. |
| `IO` | No Lean `IO` compiles.  WASI command adapters now wrap pure zero-argument `ByteArray` results, bounded `ByteArray -> ByteArray` stdin transforms, bounded `ByteArray -> Except ByteArray ByteArray` error-aware transforms, and bounded `Array ByteArray -> Except ByteArray ByteArray` argv transforms with stderr and failure exit status.  Streaming input, files, and environment variables are still absent. | Restricted `IO` is represented in the IR through declared host imports, after pure byte output and tagged error results are stable. |
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

Define a small typed IR in Lean.  It should be closer to a first-order functional language than to WASM at first.

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

### 4. WASM-shaped IR

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

Avoid modeling the whole WASM ecosystem.  Model only the WASM subset the compiler emits.

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
WASM GC, only after the core compiler is stable
```

### 6. WASM emitter

Emit a `.wasm` module from the WASM-shaped IR.  The initial host ABI should be minimal.

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
run WASM module on same input
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

### Stage 4: WASM model correctness

Define a Lean model of the emitted WASM subset.  Prove that lowering from the WASM-shaped IR to the WASM model preserves behavior.

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
formal semantics of the modeled WASM subset
WASM emitter correctness, unless separately verified
actual WASM runtime compliance
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
generated WASM module
host runner
fuzz harness comparing Lean and WASM
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
WASM AST layout
host decoder
round-trip tests
Lean/WASM differential tests
translation certificate for selected examples
```

## Third milestone

Prove the core compiler path for the first subset.

Deliverables:

```text
formal semantics for core IR
formal semantics for emitted WASM subset or WASM-shaped IR
proved extraction correctness for accepted first-order definitions
proved lowering correctness for pattern matches, calls, constructors, projections, and loops
one end-to-end compile_correct theorem for a real validator
```

## Engineering principles

Keep the accepted language small.  The compiler’s strength is a narrow semantic target, not broad Lean compatibility.

Reject unsupported code precisely.  A useful failure mode is better than unsound generated code.

Avoid the Lean runtime in the WASM output.  The output should be a small, standalone module with explicit memory and host ABI.

Prefer byte-oriented APIs first.  Strings, Unicode, arbitrary maps, and rich standard-library behavior can wait.

Keep the generated WASM deterministic.  Avoid host nondeterminism unless explicitly modeled.

Use WASM as the semantic target, not as a disguised runtime for arbitrary Lean objects.

## Summary

The project should be handed off as:

**Build a restricted, verification-oriented Lean-to-WASM extractor.  Use Lean for parsing, elaboration, type checking, and proofs.  Accept only a closed first-order executable subset.  Erase proofs, specialize definitions, lower to a small typed IR, then to a modeled WASM subset with arena allocation.  Start with byte-array validators and parsers.  Provide differential testing immediately and build toward a composed theorem showing that the WASM model computes the same function as the checked Lean source.**
