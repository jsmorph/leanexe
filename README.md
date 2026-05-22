# LeanExe

LeanExe compiles a restricted Lean 4 program to a standalone WebAssembly module.  Lean remains the type checker and source language; the compiler loads a checked declaration from a Lean module and emits WASM for the executable subset described in [Language Specification](spec.md).  The supported subset covers first-order pure programs over scalar values, byte arrays, fixed-width arrays, structures, inductive values, bounded recursion, and internal recursive data structures.

The default generated module exports a plain WASM function for the selected Lean declaration.  Scalar programs can run directly with Wasmtime.  Programs that pass or return byte arrays, structures, variants, or arrays use the ABI described below, so a host program must provide flattened values or memory values in the expected form.  WASI command modes provide stdout output, bounded stdin input, and an error-aware byte transform without compiling Lean `IO`.

## Requirements

This repository uses Lean through `elan` and Lake.  The pinned Lean version lives in `lean-toolchain`, and Lake builds the `lean-wasm` executable.  Wasmtime runs scalar examples and WASI command examples from the command line.  The repository test suite uses a small C host runner built against the Wasmtime C API for library-mode ABI tests that need memory writes and memory inspection.

```sh
tools/download-wasmtime.sh
lake build
tools/build-wasmtime-host.sh
```

`tools/download-wasmtime.sh` downloads the Wasmtime CLI and matching C API package for the detected Linux platform into `build/tools/wasmtime`.  It uses Wasmtime 44.0.0 by default.  `WASMTIME_VERSION` and `WASMTIME_PLATFORM` select a specific release artifact.  The full repository test suite expects the CLI at `build/tools/wasmtime/current/wasmtime` or a `WASMTIME` environment variable, and it expects the C API package at `build/tools/wasmtime/wasmtime-v44.0.0-<platform>-c-api` or a `WASMTIME_C_API` environment variable.  Node orchestrates tests, but generated WASM executes through Wasmtime.

```sh
node test/run_all.js
```

## Repository Layout

| Path | Purpose |
|------|---------|
| `LeanExe/Extract` | Checked-declaration extraction, dependency reporting, ABI lowering, and IR generation. |
| `LeanExe/IR` | The first-order core IR used before WASM emission. |
| `LeanExe/Wasm` | WASM module model, binary encoder, WAT printer, and interpreter support used by tests. |
| `LeanExe/Examples` | Example Lean programs that exercise the supported subset. |
| `test` | Node and Lean tests that compare Lean execution with generated WASM behavior. |
| `manual.md` | Practical guide to writing Lean source that LeanExe can compile. |
| `spec.md` | The accepted Lean subset, ABI, semantics, and known unsupported features. |
| `plan.md` | Development plan for expanding the compiler. |
| `devnotes.md` | Development notes and references. |

## Write a Program

Write ordinary Lean definitions inside a Lake module.  The selected entry declaration must be pure, monomorphically specialized at runtime, first-order, and accepted by the subset in [Language Specification](spec.md).  Use [LeanExe User Manual](manual.md) for source templates and practical authoring rules.  Use concrete types such as `UInt64`, `Nat`, `Bool`, `ByteArray`, arrays, structures, and inductives; parametric structures and inductives may appear at concrete supported instantiations.  Simple polymorphic helpers can be useful when each call site fixes concrete supported types, while type classes, function values, `IO`, `unsafe`, and `partial` remain outside the accepted subset.

This scalar example compiles to an exported WASM function that Wasmtime can call directly:

```lean
namespace LeanExe.Examples.ReadmeDemo

def choose (flag x y : UInt64) : UInt64 :=
  if flag == 0 then x else y

end LeanExe.Examples.ReadmeDemo
```

Store the file at `LeanExe/Examples/ReadmeDemo.lean`, then build the module:

```sh
lake build LeanExe.Examples.ReadmeDemo
```

The compiler input is the checked Lean declaration loaded from the built module.  The command names the module and the fully qualified entry declaration, and the compiler rejects declarations outside the supported subset.  A rejected program should be treated as outside the language accepted by LeanExe, even if Lean itself can evaluate it.

Use explicit `Nat` fuel for loops and recursive algorithms.  The recursive helper should take fuel as its first argument, return a supported value, and make the recursive call in tail position.  This pattern compiles to a WASM loop instead of relying on Lean's full recursion machinery.

Pure `Id.run do` blocks are accepted for local mutable-state code that Lean elaborates to first-order terms.  Mutable locals may hold scalars, structures, byte arrays, arrays, `Option`, `Except`, products, supported tagged values, and internal recursive pointers when their types satisfy the normal layout rules.  State records may contain heap fields such as `ByteArray` and internal `Array` values.  Nested conditional, `match`, and `if let` assignments compile through Lean's generated local continuations when those continuations remain local and first-order.  Sparse generated matches from `if let` and catch-all arms are accepted for `Option` and nonrecursive user inductives.  Parser-style loops may combine mutable cursors, indexed `ByteArray` reads, mutable byte-array output, mutable arrays, and explicit status values.

`Option` and `Except` do-notation is accepted when Lean elaborates it to first-order `Pure.pure`, `Bind.bind`, and `ForIn.forIn` applications.  `Except` bind chains may call helpers that use accepted loops and may return structured, tagged, array, or byte-array payloads.  Error results short-circuit later binds and later monadic loop iterations, matching standard Lean behavior.

Loops are accepted for scans over `ByteArray`, fixed-width arrays, ranges such as `[start:stop]` or `[start:stop:step]`, and source `while` loops that Lean elaborates through `Lean.Loop`, when the checked monad is `Id`, `Option`, or `Except ε`.  The loop state may be a scalar, `ByteArray`, an array pointer, a product, a structure, a nonrecursive tagged value, or a recursive-inductive pointer value.  Loop bodies may update multiple mutable locals, use nested accepted loops, use `continue` to skip the rest of the current iteration, or use `break` to return the current loop state.  Direct `Array.foldl`, `Array.foldr`, and `ByteArray.foldl` use the same accumulator layout for supported direct-lambda folders, including byte-producing accumulators.

```lean
namespace LeanExe.Examples.ReadmeLoop

def sumToFuel : Nat -> UInt64 -> UInt64 -> UInt64
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      if n == 0 then
        acc
      else
        sumToFuel fuel (n - 1) (acc + n)

def sumTo (n : UInt64) : UInt64 :=
  sumToFuel n.toNat n 0

end LeanExe.Examples.ReadmeLoop
```

User-defined structures and nonrecursive inductives are accepted when every runtime type argument has a concrete supported type and all runtime fields use supported types after substitution.  Structures flatten by field order at the ABI boundary, and inductives flatten to a constructor tag plus payload slots.  Recursive inductives can be used inside compiled programs, including inside internal arrays, but they cannot be entry parameters or entry results.  Public arrays may contain `ByteArray`, nested arrays, `Option`, `Except`, and fixed-width structures or tagged values with heap-reference fields, provided the flattened element layout contains no recursive inductive value.  Public entry structures and tagged values may also contain heap-bearing array fields under the same nonrecursive limit.  Internal arrays may also contain products, recursive-inductive pointers, and fixed-width structures or tagged values that contain recursive pointer fields.  Mutual recursive inductive families are supported as internal data: constructors may refer to another member of the same specialized family directly or through fixed-width arrays.  Ordinary mutual structural traversals over recursive-family members are accepted for Lean's generated nested `PSum` well-founded helper shape.  Monomorphic recursive instances such as `List α` are also accepted internally when `α` has a supported internal layout, including scalar values, structures, nonrecursive tagged values, `ByteArray`, and tagged values such as `Option UInt64`, `Option ByteArray`, and `Except ByteArray UInt64` in the comparison suite.  Supported list operations include construction, matching, helper calls, source-defined traversals that return list values, direct structural recursion, direct `List.concat`, closed structural folds and predicates, heap-bearing `List.foldl` and `List.foldr` result values in the tested shapes, direct `List.any` and `List.all` over the tested element layouts, and branching tree or AST traversals.  Recursive tree traversals through an `Array` child field are accepted for the generated `WellFounded.fix` shape described in the specification.

```lean
namespace LeanExe.Examples.ReadmeData

structure Point where
  x : UInt64
  y : UInt64

inductive Status where
  | ok
  | retry (code : UInt64)
  | fail

def move (p : Point) : Point :=
  { p with x := p.x + 1 }

def statusCode : Status -> UInt64
  | .ok => 0
  | .retry code => code
  | .fail => 999

end LeanExe.Examples.ReadmeData
```

## Compile

Use `compile` to write a WASM binary.  The exported entry name is the final component of the Lean declaration name, so `LeanExe.Examples.ReadmeDemo.choose` exports `choose`.  The module also exports `memory`, `alloc`, `reset`, `retain`, `release`, and `free` for host-side allocation, repeated execution, and reference-counted result lifetime.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.ReadmeDemo \
  --entry LeanExe.Examples.ReadmeDemo.choose \
  --out build/choose.wasm
```

Use `compile-wat` to inspect the generated module as WAT.  Use `report` before compilation when you want to see how the entry declaration and its dependencies classify under the supported subset.  Use `ownership-report` when memory management is the question: it prints each extracted function's result owner slots, helper-result fresh-owner offsets, compiler-emitted release statements, returned owner expressions, fold accumulator release offsets, and source-level `LeanExe.Runtime.release` expressions.

```sh
.lake/build/bin/lean-wasm compile-wat \
  --module LeanExe.Examples.ReadmeDemo \
  --entry LeanExe.Examples.ReadmeDemo.choose \
  --out build/choose.wat

.lake/build/bin/lean-wasm report \
  --module LeanExe.Examples.ReadmeDemo \
  --entry LeanExe.Examples.ReadmeDemo.choose

.lake/build/bin/lean-wasm ownership-report \
  --module LeanExe.Examples.ReadmeDemo \
  --entry LeanExe.Examples.ReadmeDemo.choose
```

Use `compile-wasi` for a command-style module whose selected entry takes no parameters and returns `ByteArray`.  The generated module imports WASI Preview 1 `fd_write`, exports `_start`, and writes the returned bytes to stdout.  This mode does not compile Lean `IO`; the Lean entry remains a pure function.

```sh
.lake/build/bin/lean-wasm compile-wasi \
  --module LeanExe.Examples.Correctness \
  --entry LeanExe.Examples.Correctness.byteArrayStringConstReturn \
  --out build/stdout.wasm
```

Use `compile-wasi-stdin` for a bounded stdin-to-stdout transform.  The selected entry must have type `ByteArray -> ByteArray`.  The generated `_start` reads stdin through WASI `fd_read` until EOF, traps if input exceeds `--max-input-bytes`, calls the pure Lean entry, and writes the returned bytes to stdout.

```sh
.lake/build/bin/lean-wasm compile-wasi-stdin \
  --max-input-bytes 65536 \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.appendBang \
  --out build/stdin-stdout.wasm
```

Use `compile-wasi-stdin-except` when the pure entry reports failure explicitly.  The selected entry must have type `ByteArray -> Except ByteArray ByteArray`.  The generated `_start` reads bounded stdin, calls the Lean entry, writes `Except.ok` bytes to stdout with exit status `0`, and writes `Except.error` bytes to stderr before calling WASI `proc_exit 1`.

```sh
.lake/build/bin/lean-wasm compile-wasi-stdin-except \
  --max-input-bytes 65536 \
  --module LeanExe.Examples.Correctness \
  --entry LeanExe.Examples.Correctness.byteArrayExceptBangOrError \
  --out build/stdin-except.wasm
```

Use `compile-wasi-argv-except` for command arguments.  The selected entry must have type `Array ByteArray -> Except ByteArray ByteArray`.  The generated `_start` reads WASI arguments through `args_sizes_get` and `args_get`, skips `argv[0]`, builds an internal `Array ByteArray` containing the user arguments, and applies the same stdout, stderr, and exit-status rules as `compile-wasi-stdin-except`.  `--max-args` limits user arguments.  `--max-argv-bytes` limits the WASI argument buffer, including `argv[0]` and NUL terminators.

```sh
.lake/build/bin/lean-wasm compile-wasi-argv-except \
  --max-args 16 \
  --max-argv-bytes 4096 \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.argvFirstLast \
  --out build/argv-except.wasm
```

Use `compile-wasi-stdin-argv-except` when a command needs both stdin and arguments.  The selected entry must have type `ByteArray -> Array ByteArray -> Except ByteArray ByteArray`.  The generated `_start` reads bounded stdin, reads bounded WASI argv, skips `argv[0]`, and applies the same stdout, stderr, and exit-status rules as `compile-wasi-stdin-except`.  The stdin bound and argv bounds reserve fixed memory regions before the Lean entry runs.

```sh
.lake/build/bin/lean-wasm compile-wasi-stdin-argv-except \
  --max-input-bytes 8192 \
  --max-args 8 \
  --max-argv-bytes 256 \
  --module LeanExe.Examples.JsonTreeCommand \
  --entry LeanExe.Examples.JsonTreeCommand.searchTree \
  --out build/search-tree.wasm
```

## Run

Scalar parameters and scalar results use WASM `i64`.  `Bool` uses `0` for false and `1` for true.  `Nat` values must fit in the compiler's bounded `i64` representation.

```sh
wasmtime run --invoke choose build/choose.wasm 0 41 99
```

The expected output is:

```text
41
```

The repository examples can be compiled the same way.  `LeanExe.Examples.Collatz.steps` accepts one `UInt64` and returns the number of Collatz steps.  `LeanExe.Examples.Prime.next` accepts one `UInt64` and returns the smallest prime number greater than the input.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.Collatz \
  --entry LeanExe.Examples.Collatz.steps \
  --out build/collatz.wasm

wasmtime run --invoke steps build/collatz.wasm 27
```

A WASI command module runs through Wasmtime without `--invoke`.  The stdout modes make byte-producing programs observable as command programs, and the `Except` mode also exposes stderr and a nonzero exit status for source-level errors.

```sh
wasmtime run build/stdout.wasm
printf AB | wasmtime run build/stdin-stdout.wasm
printf AB | wasmtime run build/stdin-except.wasm
wasmtime run build/argv-except.wasm alpha omega
```

`LeanExe.Examples.JsonTreeCommand` demonstrates a two-command JSON pipeline.  `makeTree` reads a JSON array from stdin, parses it through the ASCII JSON AST parser, and writes a binary-search tree as JSON.  `searchTree` reads that JSON tree from stdin, parses it through the same AST parser, decodes it into the source-level `Tree` type, reads the search key from argv, and writes a JSON boolean result.

`LeanExe.Examples.JsonTypedDecode` demonstrates typed JSON decoding over the AST.  It decodes a JSON object into a source-defined `Request` structure, rejects missing, duplicate, unknown, and mistyped fields, computes checked aggregate values, and returns JSON through the WASI `Except` adapter.

`LeanExe.Examples.JsonObjectArrayDecode` extends the typed decoder style to arrays of source-defined structures.  It decodes a request whose `items` field contains objects with `id` and `weight` fields, computes a scaled weighted sum, rejects malformed nested values, and returns compact JSON through the WASI `Except` adapter.

`LeanExe.Examples.JsonMergeTreeCommand` extends that pipeline with explicit RC observation.  `makeMergedTree` reads two JSON arrays, builds one tree for each, copies both into a third merged tree, releases replaced accumulator roots during immutable insertion, releases the first two final source roots, and writes the merged tree plus GC counters and source node counts.  `searchMergedTree` reads that intermediate object and searches the final tree.

`LeanExe.Examples.JsonGcTreeRewrite` is a single-command GC exercise.  It reads a JSON object with `depth`, `rounds`, `salt`, and `search`, builds a balanced tree, rewrites whole tree generations, releases each old root after the next generation exists, releases the final root after computing metrics, and writes a JSON result with allocation, release, and free counters.

```sh
printf '%s' '[1,6,4,100,33,5,5,20]' \
  | wasmtime run build/make-tree.wasm \
  | wasmtime run build/search-tree.wasm 4
```

## Compare With Standard Lean

Use `tools/compare-standard.js` to compare accepted entries against standard Lean execution.  The tool generates a temporary Lean runner under `.lake/build/standard-compare`, runs it with `lake env lean --run`, compiles the same entry through LeanExe, runs the generated WASM with Wasmtime, and compares the observed results.  Command modes compare exit status, stdout, and stderr byte-for-byte for `ByteArray`, `ByteArray -> ByteArray`, `ByteArray -> Except ByteArray ByteArray`, `Array ByteArray -> Except ByteArray ByteArray`, and `ByteArray -> Array ByteArray -> Except ByteArray ByteArray` entries.

Pure mode compares scalar library exports invoked through `wasmtime --invoke`; the caller supplies the standard Lean call expression when flattened WASM parameters differ from the Lean source call, and supplies a result-slot expression of type `Array UInt64` for the flattened return value.  Pure-ABI mode compares library exports through the Wasmtime C host runner and decodes heap-backed public ABI results from exported memory using a JSON layout descriptor.  The standard Lean side serializes the same value to JSON through `--serializer`, so this mode can compare public structures, tagged values, byte arrays, and arrays without compiling a generated WASI wrapper.  Pure-bytes mode compares a concrete pure call by serializing its result to `ByteArray`, compiling a generated wrapper through `compile-wasi`, and comparing the bytes written by standard Lean with the bytes written by the generated WASM command.

`--abi-layout` accepts JSON descriptors for public ABI values: scalar names such as `"UInt64"` and `"Nat"`, `"ByteArray"`, `{"array": ...}`, `{"struct": [["field", ...], ...]}`, and `{"tagged": [[...], ...]}`.  `--abi-arg` supplies heap-bearing host arguments in the same descriptor-value shape when scalar `--arg` values are insufficient.  The generated standard Lean runner defines small JSON serializer helpers such as `__leanexeJsonUInt64`, `__leanexeJsonArray`, and `__leanexeJsonByteArray` for comparison expressions.

```sh
node tools/compare-standard.js \
  --mode stdin-except \
  --module LeanExe.Examples.JsonGcd \
  --entry transform \
  --stdin '[48,18,30]'
```

```sh
node tools/compare-standard.js \
  --mode pure \
  --module LeanExe.Examples.Correctness \
  --entry structureReturn \
  --arg 4 \
  --result-slots '#[__leanexeValue.x, __leanexeValue.y]'
```

```sh
node tools/compare-standard.js \
  --mode pure-bytes \
  --module LeanExe.Examples.Correctness \
  --entry byteArrayReturnABC \
  --serializer '__leanexeValue'
```

```sh
node tools/compare-standard.js \
  --mode pure-abi \
  --module LeanExe.Examples.Correctness \
  --entry publicByteArrayArrayReturn \
  --abi-layout '{"array":"ByteArray"}' \
  --serializer '__leanexeJsonArray __leanexeValue __leanexeJsonByteArray'
```

```sh
node tools/compare-standard.js \
  --mode pure-abi \
  --module LeanExe.Examples.Correctness \
  --entry publicByteArrayArrayOpsReturn \
  --abi-layout '{"array":"ByteArray"}' \
  --abi-arg '{"layout":{"array":"ByteArray"},"value":[[65],[66,67],[68,69,70]]}' \
  --standard-call 'LeanExe.Examples.Correctness.publicByteArrayArrayOpsReturn #["A".toUTF8, "BC".toUTF8, "DEF".toUTF8]' \
  --serializer '__leanexeJsonArray __leanexeValue __leanexeJsonByteArray'
```

Run the built-in comparison cases with:

```sh
node tools/compare-standard.js --self-test
```

## Host Memory Values

`ByteArray` and arrays use the module memory.  The module exports `alloc(len : i64) : i64`; a host calls `alloc`, writes bytes into the exported memory, and passes the returned pointer plus a length when the entry expects a `ByteArray`.  The allocator grows WASM memory when no free block and no current heap range can satisfy a request.  Returned byte arrays use a pointer and length result pair at the public ABI, while compiled code carries an internal owner slot so stored byte-array slices can keep their allocation root alive.  The module also exports `retain(ptr : i64) : i64`, `release(ptr : i64)`, and `free(ptr : i64)` for reference-counted heap objects.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.AsciiDigits \
  --entry LeanExe.Examples.AsciiDigits.validateGeneric \
  --out build/bytes.wasm
```

```sh
tools/build-wasmtime-host.sh
build/tools/leanexe-wasmtime-host call build/bytes.wasm validateGeneric i64 bytes:3132333435
```

The expected output is:

```text
1
```

When a library-mode result points into module memory, read or copy the result before calling `release` or `reset`.  `release` decrements the object's reference count and returns the block to the runtime free list when the count reaches zero.  Public `ByteArray` results expose only pointer and length, so a returned slice may not be a releasable root pointer; use `reset` at a call boundary or release only when the program's result protocol guarantees a root pointer.  `reset` rewinds the whole heap and invalidates every old pointer, regardless of reference count.

The compiler emits `release` for local heap temporaries only when the released owner is nonrecursive, currently `ByteArray` or `Array`, and the owner comes from a visible fresh allocation or helper-call result.  This lets scalar-result helpers reclaim internal arrays and byte arrays before returning, and it lets heap-result functions release fresh nonrecursive owners after result materialization when those owners are absent from returned heap roots and borrowed root expressions.  Ordinary recursive heap temporaries remain conservative: the compiler may leak them, but it must not release them unless an explicit source-level ownership boundary or a supported accumulator-replacement rule applies.  Recursive heap allocation retains borrowed child pointers and transfers child pointers proven fresh by the same ownership summaries.  `Array.foldl`, `Array.foldr`, `ByteArray.foldl`, and accepted loops release replaced heap-valued accumulator owner slots after the first iteration when the replacement is proven fresh and the loop body has not already released the old slot.  The compiler skips the initial accumulator value for this rule because ordinary Lean aliases can still refer to that value after the loop.  It keeps heap-pointer helper results that may borrow from heap arguments conservative: hosts remain responsible for releasing returned arrays and byte arrays after reading them.

Compiled Lean code can read runtime counters with `LeanExe.Runtime.allocCount`, `retainCount`, `releaseCount`, and `freeCount`.  Source code can call `LeanExe.Runtime.release value` for a monomorphic recursive-inductive root or an array value when the program has an explicit ownership boundary.  The extractor preserves `let _ := LeanExe.Runtime.release value`, so a program can mark a boundary without using the returned counter.  The released value, and any heap node shared with a live value, must not be used after the call; the compiler does not yet prove that ownership condition.  Array and recursive-value release follows recursive-inductive child pointers, `ByteArray` owner slots, and nested `Array` owner slots in fixed-width layouts.  Releasing a borrowed public array with owner `0` is a no-op.

Fixed-width arrays use the compiler's heap layout.  Scalar values occupy one slot, `ByteArray` elements occupy owner, pointer, and length slots, nested `Array` elements occupy owner and pointer slots, products and fixed-width structures or tagged values occupy their flattened slot count, and recursive inductive values occupy one pointer slot.  Public entry arrays use the same fixed-width layout for scalar elements, byte arrays, nested arrays, structures, and tagged values, but they exclude recursive inductive values.  Structure values flatten field-by-field at the ABI boundary, while nonrecursive inductive values flatten to a constructor tag followed by payload slots.  Recursive inductive values are supported as internal values, including recursive pointer fields inside internal fixed-width structures and tagged values, mutual-family pointers, monomorphic `List` construction, matching, direct traversal over one or more direct recursive fields, mutual structural traversal over recursive-family members, source-defined list builders such as append and reverse, generated array-child traversal, explicit-accumulator `List.foldl` helpers, top-level closed `List.foldl` bodies with one hidden accumulator, closed structural predicates such as direct `List.any` and `List.all`, direct expression-position `List.length`, list append notation through `++`, `List.concat`, `List.reverse`, `List.map`, `List.filter`, and `List.foldr` with closed direct-lambda callbacks, expression-position structural recursion that captures supported first-order surrounding values, and limited direct-lambda helper calls to `List.map`, `List.filter`, `List.find?`, `List.foldl`, `List.any`, and `List.all`, but entry parameters and entry results cannot expose recursive data through the host ABI.

## Supported Lean

The supported subset is practical but restricted.  Programs should use concrete, first-order definitions with no runtime-polymorphic functions or type-class resolution at the entry boundary.  Helper definitions may be separate Lean declarations as long as the compiler can classify every reachable dependency.

Supported values include `Unit`, `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, `ByteArray`, `LeanExe.AsciiString`, `Array`, products, internal `PSum`, user-defined structures, user-defined inductives, `Option`, `Except`, monomorphic self-recursive inductives, mutual recursive inductive families, and monomorphic recursive instances such as `List α` when `α` has a supported internal layout.  `UInt8` and `UInt32` may appear at the public entry boundary as one-slot scalar values, where inputs and outputs are reduced modulo their fixed width.  Public arrays may store byte arrays, nested arrays, and fixed-width structures or tagged values containing those heap fields.  Internal arrays may also store products, recursive-inductive pointer fields, and fixed-width structures or tagged values containing those pointers.  Equality through `==`, `!=`, and decided equality propositions supports scalars, byte arrays, fixed-width arrays whose element type supports equality, products, structures, internal sums, `Option`, `Except`, and nonrecursive tagged values when every runtime field supports equality.  Recursive-inductive equality remains unsupported.  `LeanExe.AsciiString` is a one-field structure over `ByteArray` with explicit validation helpers for the ASCII invariant.  Restricted compile-time ASCII `String` expressions may be converted to bytes with `.toUTF8`, measured with `.length`, tested with `.isEmpty`, and compared with `==` or `!=`.

Supported control flow includes `let`, direct calls, `if`, pattern matching, pure `do` notation with local mutable assignments, pure `for` and `while` loops with supported accumulator values, bounded recursion over an explicit `Nat` fuel argument, direct structural recursion over recursive inductives, mutual structural recursion over recursive-family members, expression-position structural recursion with supported first-order post-arguments and supported captured values, a top-level closed `List.foldl` shape with one hidden accumulator, closed structural predicates for direct `List.any` and `List.all`, generated `Array`-child recursion, inline-specialized first-order polymorphic helpers, and selected direct-lambda library calls that specialize to first-order code.  Fuel-recursive functions may branch through nested `if` and supported inductive matches when tail calls remain in the accepted loop shape, and recursive-descent helpers may use non-tail self-calls when they consume decremented fuel and then inspect the returned value.  Pure `do` assignments may elaborate through local continuation lambdas, flattened generated matchers over nested single-constructor accumulator structures, and `PUnit`; those checked forms compile when the continuations normalize away to first-order values.  Unsupported features include shared generic runtime functions, type classes, higher-order functions, closures that survive normalization, full `IO`, runtime `String`, runtime `Char`, arbitrary Lean and Std library functions, hidden carried arguments outside the accepted expression-position, unsupported structural-recursion shapes, mutual recursion outside the nested `PSum` shapes described in the specification, `unsafe`, `partial`, unbounded natural-number arithmetic, course-of-values recursion, exported recursive data structures, and public arrays of recursive values.  These features remain outside the accepted language even when Lean accepts the source file.

## ABI Summary

| Lean type | WASM ABI |
|-----------|----------|
| `Bool` | One `i64`, with `0` or `1`. |
| `UInt8` | One `i64`, reduced modulo `2^8`. |
| `UInt32` | One `i64`, reduced modulo `2^32`. |
| `UInt64` | One `i64`, interpreted modulo `2^64`. |
| `Nat` | One nonnegative `i64` within the supported bound. |
| `ByteArray` parameter | Pointer and length, both `i64`. |
| `ByteArray` result | Pointer and length, both `i64`. |
| `Array α` | Pointer to a heap array whose elements have fixed-width slots. |
| Structure | Field values flattened in declaration order. |
| Nonrecursive inductive | Constructor tag followed by payload slots. |
| Recursive inductive | Internal heap value only. |

The entry declaration name must not collide with runtime exports such as `memory`, `alloc`, `reset`, `retain`, `release`, or `free`.  The host may call `release()` for individual returned heap objects or `reset()` when no old pointer remains live.  Integer overflow and invalid memory access trap according to the semantics in [Language Specification](spec.md).

## Examples

The examples directory contains small programs that exercise the user-facing subset:

| Module | Entry | Description |
|--------|-------|-------------|
| `LeanExe.Examples.Collatz` | `steps` | Counts Collatz steps for a `UInt64` input. |
| `LeanExe.Examples.Prime` | `next` | Computes the smallest prime greater than a `UInt64` input. |
| `LeanExe.Examples.IntMap` | `checksum`, `query` | Uses a small structure-backed integer map written in the subset. |
| `LeanExe.Examples.ByteArrayPrograms` | Several entries | Validates and transforms `ByteArray` inputs. |
| `LeanExe.Examples.AsciiStringPrograms` | Several entries | Validates and transforms ASCII byte strings. |
| `LeanExe.Examples.JsonDouble` | `transform` | Parses a small ASCII JSON request and returns JSON bytes. |
| `LeanExe.Examples.JsonAdd` | `transform` | Parses two decimal JSON fields and returns their checked sum. |
| `LeanExe.Examples.JsonCollatzLength` | `transform` | Parses a decimal Collatz request and returns the sequence length. |
| `LeanExe.Examples.JsonGcd` | `transform` | Reads a JSON array from stdin and writes a JSON GCD result through WASI. |
| `LeanExe.Examples.JsonTypedDecode` | `transform` | Decodes a JSON object into a source-defined request structure and writes checked aggregate results through WASI. |
| `LeanExe.Examples.JsonObjectArrayDecode` | `transform` | Decodes a JSON object containing an array of source-defined item structures through WASI. |
| `LeanExe.Examples.JsonTreeCommand` | `makeTree`, `searchTree` | Builds a simple JSON binary-search tree and searches it through a WASI pipeline. |
| `LeanExe.Examples.JsonMergeTreeCommand` | `makeMergedTree`, `searchMergedTree` | Merges two JSON integer-array trees, releases the source trees, and reports runtime GC counters. |
| `LeanExe.Examples.JsonGcTreeRewrite` | `transform` | Rewrites balanced tree generations, releases old roots, and reports runtime GC counters. |
| `LeanExe.Examples.JsonTools` | `transform`, `lookup` | Exercises limited JSON field lookup and object generation helpers. |
| `LeanExe.Examples.Correctness` | Many entries | Exercises structures, inductives, arrays, recursion, and edge cases. |

Use the examples as templates for new programs.  Start with a scalar entry when possible, then add memory values once the scalar logic compiles and tests pass.  Keep helper functions concrete and first-order so the dependency classifier can prove that the whole call graph belongs to the accepted subset.
