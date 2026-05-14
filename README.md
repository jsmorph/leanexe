# LeanExe

LeanExe compiles a restricted Lean 4 program to a standalone WebAssembly module.  Lean remains the type checker and source language; the compiler loads a checked declaration from a Lean module and emits WASM for the executable subset described in [Language Specification](spec.md).  The supported subset covers first-order pure programs over scalar values, byte arrays, fixed-width arrays, structures, inductive values, bounded recursion, and internal recursive data structures.

The default generated module exports a plain WASM function for the selected Lean declaration.  Scalar programs can run directly with Wasmtime or another WASM engine that can invoke exported functions.  Programs that pass or return byte arrays, structures, variants, or arrays use the ABI described below, so a host program must provide flattened values or memory values in the expected form.  WASI command modes provide stdout output, bounded stdin input, and an error-aware byte transform without compiling Lean `IO`.

## Requirements

This repository uses Lean through `elan` and Lake.  The pinned Lean version lives in `lean-toolchain`, and Lake builds the `lean-wasm` executable.  A standalone WASM engine such as Wasmtime can run scalar examples and WASI command examples from the command line, while a JavaScript, Go, Rust, or C host can instantiate modules that use memory values.

```sh
lake build
```

The test suite uses Node for the existing instantiation checks, including host-memory checks, and Wasmtime for command-style WASM execution.  Wasmtime is not required for the compiler itself, but the full repository test suite expects the downloaded binary at `build/tools/wasmtime/current/wasmtime` or a `WASMTIME` environment variable.  If Wasmtime is not on `PATH`, use the absolute path to the downloaded binary.

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
| `spec.md` | The accepted Lean subset, ABI, semantics, and known unsupported features. |
| `plan.md` | Development plan for expanding the compiler. |
| `devnotes.md` | Development notes and references. |

## Write a Program

Write ordinary Lean definitions inside a Lake module.  The selected entry declaration must be pure, monomorphically specialized at runtime, first-order, and accepted by the subset in [Language Specification](spec.md).  Use concrete types such as `UInt64`, `Nat`, `Bool`, `ByteArray`, arrays, structures, and inductives; parametric structures and inductives may appear at concrete supported instantiations.  Simple polymorphic helpers can be useful when each call site fixes concrete supported types, while type classes, function values, `IO`, `unsafe`, and `partial` remain outside the accepted subset.

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

Pure `Id.run` `for` loops are also accepted for simple scans over `ByteArray`, fixed-width arrays, and ranges such as `[start:stop]` or `[start:stop:step]`.  The loop state may be a scalar, `ByteArray`, an array pointer, a product, a structure, a nonrecursive tagged value, or a recursive-inductive pointer value.  The loop body may update the accumulator, use `continue` to skip the rest of the current iteration, or use `break` to return the current loop state.  Direct `Array.foldl` and `ByteArray.foldl` use the same accumulator layout for supported direct-lambda folders, including byte-producing accumulators.

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

User-defined structures and nonrecursive inductives are accepted when every runtime type argument has a concrete supported type and all runtime fields use supported types after substitution.  Structures flatten by field order at the ABI boundary, and inductives flatten to a constructor tag plus payload slots.  Recursive inductives can be used inside compiled programs, including inside internal arrays, but they cannot be entry parameters or entry results.  Internal arrays may contain nested arrays, products, recursive-inductive pointers, and fixed-width structures or tagged values that contain array or recursive pointer fields.  Public arrays remain limited to scalar, structure, and tagged fixed-width elements whose layouts contain no nested heap references.  Mutual recursive inductive families are supported as internal data: constructors may refer to another member of the same specialized family directly or through fixed-width arrays.  Ordinary mutual structural traversals over recursive-family members are accepted for Lean's generated nested `PSum` well-founded helper shape.  Monomorphic recursive instances such as `List UInt64` are also accepted internally for construction, matching, helper calls, source-defined traversals that return list values, direct structural recursion, closed structural folds and predicates, and branching tree or AST traversals.  Recursive tree traversals through an `Array` child field are accepted for the generated `WellFounded.fix` shape described in the specification.

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

Use `compile` to write a WASM binary.  The exported entry name is the final component of the Lean declaration name, so `LeanExe.Examples.ReadmeDemo.choose` exports `choose`.  The module also exports `memory`, `alloc`, and `reset` for host-side allocation and repeated execution.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.ReadmeDemo \
  --entry LeanExe.Examples.ReadmeDemo.choose \
  --out build/choose.wasm
```

Use `compile-wat` to inspect the generated module as WAT.  Use `report` before compilation when you want to see how the entry declaration and its dependencies classify under the supported subset.  The report command is the best first diagnostic when a program does not compile.

```sh
.lake/build/bin/lean-wasm compile-wat \
  --module LeanExe.Examples.ReadmeDemo \
  --entry LeanExe.Examples.ReadmeDemo.choose \
  --out build/choose.wat

.lake/build/bin/lean-wasm report \
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

## Host Memory Values

`ByteArray` and arrays use the module memory.  The module exports `alloc(len : i64) : i64`; a host calls `alloc`, writes bytes into the exported memory, and passes the returned pointer plus a length when the entry expects a `ByteArray`.  Returned byte arrays use a pointer and length result pair.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.AsciiDigits \
  --entry LeanExe.Examples.AsciiDigits.validateGeneric \
  --out build/bytes.wasm
```

```js
import fs from "node:fs";

const bytes = fs.readFileSync("build/bytes.wasm");
const { instance } = await WebAssembly.instantiate(bytes, {});
const input = new TextEncoder().encode("12345");
const ptr = Number(instance.exports.alloc(BigInt(input.length)));
new Uint8Array(instance.exports.memory.buffer, ptr, input.length).set(input);

const ok = instance.exports.validateGeneric(BigInt(ptr), BigInt(input.length));
console.log(ok === 1n ? "accepted" : "rejected");
```

Fixed-width arrays use the compiler's arena layout.  Scalar values occupy one slot, `ByteArray` elements occupy pointer and length slots, products and fixed-width structures or tagged values occupy their flattened slot count, and heap-backed internal values such as nested arrays and recursive inductives occupy one pointer slot.  Structure values flatten field-by-field at the ABI boundary, while nonrecursive inductive values flatten to a constructor tag followed by payload slots.  Recursive inductive values are supported as internal values, including recursive pointer fields inside internal fixed-width structures and tagged values, mutual-family pointers, monomorphic `List UInt64` construction, matching, direct traversal over one or more direct recursive fields, mutual structural traversal over recursive-family members, source-defined list builders such as append and reverse, generated array-child traversal, explicit-accumulator `List.foldl` helpers, top-level closed `List.foldl` bodies with one hidden accumulator, closed structural predicates such as direct `List.any` and `List.all`, direct expression-position `List.length`, list append notation through `++`, `List.reverse`, `List.map`, `List.filter`, and `List.foldr` with closed direct-lambda callbacks, and limited direct-lambda helper calls to `List.map`, `List.filter`, `List.find?`, and `List.any`, but entry parameters and entry results cannot expose recursive data, byte-array arrays, or nested arrays through the host ABI.

## Supported Lean

The supported subset is practical but restricted.  Programs should use concrete, first-order definitions with no runtime-polymorphic functions or type-class resolution at the entry boundary.  Helper definitions may be separate Lean declarations as long as the compiler can classify every reachable dependency.

Supported values include `Unit`, `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, `ByteArray`, `LeanExe.AsciiString`, `Array`, products, internal `PSum`, user-defined structures, user-defined inductives, `Option`, `Except`, monomorphic self-recursive inductives, mutual recursive inductive families, and monomorphic recursive instances such as `List UInt64`.  `UInt8` and `UInt32` may appear at the public entry boundary as one-slot scalar values, where inputs and outputs are reduced modulo their fixed width.  Internal arrays may store byte arrays, nested arrays, products, recursive-inductive pointer fields, and fixed-width structures or tagged values containing those pointers.  `LeanExe.AsciiString` is a one-field structure over `ByteArray` with explicit validation helpers for the ASCII invariant.  Restricted compile-time ASCII `String` expressions may be converted to bytes with `.toUTF8`, measured with `.length`, tested with `.isEmpty`, and compared with `==` or `!=`.

Supported control flow includes `let`, direct calls, `if`, pattern matching, pure `do` notation, bounded tail recursion over an explicit `Nat` fuel argument, direct structural recursion over recursive inductives, mutual structural recursion over recursive-family members, expression-position structural recursion with supported first-order post-arguments, a top-level closed `List.foldl` shape with one hidden accumulator, closed structural predicates for direct `List.any` and `List.all`, generated `Array`-child recursion, inline-specialized first-order polymorphic helpers, and selected direct-lambda library calls that specialize to first-order code.  Unsupported features include shared generic runtime functions, type classes, higher-order functions, closures, full `IO`, runtime `String`, runtime `Char`, arbitrary Lean and Std library functions, hidden carried arguments outside the accepted expression-position, closed structural-fold, structural-predicate, generated array-descent, mutual recursion outside the nested `PSum` shapes described in the specification, `unsafe`, `partial`, unbounded natural-number arithmetic, course-of-values recursion, exported recursive data structures, public nested arrays, and public arrays of recursive values.  These features remain outside the accepted language even when Lean accepts the source file.

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
| `Array α` | Pointer to an arena array whose elements have fixed-width slots. |
| Structure | Field values flattened in declaration order. |
| Nonrecursive inductive | Constructor tag followed by payload slots. |
| Recursive inductive | Internal arena value only. |

The entry declaration name must not collide with runtime exports such as `memory`, `alloc`, or `reset`.  The host may call `reset()` between runs to clear the module allocator.  Integer overflow and invalid memory access trap according to the semantics in [Language Specification](spec.md).

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
| `LeanExe.Examples.JsonTools` | `transform`, `lookup` | Exercises limited JSON field lookup and object generation helpers. |
| `LeanExe.Examples.Correctness` | Many entries | Exercises structures, inductives, arrays, recursion, and edge cases. |

Use the examples as templates for new programs.  Start with a scalar entry when possible, then add memory values once the scalar logic compiles and tests pass.  Keep helper functions concrete and first-order so the dependency classifier can prove that the whole call graph belongs to the accepted subset.
