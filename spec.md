# LeanExe Language Specification

LeanExe accepts a restricted executable subset of Lean 4 and emits a standalone WebAssembly module for one selected entry declaration.  Lean remains the parser, elaborator, type checker, and proof checker.  The compiler reads checked declarations from the Lean environment, rejects declarations outside this specification, and emits WASM only for accepted programs.

The language targets deterministic pure programs over machine integers, byte buffers, arrays, structures, and inductive values.  It supports enough Lean to write conventional first-order programs with bounded loops and recursive helper data structures.  Effects such as `IO`, file access, host calls, concurrency, randomness, and time are outside the accepted language until they have an explicit WASM import model.

## Compilation Model

The compiler input is a module name and a fully qualified Lean declaration name.  The module must already build under Lake or otherwise be visible to Lean's module loader.  The compiler imports that module, finds the checked declaration, computes runtime-relevant dependencies rooted at the module's root namespace, and lowers the accepted call graph.

An entry declaration must be a named constant with an executable value.  It must be safe, non-`partial`, monomorphic at runtime, first-order, and closed after Lean elaboration.  Helper declarations should live under the same root namespace as the imported module; external declarations compile only when LeanExe implements them as primitives.

Proofs may appear in source files and in proof fields of supported structures or inductives.  Proof arguments and proof fields are erased when they have no runtime content.  A theorem, proposition, quotient, axiom, opaque executable constant, unsafe declaration, or effectful declaration cannot contribute executable behavior to an accepted program.

The command-line entry point for generic compilation is:

```sh
.lake/build/bin/lean-wasm compile \
  --module Module.Name \
  --entry Module.Name.entry \
  --out build/entry.wasm
```

`compile-wat` emits text-format WASM for inspection.  `report --module Module.Name --entry Module.Name.entry` imports the same module and prints the entry shape, dependency frontier, and first rejection reasons.  A program that Lean accepts but LeanExe rejects lies outside this language.

## WASM Module ABI

A generated module exports one 16-page linear memory, `alloc(len : i64) : i64`, `reset()`, and the selected entry function.  The arena starts at byte offset `4096`, and `alloc` returns byte offsets in that memory.  The host may call `reset()` between runs to clear arena allocations; returned pointers remain valid only until `reset`.

The entry export name is the last component of the Lean declaration name.  For example, `My.Module.answer` exports `answer`.  The entry name must not be `memory`, `alloc`, or `reset`, because those names belong to the runtime ABI.

Every scalar ABI slot is a WASM `i64`.  `Bool` uses `0` for false and `1` for true.  `UInt64` uses the full unsigned 64-bit representation, and `Nat` uses the bounded unsigned representation described below.

`ByteArray` crosses the ABI as two slots: byte pointer and byte length.  Structure values flatten their runtime fields in Lean declaration order after proof-field erasure.  Nonrecursive inductive values flatten as a constructor tag followed by payload slots for every constructor in declaration order; inactive payload slots are ignored on input and may hold default values on output.

Arrays cross the ABI as arena pointers.  Array elements must have a fixed slot width, and the pointed-to layout starts with the array length as an `i64` header followed by flattened element slots.  Recursive inductive values are internal heap values and cannot cross the public entry ABI.

## Types

| Lean type | Entry parameter | Entry result | Internal value | Notes |
|-----------|-----------------|--------------|----------------|-------|
| `Unit` | No | No | Yes | Runtime value is erased to a zero-valued scalar where needed. |
| `Bool` | Yes | Yes | Yes | ABI slot is `0` or `1`. |
| `UInt8` | No | No | Yes | Used by `ByteArray`, arrays, and helper code. |
| `UInt32` | No | No | Yes | Used by helper code and byte-oriented algorithms. |
| `UInt64` | Yes | Yes | Yes | Main scalar integer type for public entries. |
| `Nat` | Yes | Yes | Yes | Runtime values must fit in the bounded `i64` representation. |
| `ByteArray` | Yes | Yes | Yes | ABI is pointer and length. |
| `LeanExe.AsciiString` | Yes | Yes | Yes | One-field structure over `ByteArray`; validation is explicit. |
| `Array α` | Yes | Yes | Yes | `α` must have a fixed-width array layout. |
| `Prod α β` | No | No | Yes | Products are internal values with lazy projection behavior. |
| Structure | Yes | Yes | Yes | Monomorphic, nonrecursive structures with supported runtime fields. |
| User inductive | Yes | Yes | Yes | Monomorphic, nonrecursive inductives with supported runtime fields. |
| Recursive inductive | No | No | Yes | Monomorphic self-recursive inductives are allowed inside accepted code. |
| `Option α` | Yes | Yes | Yes | Treated as a supported tagged value when `α` is supported. |
| `Except ε α` | Yes | Yes | Yes | Treated as a supported tagged value when both payload types are supported. |
| Propositions | Erased | Erased | Erased | Proofs may justify Lean source but have no WASM value. |
| `String` | No | No | No | Use `ByteArray` for byte input and output. |

Entry parameters support `Bool`, `UInt64`, bounded `Nat`, `ByteArray`, fixed-width `Array`, supported structures, supported nonrecursive inductives, `Option`, and `Except`.  Entry results support the same set.  `UInt8`, `UInt32`, `Unit`, products, and recursive inductives are internal-only types even though helpers may use them.

An array element type is fixed-width when LeanExe can assign a constant number of `i64` slots to each element.  The accepted element types are `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, supported structures, supported nonrecursive inductives, `Option`, and `Except`.  Nested arrays and arrays of recursive inductive values are unsupported.

## Numeric Semantics

`UInt64` arithmetic uses the unsigned 64-bit Lean semantics.  Addition, subtraction, and multiplication wrap modulo `2^64`.  Division by zero returns `0`, and remainder by zero returns the dividend, matching Lean's fixed-width integer behavior.

`UInt8` and `UInt32` are represented internally as constrained `i64` values.  Literals and `ofNat` conversions reduce modulo `2^8` or `2^32`, arithmetic wraps to the same width, and conversions to wider supported types preserve the constrained value.  Shifts mask the shift amount modulo the type width before shifting.

Runtime `Nat` uses an unsigned 64-bit bound rather than arbitrary precision.  A runtime `Nat` literal must be less than `2^64` unless it is consumed directly by a fixed-width conversion that defines its own modulo behavior.  `Nat` subtraction is saturating, `Nat.pred` uses that saturation, and `Nat.succ` uses checked addition.

`Nat` addition and multiplication trap when the result would exceed the bounded representation.  `Nat` division by zero returns `0`, and `Nat` remainder by zero returns the dividend.  `Nat.beq`, `Nat.blt`, `Nat.ble`, `Nat.min`, and `Nat.max` use unsigned comparisons over the bounded representation.

Supported comparisons and equality include scalar equality for `Bool`, `UInt8`, `UInt32`, `UInt64`, and `Nat`; unsigned comparisons for supported numeric scalars; and boolean operations `&&`, `||`, `!`, and `Bool.xor`.  Short-circuiting boolean operations preserve Lean evaluation order.  Unsupported numeric types, arbitrary-precision runtime arithmetic, signed integer operations, and floating-point operations are outside the language.

## Terms and Control Flow

The accepted term language is first-order.  It includes variables, local `let`, direct calls to accepted helpers, numeric literals, constructors, projections, `if`, dependent `if` with erased proof binders, pattern matching, pure `Id` `do` notation, and a restricted fuel-recursive loop shape.  It excludes higher-order arguments, closures, polymorphic runtime values, type-class-driven runtime dispatch, opaque executable constants, and arbitrary recursors.

Local `let` bindings preserve Lean evaluation behavior for lazy internal values.  A demanded field, branch, or projection extracts only the value needed by the result.  This matters for products, options, structures, and branch-selected values whose unused components may contain trapping expressions.

Named helper calls are allowed when the helper has a supported internal type and lives under the same root namespace as the entry module.  Nonrecursive helpers are extracted directly or inlined as needed.  The identity function, `Id.run`, `Pure.pure`, `Bind.bind`, `Applicative.toPure`, `Monad.toApplicative`, and `Monad.toBind` are erased for pure `Id` code.

Pattern matching is supported for `Bool`, nonrecursive `Nat` zero/successor matches, products, structures, nonrecursive user inductives, recursive user inductives in internal positions, `Option`, and `Except`.  Branch results must have a common supported value shape.  Proposition-valued motives and dependent runtime result shapes are unsupported.

The accepted recursive function shape uses a first `Nat` fuel parameter that decreases on each recursive call.  The function may carry scalar values, byte arrays, arrays, structures, nonrecursive tagged values, and internal recursive inductive pointers through the loop.  The recursive branch must be a tail call or an `if` whose supported branch returns the tail call, and the base or early-exit value must have a supported result type.

## Structures and Inductives

A supported structure has no type parameters, no indices, one constructor, no recursion, and runtime fields whose types are supported.  Constructors, field projections, structure-update elaborations, single-constructor matches, entry parameters, local values, helper parameters, helper results, arrays of structures, and exported structure results are accepted.  Proof fields are removed from the runtime layout.

A supported nonrecursive user inductive has no type parameters, no indices, at least one constructor, and runtime constructor fields whose types are supported.  Constructors, generated matcher extraction, nullary enum matches, branch-selected values, entry parameters, local values, helper values, arrays of tagged values, and exported results are accepted.  The ABI tag is the constructor index in Lean constructor order.

A supported recursive user inductive is monomorphic, self-recursive, and non-mutual.  Constructor fields may contain the inductive itself or other supported nonrecursive field types.  Recursive values may be constructed, matched, stored in locals, passed to helpers, returned from helpers, selected by branches, and carried through accepted fuel-recursive loops.

Recursive inductive values do not have a public entry ABI yet.  They cannot appear as entry parameters, entry results, array elements, structure fields exposed through entry values, or nonrecursive inductive payloads exposed through entry values.  Indexed inductives, mutual inductives, polymorphic inductives, recursive structures, inherited-field structure flattening, and unsupported runtime fields are rejected.

## Arrays

`Array α` values use a copy-on-write arena layout.  The first `i64` cell stores the length, and element cells follow immediately.  A one-slot element at index `i` lives at byte offset `8 * (i + 1)`, while a width-`w` element uses slots `8 * (1 + i * w + s)` for slot `s`.

Accepted scalar element types are `Bool`, `UInt8`, `UInt32`, `UInt64`, and bounded `Nat`.  Supported structures flatten by field order, and supported tagged values store the tag followed by payload slots for every constructor.  Fixed-width array operations preserve old arrays by allocating a new array for updates.

Array literals compile when Lean elaborates them as `List.toArray` over a literal list whose item type has a fixed-width layout.  The supported constructors are `Array.empty`, `Array.mkEmpty`, `Array.emptyWithCapacity`, `Array.singleton`, and `Array.replicate`.  Capacity arguments are not observable in the accepted language.

The supported read operations are `Array.size`, `Array.isEmpty`, proof-indexed `a[i]`, `a[i]!`, `a[i]?`, `Array.getD`, `Array.back`, `Array.back!`, and `Array.back?`.  Trapping reads emit WASM `unreachable` on out-of-bounds access.  Safe reads return `Option` values without reading an element payload when the index is out of bounds.

The supported update and sequence operations are `Array.set`, `Array.set!`, `Array.setIfInBounds`, `Array.modify`, `Array.push`, `Array.pop`, `Array.append`, append notation through `++`, `Array.extract`, `Array.insertIdx`, `Array.insertIdx!`, `Array.insertIdxIfInBounds`, `Array.eraseIdx`, `Array.eraseIdx!`, `Array.eraseIdxIfInBounds`, `Array.swap`, `Array.swapAt`, `Array.swapIfInBounds`, and `Array.reverse`.  Bang operations trap on invalid indices.  In-bounds updates allocate fresh arrays and leave aliases to old arrays unchanged.

The supported iteration and search operations are `Array.map`, `Array.foldl`, `Array.find?`, `Array.findIdx?`, `Array.any`, `Array.all`, and `Array.filter`.  Mappers, folders, and predicates must be direct lambdas that LeanExe can extract without closure allocation.  `Array.foldl` supports a one-slot accumulator such as `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, or a supported array pointer.

Nested arrays, arrays of recursive types, polymorphic array code, array capacity behavior, and effectful callbacks are unsupported.  The implementation favors Lean value semantics over in-place mutation.  Programs should assume copy-on-write behavior for every accepted update.

## Byte Arrays

`ByteArray` values use a pointer-length representation.  Entry parameters come from host memory, and returned values may point to host-provided input memory, a slice of that memory, or arena memory allocated by compiled code.  The host must read returned bytes before calling `reset()`.

Supported read operations include `ByteArray.size`, `ByteArray.isEmpty`, `ByteArray.get!`, proof-indexed indexing, bang indexing, safe indexing, and `ByteArray.extract`.  Out-of-bounds trapping reads emit WASM `unreachable`.  Safe indexing returns `Option UInt8`, and extract clamps the stop index to the source length.

Supported construction and update operations include `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, `ByteArray.push`, `ByteArray.append`, append notation through `++`, proof-indexed `ByteArray.set`, trapping `ByteArray.set!`, and value-level `ByteArray.copySlice`.  Update operations allocate new byte buffers and preserve aliases to the old input.  `ByteArray.copySlice` follows Lean's pure value behavior rather than capacity behavior.

Supported binary and loop operations include `ByteArray.toUInt64LE!`, `ByteArray.toUInt64BE!`, `ByteArray.foldl`, and `ByteArray.findIdx?`.  The fixed-width decoding operations require exactly eight bytes and trap otherwise.  `ByteArray.foldl` supports a one-slot accumulator such as `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, or a supported array pointer, and byte-array folders and predicates must be direct lambdas.

Unsupported byte-array features include `ByteArray.foldlM`, `USize` indexing APIs, `ByteArray.uset`, string conversion, UTF-8 decoding, effectful callbacks, and closure-valued callbacks.  Hosts interact with byte arrays through `alloc`, `memory`, and the pointer-length ABI.  Wasmtime's scalar `--invoke` interface is convenient for scalar examples, but byte-array entries need a host program that writes and reads module memory.

## ASCII Strings

`LeanExe.AsciiString` is a source-level structure whose runtime representation is one `ByteArray` field.  The type is intended for byte-oriented text that must remain in the ASCII range, which covers JSON punctuation, decimal digits, unescaped field names, simple error messages, and generated protocol text.  It avoids Lean `String` and `Char` semantics, so indexing remains byte indexing and the compiler does not need UTF-8 decoding.

The library provides `empty`, `ofTrustedByteArray`, `toByteArray`, `size`, `isEmpty`, `get!`, `get?`, `getD`, `isAsciiByte`, `pushTrustedByte`, `pushByte?`, `append`, `extract`, `isAscii`, `ofByteArray?`, `singletonTrusted`, and `singleton?`.  Trusted constructors do not inspect bytes and therefore rely on the caller to preserve the ASCII invariant.  Checked constructors and checked pushes return `Option AsciiString`, using `none` when input bytes are outside `0..127`.

The compiler treats `AsciiString` as an ordinary supported monomorphic structure over `ByteArray`.  An `AsciiString` entry parameter or result flattens like that structure, so the public ABI is the same pointer-length pair used by the underlying `ByteArray` field.  The recommended public boundary remains `ByteArray -> ByteArray` with explicit `AsciiString.ofByteArray?` validation inside the program, because that makes malformed host input part of the source-level behavior.

## Option, Except, and Products

`Option α` uses the same tagged-value representation as a two-constructor user inductive.  Supported operations include `Option.none`, `Option.some`, `Option.casesOn`, `Option.rec`, `Option.getD`, `Option.get!`, `Option.orElse`, `Option.elim`, `Option.map`, `Option.filter`, `Option.any`, `Option.all`, `Option.bind`, `Option.isSome`, and `Option.isNone`.  The payload type must be supported wherever the `Option` value appears.

`Except ε α` is represented as a two-constructor tagged value.  Supported operations include `Except.error`, `Except.ok`, `Except.casesOn`, `Except.rec`, `Except.map`, `Except.mapError`, `Except.bind`, `Except.toOption`, `Except.isOk`, and restricted fallback through `<|>`.  Both payload types must be supported in the value's position.

Products are supported as internal values.  `Prod.mk`, `.1`, `.2`, `Prod.casesOn`, and `Prod.rec` preserve lazy field demand in the extractor.  Product entry parameters and product entry results are rejected because the public ABI assigns source identity to structures and tagged values instead.

## Unsupported Features

Unsupported runtime features include polymorphic executable code, type classes that require runtime specialization, higher-order functions, closures, general structural recursion, mutual recursion, arbitrary Lean or Std library calls, `unsafe`, `partial`, opaque executable constants, executable axioms, quotients, `IO`, `EIO`, `BaseIO`, `Task`, file access, environment access, time, randomness, concurrency, reflection, and FFI.  Unsupported data features include `String`, `List` as a runtime value, nested arrays, arrays of recursive values, exported recursive data structures, recursive structures, indexed inductives, mutual inductives, and polymorphic structures or inductives.  Unsupported numeric features include signed integers, floating-point arithmetic, and arbitrary-precision runtime `Nat`.

Unsupported features should produce a rejection during `report` or `compile`.  They should not be emulated through hidden Lean runtime calls.  A missing rejection is a compiler bug, because accepted WASM must be explainable through this specification.

## Diagnostics and Correctness

The report command classifies the entry point and its reachable declarations.  It marks known primitives, erased proofs, supported source-defined structures and inductives, rejected executable dependencies, and external frontier items.  The first useful diagnostic for a failed compile is:

```sh
.lake/build/bin/lean-wasm report --module Module.Name --entry Module.Name.entry
```

The compiler's user-facing correctness claim is semantic agreement for accepted pure programs under the bounded numeric and memory model stated here.  Tests compare generated WASM behavior with Lean execution for the supported examples and correctness fixtures.  The generic compiler does not claim a complete mechanized proof of source-to-WASM equivalence.

Traps are part of the modeled behavior for operations that Lean would panic on in ordinary execution, such as bang indexing out of bounds.  The compiler must preserve observable evaluation order for accepted pure code, including lazy field projection and short-circuiting boolean operations.  Host behavior outside the ABI, including reading stale pointers after `reset` or passing malformed flattened values, is outside the Lean source semantics.
