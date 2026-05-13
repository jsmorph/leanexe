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
| `PSum α β` | No | No | Yes | Internal sum values are accepted for Lean's generated mutual-recursion helpers. |
| Structure | Yes | Yes | Yes | Nonrecursive structures with concrete supported runtime type arguments and supported runtime fields.  Internal-only structures may contain recursive-inductive pointer fields. |
| User inductive | Yes | Yes | Yes | Nonrecursive inductives with concrete supported runtime type arguments and supported runtime fields.  Internal-only tagged values may contain recursive-inductive pointer payloads. |
| Recursive inductive | No | No | Yes | Monomorphic self-recursive inductives, mutual recursive inductive families, and monomorphic recursive instances are allowed inside accepted code. |
| `List α` | No | No | Yes | Internal monomorphic instances such as `List UInt64`; public list ABI is unsupported.  Source-defined structural helpers may traverse and return lists.  Limited direct-lambda library calls are accepted for monomorphic helpers. |
| `Option α` | Yes | Yes | Yes | Treated as a supported tagged value when `α` is supported. |
| `Except ε α` | Yes | Yes | Yes | Treated as a supported tagged value when both payload types are supported. |
| Propositions | Erased | Erased | Erased | Proofs may justify Lean source but have no WASM value. |
| `String` | No | No | Compile-time ASCII only | Runtime strings are unsupported; restricted compile-time ASCII expressions may feed `String.toUTF8`, `String.length`, `String.isEmpty`, and equality. |

Entry parameters support `Bool`, `UInt64`, bounded `Nat`, `ByteArray`, fixed-width `Array`, supported structures, supported nonrecursive inductives, `Option`, and `Except`.  Entry results support the same set.  Public structures, public tagged values, public `Option`, public `Except`, and public arrays must not contain recursive-inductive values anywhere in their flattened layout.  `UInt8`, `UInt32`, `Unit`, products, `PSum`, and recursive inductives are internal-only types even though helpers may use them.

An array element type is fixed-width when LeanExe can assign a constant number of `i64` slots to each element.  The accepted public element types are `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, supported structures, supported nonrecursive inductives, `Option`, and `Except`, provided their layouts do not contain recursive values.  Internal arrays may also store recursive inductive values as one-slot heap pointers, and they may store fixed-width structures or tagged values that contain those pointers.  Nested arrays remain unsupported.

## Numeric Semantics

`UInt64` arithmetic uses the unsigned 64-bit Lean semantics.  Addition, subtraction, and multiplication wrap modulo `2^64`.  Division by zero returns `0`, and remainder by zero returns the dividend, matching Lean's fixed-width integer behavior.

`UInt8` and `UInt32` are represented internally as constrained `i64` values.  Literals and `ofNat` conversions reduce modulo `2^8` or `2^32`, arithmetic wraps to the same width, and conversions to wider supported types preserve the constrained value.  Shifts mask the shift amount modulo the type width before shifting.

Runtime `Nat` uses an unsigned 64-bit bound rather than arbitrary precision.  A runtime `Nat` literal must be less than `2^64` unless it is consumed directly by a fixed-width conversion that defines its own modulo behavior.  `Nat` subtraction is saturating, `Nat.pred` uses that saturation, and `Nat.succ` uses checked addition.

`Nat` addition and multiplication trap when the result would exceed the bounded representation.  `Nat` division by zero returns `0`, and `Nat` remainder by zero returns the dividend.  `Nat.beq`, `Nat.blt`, `Nat.ble`, `Nat.min`, and `Nat.max` use unsigned comparisons over the bounded representation.

Supported comparisons and equality include scalar equality for `Bool`, `UInt8`, `UInt32`, `UInt64`, and `Nat`; unsigned comparisons for supported numeric scalars; and boolean operations `&&`, `||`, `!`, and `Bool.xor`.  Short-circuiting boolean operations preserve Lean evaluation order.  Unsupported numeric types, arbitrary-precision runtime arithmetic, signed integer operations, and floating-point operations are outside the language.

## Terms and Control Flow

The accepted term language is first-order.  It includes variables, local `let`, direct calls to accepted helpers, numeric literals, constructors, projections, `if`, dependent `if` with erased proof binders, pattern matching, pure `Id` `do` notation, pure `for` loops over `ByteArray`, fixed-width `Array`, and `Std.Legacy.Range`, and a restricted fuel-recursive loop shape.  It excludes higher-order arguments, closures, polymorphic runtime values, type-class-driven runtime dispatch, opaque executable constants, and arbitrary recursors.

Local `let` bindings preserve Lean evaluation behavior for lazy internal values.  A demanded field, branch, or projection extracts only the value needed by the result.  This matters for products, options, structures, and branch-selected values whose unused components may contain trapping expressions.

Named helper calls are allowed when the helper has a supported internal type and lives under the same root namespace as the entry module.  Nonrecursive helpers are extracted directly or inlined as needed, and recursive helpers can be called directly when they match the accepted fuel-recursive shape.  The extractor emits real WASM calls when demand analysis proves that strict argument evaluation preserves Lean behavior.  Structured helper returns use flattened result slots, and conditional structured results are materialized into locals through statement-level branches so one source call does not become one call per returned slot.  Strict helper-call arguments and eager fixed-width array element payloads materialize top-level let and call values in source order before flattening, so a structured helper used in those positions is evaluated once.  The identity function, `Id.run`, `Pure.pure`, `Bind.bind`, `Applicative.toPure`, `Monad.toApplicative`, and `Monad.toBind` are erased for pure `Id` code.

Transparent specialization unfolds nonlocal transparent applications only when the application contains a direct lambda argument and the callee is not one of the explicitly lowered primitive, matcher, or recursor families.  This admits selected first-order uses of Lean library functions without closure allocation.  Function values still cannot escape, appear in public types, or survive as runtime values.

Local first-order polymorphic helpers can be inline-specialized at concrete call sites when all static type or proof arguments precede the runtime arguments, every runtime parameter has a supported concrete type after substitution, and the concrete result type is supported.  The specialized body uses the same lazy argument bindings as monomorphic inline helpers, so an unused runtime argument is not evaluated.  This covers helpers such as `Box α -> α`, `PairBox α β -> α`, and `ParamResult ε α -> Bool` at concrete supported instantiations.

Pure `Id.run` `for` loops compile when Lean elaborates them to `ForIn.forIn` over `ByteArray`, a fixed-width `Array`, or `Std.Legacy.Range`, and each loop step returns a supported `ForInStep.yield` or `ForInStep.done` value.  Range loops use bounded `Nat` start, stop, and step fields and follow Lean's exclusive-stop iteration order.  The accumulator may be a scalar, an `Array` pointer value with supported fixed-width elements, a product, a structure, a nonrecursive tagged value, or a recursive-inductive pointer value, provided its flattened representation contains no `ByteArray` field.  The accepted loop body may use `let mut` assignments that elaborate to local lets, `continue` branches that yield the current accumulator, and `break` branches that return `ForInStep.done`.  Conditional `break` or `continue` may appear before later assignments in the same loop body.  `ByteArray` accumulator values, maps, polymorphic iterators, and monadic effects are unsupported.

Helper calls may return supported structured values, including structures, byte arrays, arrays, `Option`, `Except`, and user-defined tagged values.  The call result uses the same flattened ABI slots as an entry result, then the extractor reconstructs the source-level value shape for projections and matches.  This rule matters for parser-style code, where a bounded recursive helper often returns a tagged parse result that later code matches before producing a public `ByteArray`.

Pattern matching is supported for `Bool`, nonrecursive `Nat` zero/successor matches, products, structures, nonrecursive user inductives, recursive user inductives in internal positions, `Option`, and `Except`.  Branch results must have a common supported value shape.  Proposition-valued motives and dependent runtime result shapes are unsupported.

The accepted fuel-recursive function shape uses a first `Nat` fuel parameter that decreases on each recursive call.  The function may carry scalar values, byte arrays, arrays, structures, nonrecursive tagged values, and internal recursive inductive pointers through the loop.  This admits state-passing parser loops whose cursor, accumulator, and flags live in a supported structure.  The recursive branch may start with local `let` bindings before the tail call or before an immediate `if` whose supported branch returns the tail call.  Those bindings use the same lazy demand behavior as ordinary local lets, so an unused step binding does not evaluate.  The base or early-exit value must have a supported result type.

Direct structural recursion is accepted for helper functions whose first parameter has a supported self-recursive inductive type or a monomorphic instance of one.  Constructor arms may use Lean's generated below value for direct recursive fields, including branching constructors with multiple direct recursive fields.  The extractor resolves generated projection paths such as the left and right recursive results of a binary node to separate WASM self-calls.  This covers source-defined list-shaped traversals, list-building helpers such as append and reverse, binary-tree traversals, expression evaluators, and ordinary `List UInt64` traversals such as summing a recursive list.  Expression-position structural recursion is lowered by synthesizing a private helper over the recursive scrutinee and any supported first-order post-arguments, then using the same structural-recursion extractor.  This covers direct `List.length`, list append notation through `++`, `List.reverse`, `List.map`, `List.filter`, and `List.foldr` expressions when callbacks specialize to closed first-order code.  The extractor can defunctionalize generated function-valued results when function arguments are direct lambdas and runtime carried arguments are explicit first-order helper parameters.  It also accepts a top-level closed structural fold over a list-shaped recursive inductive when Lean's generated step tail-calls the single recursive field with one hidden first-order accumulator.  This covers direct `xs.foldl f init` bodies such as `leanList123.foldl (fun acc x => acc * 10 + x) 0`.  Closed structural predicates over a list-shaped recursive inductive are accepted when Lean's generated step combines a direct predicate result with the single recursive-field result through `Bool.or` or `Bool.and`, and terminal arms return the corresponding identity value.  This covers direct `xs.any p` and `xs.all p` bodies when `p` is a direct lambda.  A narrow well-founded-recursion shape is also accepted when Lean lowers recursive descent through an `Array` field to `WellFounded.fix`: the constructor arm must fold over the generated `Array.attach` value, the recursive call must use the generated well-founded handle, and the result must have a supported first-order shape.  Mutual structural recursion is accepted when Lean lowers ordinary mutual helper definitions to `WellFounded.Nat.fix` over a nested `PSum` tree, each leaf immediately matches one supported recursive-family member, recursive calls use the generated well-founded handle, and recursive descent goes through direct fields or fixed-width array folds over attached array elements.  Arbitrary well-founded recursion, mutual helper groups outside that nested `PSum` structural shape, course-of-values uses beyond direct recursive result projections, public recursive parameters, and public recursive results remain unsupported.

## Structures and Inductives

A supported structure has no indices, one constructor, no recursive structure definition, and runtime fields whose types are supported after concrete type arguments are substituted.  Constructors, field projections, structure-update elaborations, single-constructor matches, entry parameters, local values, helper parameters, helper results, arrays of structures, and exported structure results are accepted.  Proof fields are removed from the runtime layout.  Internal structures may contain recursive-inductive fields, which flatten as one-slot heap pointers when stored in fixed-width arrays or passed between helper functions.  Such structures remain internal-only when their flattened layout contains a recursive pointer.

A supported nonrecursive user inductive has no indices, at least one constructor, and runtime constructor fields whose types are supported after concrete type arguments are substituted.  Constructors, generated matcher extraction, nullary enum matches, branch-selected values, entry parameters, local values, helper values, arrays of tagged values, and exported results are accepted.  The ABI tag is the constructor index in Lean constructor order.  Internal tagged values may contain recursive-inductive payloads, including inside arrays and `Option` results produced by array search operations.  Such tagged values remain internal-only when their flattened layout contains a recursive pointer.

A supported recursive inductive family is non-indexed after all runtime type parameters have been specialized to supported types.  The family may contain one inductive or several mutual inductives.  Constructor fields may contain any member of the same specialized family, `Array` values whose elements have supported fixed-width internal layouts, or other supported nonrecursive field types.  Recursive values may be constructed, matched, stored in locals, passed to helpers, returned from helpers, selected by branches, stored in internal arrays, and carried through accepted fuel-recursive loops.  The current specialization path covers ordinary `List UInt64` construction, matching, helper calls, direct structural recursion over one or more direct recursive fields per constructor, source-defined `List` helpers for length, append, reverse, and fold-right-style traversals, recursive `Array.foldl` descent through generated `Array.attach` values, monomorphic helper calls to `List.map`, `List.filter`, `List.find?`, `List.foldl`, and `List.any`, and direct expression-position `List.length`, list append notation through `++`, `List.reverse`, `List.map`, `List.filter`, and `List.foldr` when callbacks are direct lambdas and the specialized result is a first-order value.  It also covers internal mutual-family values whose constructors refer to another member of the family directly or through a fixed-width `Array`, fixed-width structures and tagged wrappers over those family members, and ordinary mutual structural traversals over recursive-family members when Lean generates the accepted nested `PSum` well-founded shape.  `List.foldl` is accepted when its carried accumulator is an explicit helper parameter after the list parameter, and direct top-level `List.foldl` is accepted when it lowers to the closed structural-fold shape with one hidden first-order accumulator.  Direct `List.any` and `List.all` expressions are accepted when they lower to the closed structural-predicate shape with one direct-lambda predicate.  The compiler does not compile `List.concat`, nested closed structural folds, closed structural predicates whose step does not match the accepted `Bool.or` or `Bool.and` shape, mutual structural recursion outside the accepted nested `PSum` shape, mutual recursive helper functions that do not structurally descend through recursive-family values, or expression-position structural recursion whose post-arguments have unsupported runtime types.

Recursive inductive values do not have a public entry ABI yet.  They cannot appear as entry parameters, entry results, public array elements, structure fields exposed through entry values, or nonrecursive inductive payloads exposed through entry values.  They may appear inside internal structure fields, internal nonrecursive tagged payloads, and internal arrays of those fixed-width values.  Indexed inductives, unspecialized polymorphic inductives, unspecialized polymorphic structures, polymorphic functions that require runtime specialization, mutual families whose members cannot share one runtime-parameter specialization, recursive structures, inherited-field structure flattening, course-of-values recursion through generated below tails, and unsupported runtime fields are rejected.

## Arrays

`Array α` values use a copy-on-write arena layout.  The first `i64` cell stores the length, and element cells follow immediately.  A one-slot element at index `i` lives at byte offset `8 * (i + 1)`, while a width-`w` element uses slots `8 * (1 + i * w + s)` for slot `s`.

Accepted scalar element types are `Bool`, `UInt8`, `UInt32`, `UInt64`, and bounded `Nat`.  Supported structures flatten by field order, supported tagged values store the tag followed by payload slots for every constructor, and recursive inductive values store one heap pointer slot in internal arrays.  Internal fixed-width arrays may store structures and tagged values that contain recursive heap-pointer fields.  Fixed-width array operations preserve old arrays by allocating a new array for updates.

Array literals compile when Lean elaborates them as `List.toArray` over a literal list whose item type has a fixed-width layout.  The supported constructors are `Array.empty`, `Array.mkEmpty`, `Array.emptyWithCapacity`, `Array.singleton`, and `Array.replicate`.  Capacity arguments are not observable in the accepted language.

The supported read operations are `Array.size`, `Array.isEmpty`, proof-indexed `a[i]`, `a[i]!`, `a[i]?`, `Array.getD`, `Array.back`, `Array.back!`, and `Array.back?`.  Trapping reads emit WASM `unreachable` on out-of-bounds access.  Safe reads return `Option` values without reading an element payload when the index is out of bounds.

The supported update and sequence operations are `Array.set`, `Array.set!`, `Array.setIfInBounds`, `Array.modify`, `Array.push`, `Array.pop`, `Array.append`, append notation through `++`, `Array.extract`, `Array.insertIdx`, `Array.insertIdx!`, `Array.insertIdxIfInBounds`, `Array.eraseIdx`, `Array.eraseIdx!`, `Array.eraseIdxIfInBounds`, `Array.swap`, `Array.swapAt`, `Array.swapIfInBounds`, and `Array.reverse`.  Bang operations trap on invalid indices.  In-bounds updates allocate fresh arrays and leave aliases to old arrays unchanged.

The supported iteration and search operations are `Array.map`, `Array.foldl`, `Array.find?`, `Array.findIdx?`, `Array.any`, `Array.all`, and `Array.filter`.  Mappers, folders, and predicates must be direct lambdas that LeanExe can extract without closure allocation.  `Array.foldl` supports a one-slot accumulator such as `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, or a supported array pointer.

Nested arrays, public arrays of recursive values, polymorphic array code, array capacity behavior, and effectful callbacks are unsupported.  The implementation favors Lean value semantics over in-place mutation.  Programs should assume copy-on-write behavior for every accepted update.

Maps are not a primitive runtime type.  Programs may define simple table structures over supported arrays, as in an open-addressed `UInt64` map backed by `Array Slot`, when the operations stay inside the accepted first-order subset.

## Byte Arrays

`ByteArray` values use a pointer-length representation.  Entry parameters come from host memory, and returned values may point to host-provided input memory, a slice of that memory, or arena memory allocated by compiled code.  The host must read returned bytes before calling `reset()`.

Supported read operations include `ByteArray.size`, `ByteArray.isEmpty`, `ByteArray.get!`, proof-indexed indexing, bang indexing, safe indexing, and `ByteArray.extract`.  Out-of-bounds trapping reads emit WASM `unreachable`.  Safe indexing returns `Option UInt8`, and extract clamps the stop index to the source length.

Supported construction and update operations include `ByteArray.empty`, `ByteArray.mk` from `Array UInt8`, `String.toUTF8` on compile-time ASCII string expressions, `ByteArray.push`, `ByteArray.append`, append notation through `++`, proof-indexed `ByteArray.set`, trapping `ByteArray.set!`, and value-level `ByteArray.copySlice`.  Update operations allocate new byte buffers and preserve aliases to the old input.  `ByteArray.copySlice` follows Lean's pure value behavior rather than capacity behavior.

Supported binary and loop operations include `ByteArray.toUInt64LE!`, `ByteArray.toUInt64BE!`, `ByteArray.foldl`, and `ByteArray.findIdx?`.  The fixed-width decoding operations require exactly eight bytes and trap otherwise.  `ByteArray.foldl` supports a one-slot accumulator such as `Bool`, `UInt8`, `UInt32`, `UInt64`, bounded `Nat`, or a supported array pointer, and byte-array folders and predicates must be direct lambdas.

Unsupported byte-array features include `ByteArray.foldlM`, `USize` indexing APIs, `ByteArray.uset`, runtime string conversion, UTF-8 decoding, effectful callbacks, and closure-valued callbacks.  Hosts interact with byte arrays through `alloc`, `memory`, and the pointer-length ABI.  Wasmtime's scalar `--invoke` interface is convenient for scalar examples, but byte-array entries need a host program that writes and reads module memory.

## ASCII Strings

`LeanExe.AsciiString` is a source-level structure whose runtime representation is one `ByteArray` field.  The type is intended for byte-oriented text that must remain in the ASCII range, which covers JSON punctuation, decimal digits, unescaped field names, simple error messages, and generated protocol text.  It avoids runtime Lean `String` and `Char` semantics, so indexing remains byte indexing and the compiler does not need UTF-8 decoding.

ASCII text may be written with standard Lean `String` syntax when the expression is consumed at compile time.  The accepted forms are ASCII literals, local `String` lets, top-level `String` constants, `String.append`, and string append notation through `++`.  The compiler lowers those expressions through `String.toUTF8`, `String.length`, `String.isEmpty`, `==`, and `!=`, rejecting any expression whose UTF-8 bytes are not all below `128`.

Runtime `String` values remain outside the accepted language.  `String` parameters, `String` results, string values returned from helpers, runtime branch-selected strings, indexing, `Char`, UTF-8 decoding, and Unicode semantics are unsupported.  Programs that need text at the public boundary should accept `ByteArray`, validate it with `AsciiString.ofByteArray?`, and use `AsciiString` for byte-indexed ASCII processing.

The library provides `empty`, `ofTrustedByteArray`, `toByteArray`, `size`, `isEmpty`, `get!`, `get?`, `getD`, `isAsciiByte`, `pushTrustedByte`, `pushByte?`, `append`, `extract`, `equals`, `startsWith`, `containsByte`, `isAscii`, `ofByteArray?`, `singletonTrusted`, and `singleton?`.  Trusted constructors do not inspect bytes and therefore rely on the caller to preserve the ASCII invariant.  Checked constructors and checked pushes return `Option AsciiString`, using `none` when input bytes are outside `0..127`.

The compiler treats `AsciiString` as an ordinary supported monomorphic structure over `ByteArray`.  An `AsciiString` entry parameter or result flattens like that structure, so the public ABI is the same pointer-length pair used by the underlying `ByteArray` field.  The recommended public boundary remains `ByteArray -> ByteArray` with explicit `AsciiString.ofByteArray?` validation inside the program, because that makes malformed host input part of the source-level behavior.

## Limited JSON

The JSON support consists of ASCII-only parser and generator helpers written in the accepted Lean subset.  `LeanExe.Ascii.Basic` provides byte constants, whitespace skipping, and byte expectations.  `LeanExe.Ascii.Decimal` provides checked `UInt64` decimal parsing and decimal rendering, and `LeanExe.Ascii.Json` provides object-field utilities, restricted string parsing, balanced value skipping, and small object generators.

`LeanExe.Ascii.Json.findFieldRange` scans a top-level object for a named field and returns the byte range of the field value.  `getUInt64Field`, `getStringField`, `getBoolField`, `getNullField`, `getObjectField`, `getArrayField`, and `getRawField` build on that range helper.  The scanner accepts unescaped ASCII strings whose bytes are at least `32` and below `128`, excluding `"` and `\`, and it rejects non-ASCII input before parsing when programs call `AsciiString.ofByteArray?`.

Composite value skipping tracks nesting depth for `{...}` and `[...]` so a getter can pass over unknown nested values.  This skipper validates balanced nesting and restricted strings, but it does not implement the full JSON grammar inside skipped object or array values.  It also does not enforce that a closing `}` matches an opening `{` rather than `[`, so code that needs complete JSON validation still needs a real AST parser.

The generator helpers include `appendQuotedBytes?`, `appendQuotedString?`, `appendFieldPrefix?`, `appendUInt64Field?`, `appendBoolField?`, `appendNullField?`, `appendStringField?`, `appendRawField?`, `object1UInt64`, `object1Bool`, `object1String`, and the shared `errorJson`.  Quoted string generation uses the same restricted unescaped ASCII string rules as parsing.  `appendRawField?` accepts an `AsciiString` only when `skipValueAt` consumes the whole value after whitespace.

`LeanExe.Examples.JsonDouble.transform : ByteArray -> ByteArray` validates ASCII input, parses an object with one field named `n`, reads a decimal `UInt64`, doubles it when the doubled value fits in `UInt64`, and returns JSON bytes.  Success returns `{"result":<number>}`, while malformed input, non-ASCII input, parse overflow, and doubled-value overflow return `{"error":1}`.  The accepted input shape is `{ "n" : digits }` with optional ASCII whitespace around punctuation and at the end; decimal digits must be nonempty, unsigned, and within the `UInt64` range.

`LeanExe.Examples.JsonAdd.transform : ByteArray -> ByteArray` uses the same helpers for a two-field object.  It accepts `{ "a" : digits , "b" : digits }` in that fixed field order, allows the same ASCII whitespace positions, rejects decimal parse overflow, rejects `UInt64` addition overflow, and returns `{"sum":<number>}` on success.  It returns `{"error":1}` for malformed input, non-ASCII input, wrong field order, trailing input, and overflow.

`LeanExe.Examples.JsonCollatzLength.transform : ByteArray -> ByteArray` accepts an object with a field named `collatzLengthFor`, reads it through `Ascii.Json.getUInt64Field`, and returns `{"length":<number>}` through `Ascii.Json.object1UInt64`.  The length counts sequence terms, so input `41` returns `110`.  The program rejects zero, decimal parse overflow, `3n+1` overflow during sequence evaluation, fuel exhaustion before reaching `1`, malformed input, non-ASCII input, and trailing input.

`LeanExe.Examples.JsonTools.transform : ByteArray -> ByteArray` demonstrates generated JSON output through `object1UInt64` and reads its input through `Ascii.Json.getUInt64Field`, including skipped unknown values before the requested field.  `LeanExe.Examples.JsonTools.lookup : ByteArray -> UInt64` demonstrates the same generic object-field lookup as a scalar entry.

This library does not implement a general JSON value type, full object validation, array item parsing, string escape decoding, Unicode, signed numbers, fractional numbers, exponent notation, duplicate-field policy, or rich parse errors.  Programs that need small protocol-shaped JSON can accept `ByteArray`, convert through `AsciiString.ofByteArray?`, parse exact fields or use the limited field getters, and generate output with the provided object helpers.  A general JSON library needs an AST representation, object and array parsers, string escape handling, a bounded text representation beyond ASCII, and error reporting richer than the current one-byte error code.

## Option, Except, and Products

`Option α` uses the same tagged-value representation as a two-constructor user inductive.  Supported operations include `Option.none`, `Option.some`, `Option.casesOn`, `Option.rec`, `Option.getD`, `Option.get!`, `Option.orElse`, `Option.elim`, `Option.map`, `Option.filter`, `Option.any`, `Option.all`, `Option.bind`, `Option.isSome`, and `Option.isNone`.  The payload type must be supported wherever the `Option` value appears.

`Except ε α` is represented as a two-constructor tagged value.  Supported operations include `Except.error`, `Except.ok`, `Except.casesOn`, `Except.rec`, `Except.map`, `Except.mapError`, `Except.bind`, `Except.toOption`, `Except.isOk`, and restricted fallback through `<|>`.  Both payload types must be supported in the value's position.

Products are supported as internal values.  `Prod.mk`, `.1`, `.2`, `Prod.casesOn`, and `Prod.rec` preserve lazy field demand in the extractor.  Product entry parameters and product entry results are rejected because the public ABI assigns source identity to structures and tagged values instead.  `PSum` is supported as an internal sum value for the generated helper behind accepted mutual structural recursion; it has no public ABI.

## Unsupported Features

Unsupported runtime features include polymorphic executable code beyond inline-specialized first-order helpers, type classes that require runtime specialization, higher-order functions, closures, structural recursion beyond the supported direct recursive result projections, closed fold, closed predicate, generated array-descent, and nested `PSum` mutual-recursion forms described above, arbitrary Lean or Std library calls, function-valued structural-recursion motives that cannot be defunctionalized into direct lambdas and accepted first-order carried parameters, `unsafe`, `partial`, opaque executable constants, executable axioms, quotients, `IO`, `EIO`, `BaseIO`, `Task`, file access, environment access, time, randomness, concurrency, reflection, and FFI.  Unsupported data features include runtime `String`, runtime `Char`, nested arrays, public arrays of recursive values, exported recursive data structures, recursive structures, indexed inductives, unspecialized polymorphic structures or inductives, and polymorphic values at runtime.  Concrete instantiations of supported parametric structures and inductives are accepted, and simple first-order polymorphic helper calls may inline-specialize, but LeanExe does not compile one shared generic runtime function body for all type arguments.  Unsupported numeric features include signed integers, floating-point arithmetic, and arbitrary-precision runtime `Nat`.

Unsupported features should produce a rejection during `report` or `compile`.  They should not be emulated through hidden Lean runtime calls.  A missing rejection is a compiler bug, because accepted WASM must be explainable through this specification.

## Diagnostics and Correctness

The report command classifies the entry point and its reachable declarations.  It marks known primitives, erased proofs, supported source-defined structures and inductives, rejected executable dependencies, and external frontier items.  The first useful diagnostic for a failed compile is:

```sh
.lake/build/bin/lean-wasm report --module Module.Name --entry Module.Name.entry
```

The compiler's user-facing correctness claim is semantic agreement for accepted pure programs under the bounded numeric and memory model stated here.  Tests compare generated WASM behavior with Lean execution for the supported examples and correctness fixtures.  The generic compiler does not claim a complete mechanized proof of source-to-WASM equivalence.

Traps are part of the modeled behavior for operations that Lean would panic on in ordinary execution, such as bang indexing out of bounds.  The compiler must preserve observable evaluation order for accepted pure code, including lazy field projection and short-circuiting boolean operations.  Host behavior outside the ABI, including reading stale pointers after `reset` or passing malformed flattened values, is outside the Lean source semantics.
