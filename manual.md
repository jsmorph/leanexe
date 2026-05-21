# LeanExe User Manual

## Purpose

This manual explains how to write Lean source code that LeanExe can compile to WASM.  The [Language Specification](spec.md) defines the accepted language, ABI, and semantics.  This manual gives authoring rules, source templates, and debugging practices for users and LLMs that need to produce accepted source code.

The main rule is simple: write concrete, first-order Lean.  Let Lean type-check the program, then let LeanExe reject anything outside its executable subset.  When a concise Lean expression compiles to a generated helper shape that LeanExe does not support, rewrite the source into one of the stable shapes shown here.

## Quick Workflow

1. Write a Lean module under the package, usually under `LeanExe/Examples` or another namespace rooted in the module being compiled.
2. Build the module with Lake.
3. Run `report` on the intended entry if the source uses arrays, recursion, JSON, structures, inductives, or byte arrays.
4. Compile with the command mode that matches the entry type.
5. Run the generated WASM with Wasmtime or instantiate it from a host program.
6. If compilation fails, simplify the source shape before adding compiler features.

```sh
lake build LeanExe.Examples.MyProgram

.lake/build/bin/lean-wasm report \
  --module LeanExe.Examples.MyProgram \
  --entry LeanExe.Examples.MyProgram.entry

.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.MyProgram \
  --entry LeanExe.Examples.MyProgram.entry \
  --out build/my-program.wasm
```

The report command is the first diagnostic tool.  It imports the module, expands reachable declarations under the module root namespace, classifies dependencies, and reports the first useful rejection.  A source program that Lean accepts but LeanExe rejects lies outside this compiler's current language.

## Core Authoring Rules

Use these rules before reaching for more specific templates:

- Use concrete runtime types: `UInt64`, `Nat`, `Bool`, `ByteArray`, `Array`, structures, nonrecursive inductives, `Option`, `Except`, and internal recursive inductives.
- Keep public entry types ABI-friendly.  Recursive data, `List`, products, `PSum`, nested arrays, and arrays of recursive values are internal-only.
- Keep helper definitions under the same root namespace as the module being compiled.
- Use named helper declarations freely when their types are concrete and first-order.
- Use `for` and `while` loops in `Id`, `Option`, or `Except` when the collection and accumulator types are supported.
- Use direct lambdas in `Array.foldl`, `Array.foldlM`, `Array.map`, `Array.filter`, `Array.find?`, `ByteArray.foldl`, `ByteArray.foldlM`, and similar accepted callbacks.
- Use `UInt64` for most arithmetic at public boundaries.  Use `Nat` for fuel and indexes when the value stays within the bounded runtime representation.
- Use `ByteArray` at command boundaries.  Validate text with `AsciiString.ofByteArray?` inside the program when the input must be ASCII.
- Use `Except ByteArray ByteArray` for command-style programs that need explicit user-visible errors.
- Use explicit constructor arms for recursive ASTs.  Sparse `if let` and catch-all matches are accepted for `Option` and nonrecursive user inductives.
- Use `report` after changing source shape.  Do not assume that a Lean library function compiles because Lean can evaluate it.

Avoid these forms in source intended for LeanExe:

- Runtime `String`, runtime `Char`, `IO`, `EIO`, `BaseIO`, `Task`, file access, randomness, time, concurrency, reflection, and FFI.
- `unsafe`, `partial`, opaque executable constants, executable axioms, quotients, and arbitrary Lean runtime calls.
- Escaping lambdas, function-valued fields, closure-valued helpers, and higher-order values that survive as runtime data.
- Runtime-polymorphic public entries and shared generic runtime helper bodies.
- Public recursive data structures, public `List`, public nested arrays, public arrays of `ByteArray`, and public arrays of recursive values.
- Wildcard-heavy matches over recursive or large inductives when explicit arms make the accepted shape clearer.
- Generic recursive JSON object decoders that hide the child-size proof from LeanExe's accepted well-founded-recursion shape.

## Entry Shapes

Choose the compile command from the entry type.  The Lean source stays pure in every mode.  WASI adapters add command behavior around the pure entry.

| Entry type | Command | Runtime behavior |
|------------|---------|------------------|
| Scalar or ABI value function | `compile` | Exports a callable WASM function, `memory`, `alloc`, and `reset`. |
| Any accepted entry | `compile-wat` | Emits WAT for inspection instead of binary WASM. |
| `ByteArray` | `compile-wasi` | Calls the entry and writes returned bytes to stdout. |
| `ByteArray -> ByteArray` | `compile-wasi-stdin` | Reads bounded stdin and writes returned bytes to stdout. |
| `ByteArray -> Except ByteArray ByteArray` | `compile-wasi-stdin-except` | Writes `ok` bytes to stdout, writes `error` bytes to stderr, and exits nonzero. |
| `Array ByteArray -> Except ByteArray ByteArray` | `compile-wasi-argv-except` | Passes user argv as an internal array of byte arrays. |
| `ByteArray -> Array ByteArray -> Except ByteArray ByteArray` | `compile-wasi-stdin-argv-except` | Passes bounded stdin and bounded user argv. |

Library-mode array and byte-array values use exported memory.  Hosts allocate input bytes with `alloc`, write data into `memory`, pass pointer-length pairs, and read returned pointer-length pairs before releasing owned root pointers or calling `reset`.  Command-mode programs hide that host ABI behind WASI.

## Memory Management

LeanExe modules use a small reference-counted heap inside growable WASM linear memory.  Heap-backed values allocate with a header before the payload pointer, and released objects return to a free list for later allocation.  This includes byte arrays, arrays, recursive inductive values, nested internal arrays, JSON AST nodes, and other heap-backed values created by compiled code.

In library mode, the host controls result lifetime.  It may call `alloc` to reserve input memory, call the exported Lean entry, and read returned pointer-length values or memory-backed arrays.  It may call `release(ptr)` or `free(ptr)` for a returned pointer known to be an owned allocation root.  A public `ByteArray` result exposes only pointer and length, so a slice can point inside an owned allocation or into borrowed input; the host should copy or consume those bytes before `reset()` unless the program's result protocol guarantees that the pointer is a root.  `retain(ptr)` increments the reference count and returns the same pointer, which lets a host keep a result while passing it through code that may release its own reference.

`reset()` remains a coarse reclamation operation.  It rewinds the heap and clears the free list, invalidating every old pointer regardless of reference count.  A host should use either explicit `release` calls for individual returned objects or `reset()` at a boundary where no old pointer remains live.

The compiler emits `release` for a conservative class of local heap temporaries: the temporary must come from a visible fresh allocation in a local expression or local binding, and the function result type must contain no heap pointer.  This lets scalar-result helpers reclaim internal arrays, byte arrays, and recursive values before returning.  It also computes helper-result ownership summaries from the extracted IR, then releases array, byte-array, and recursive-inductive owner slots in scalar-result callers when the callee result is proven fresh, including helpers that receive heap-bearing parameters.  Heap-result functions have a narrower cleanup rule: a fresh nonrecursive owner slot, currently `ByteArray` or `Array`, may be released after result materialization when it is absent from the returned heap roots and from borrowed root expressions used by the returned value.  Recursive heap-result temporaries remain conservative unless released by an explicit source-level ownership boundary or by another supported rule.  Recursive heap allocation retains borrowed child pointers and transfers child pointers proven fresh by the same ownership summaries.  `Array.foldl`, `Array.foldlM`, `ByteArray.foldl`, `ByteArray.foldlM`, and accepted loops release replaced accumulator owner slots after the first iteration when the next accumulator slot is proven fresh and the body has not already released the old slot; this covers byte-array accumulators, array accumulators, recursive-inductive accumulators, and owner slots inside supported accumulator structures or tagged values.  The compiler skips the initial accumulator value for this rule because ordinary Lean aliases can still refer to that value after the loop.  The compiler keeps heap-pointer helper results that may borrow from heap arguments conservative.

Compiled Lean code may read runtime counters through `LeanExe.Runtime.allocCount`, `retainCount`, `releaseCount`, and `freeCount`.  It may call `LeanExe.Runtime.release value` for a monomorphic recursive-inductive root or an array value at an explicit ownership boundary; the compiled call releases the nonzero owner root and returns the current free count.  The extractor preserves `let _ := LeanExe.Runtime.release value`, so a program can mark the boundary without adding the returned counter to its own result.  The program must not use the released value, or any heap node shared with a live value, after the call, and the compiler does not yet prove that condition.  Array and recursive-value release follows recursive-inductive child pointers, `ByteArray` owner slots, and nested `Array` owner slots stored in fixed-width layouts.  Releasing a borrowed public array with owner `0` is a no-op.

In WASI command mode, the generated module is a single-run command.  The adapter reads stdin or argv, calls the pure Lean entry, writes stdout or stderr, and exits.  Process exit discards all allocations, but one large request can still allocate enough intermediate data to hit a host memory limit before exit.  In those cases, source-level `LeanExe.Runtime.release` can mark an owned recursive root dead inside the command.

## Scalar Template

Scalar entries are the easiest way to test core logic.  Public scalar arguments and results become WASM `i64` values.  `Bool` uses `0` and `1`, `UInt8` and `UInt32` reduce at the ABI boundary, and `UInt64` uses the full unsigned 64-bit representation.

```lean
namespace LeanExe.Examples.ManualScalar

def choose (flag x y : UInt64) : UInt64 :=
  if flag == 0 then
    x
  else
    y

end LeanExe.Examples.ManualScalar
```

Compile and run:

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.ManualScalar \
  --entry LeanExe.Examples.ManualScalar.choose \
  --out build/choose.wasm

wasmtime run --invoke choose build/choose.wasm 0 41 99
```

Use `UInt64` unless the source logic specifically needs bounded `Nat` operations.  `UInt64` arithmetic wraps like Lean's fixed-width integer operations.  Runtime `Nat` is bounded to the compiler's `i64` representation, and overflowing `Nat` addition or multiplication traps.

## Structures and Inductives

Use structures for named fixed-width records.  Public structures flatten by runtime field order after proof-field erasure.  Internal structures may contain recursive-inductive pointer fields, byte arrays, arrays, or other supported values when their use stays inside accepted code.

```lean
namespace LeanExe.Examples.ManualData

structure Point where
  x : UInt64
  y : UInt64

def moveRight (p : Point) : Point :=
  { p with x := p.x + 1 }

def score (p : Point) : UInt64 :=
  p.x * 10 + p.y

end LeanExe.Examples.ManualData
```

Use nonrecursive inductives for small tagged values.  Public nonrecursive inductives flatten to a constructor tag plus payload slots for all constructors in declaration order.  Pattern matches should return a common supported shape.

```lean
namespace LeanExe.Examples.ManualStatus

inductive Status where
  | ok
  | retry (code : UInt64)
  | fail

def statusCode : Status -> UInt64
  | .ok => 0
  | .retry code => code
  | .fail => 999

end LeanExe.Examples.ManualStatus
```

Use `deriving BEq, DecidableEq` when source code compares structures or nonrecursive tagged values with `==`, `!=`, or `if left = right then ...`.  Lean still needs those instances for the program to type-check, but LeanExe lowers the comparison from the concrete value type rather than by executing an instance dictionary at runtime.  Structural equality supports products, structures, internal sums, `Option`, `Except`, and nonrecursive tagged values when every runtime field has supported equality.  `ByteArray` equality compares lengths and bytes, and `Array` equality compares lengths and elements when the element type has a fixed-width layout and supported equality.  Recursive-inductive equality remains unsupported, including array element equality for recursive inductive values.

Use recursive inductives as internal data.  They may be constructed, stored in internal arrays, traversed, returned from helpers, and carried in `Option`, `Except`, structures, or tagged values inside the compiled program.  They cannot appear as public entry parameters or public entry results.

```lean
namespace LeanExe.Examples.ManualTree

inductive Tree where
  | empty : Tree
  | node : UInt64 -> Tree -> Tree -> Tree

def size : Tree -> UInt64
  | .empty => 0
  | .node _ left right => 1 + size left + size right

def contains (needle : UInt64) : Tree -> Bool
  | .empty => false
  | .node value left right =>
      if needle == value then
        true
      else if needle < value then
        contains needle left
      else
        contains needle right

end LeanExe.Examples.ManualTree
```

Structural recursion works best when the recursive argument is the first parameter or when recursive descent follows accepted generated shapes.  If the report rejects a recursive helper, rewrite it so the recursive data parameter drives the match directly and nonrecursive carried values remain explicit parameters.

## Option, Except, and Error Results

`Option` works well for internal parse failures, search results, and optional values.  Match explicitly on `some` and `none` when the control flow is clearer as a case split.  Use `Option` `do` notation when parse steps should short-circuit on `none`; LeanExe lowers accepted `Pure.pure`, `Bind.bind`, and loop forms to the same tagged representation as explicit matches.

```lean
def optionOrZero (value : Option UInt64) : UInt64 :=
  match value with
  | some n => n
  | none => 0

def checkedPair (a? b? : Option UInt64) : Option (UInt64 × UInt64) :=
  do
    let a <- a?
    let b <- b?
    some (a, b)
```

`Except ByteArray ByteArray` is the preferred command result type when a byte-oriented program can fail.  In WASI `Except` modes, `Except.ok bytes` writes to stdout and exits successfully.  `Except.error bytes` writes to stderr and exits with status `1`.

```lean
namespace LeanExe.Examples.ManualExcept

def errorJson : ByteArray :=
  "{\"error\":1}".toUTF8

def bangOrError (input : ByteArray) : Except ByteArray ByteArray :=
  if input.size == 0 then
    Except.error errorJson
  else
    Except.ok (input.push (33 : UInt8))

def bangOrErrorDo (input : ByteArray) : Except ByteArray ByteArray :=
  do
    let bytes <-
      if input.size == 0 then
        Except.error errorJson
      else
        Except.ok input
    pure (bytes.push (33 : UInt8))

end LeanExe.Examples.ManualExcept
```

Parser-shaped `Except` code may call helpers whose bodies use accepted loops.  The successful path can return a scalar, structure, tagged value, array, or byte array when that value fits the normal layout rules.  The error path short-circuits later binds and later monadic loop iterations, so a failed parse skips later computation exactly as Lean does.

```lean
def digitByteOrError (byte : UInt8) : Except UInt64 UInt8 :=
  if (48 : UInt8) <= byte && byte <= (57 : UInt8) then
    Except.ok (byte - 48)
  else
    Except.error byte.toUInt64

def digitBytes : Except UInt64 ByteArray := do
  let first <- digitByteOrError (52 : UInt8)
  let second <- digitByteOrError (53 : UInt8)
  pure ((ByteArray.empty.push first).push second)

def checkedLoop (values : Array UInt64) : Except UInt64 UInt64 := do
  let mut sum := (0 : UInt64)
  for value in values do
    if value > 100 then
      Except.error value
    else
      sum := sum + value
  return sum
```

The supported `Option` and `Except` combinators include direct `map` and `bind`, overloaded `Functor.map`, and `do` notation that elaborates to accepted `Pure.pure`, `Bind.bind`, and `ForIn.forIn` forms.  Monadic `for` loops are accepted over `ByteArray`, fixed-width arrays, and ranges, and monadic `while` loops are accepted through Lean's checked `Lean.Loop` form.  The callback must be written at the call site, and callback values must not pass through variables, structures, arrays, or helper parameters.

Compile a stdin command:

```sh
.lake/build/bin/lean-wasm compile-wasi-stdin-except \
  --max-input-bytes 65536 \
  --module LeanExe.Examples.ManualExcept \
  --entry LeanExe.Examples.ManualExcept.bangOrError \
  --out build/bang-or-error.wasm
```

## Pure Mutable Code

Use `Id.run do` when the clearest source shape has local mutable state.  Lean elaborates `let mut`, assignment, `for`, `while`, `break`, and `continue` into pure first-order terms, and LeanExe accepts the checked forms for supported accumulator types.  This is often the most readable way to write scanner and transformer code with counters, cursors, byte output buffers, status values, or small state structures.

```lean
namespace LeanExe.Examples.ManualLoops

structure ScanState where
  count : UInt64
  sum : UInt64

structure BufferState where
  pos : Nat
  out : ByteArray
  ok : Bool

inductive StepStatus where
  | ok : UInt64 -> StepStatus
  | skip : UInt64 -> StepStatus

def classify (x : UInt64) : Option UInt64 := Id.run do
  let mut result : Option UInt64 := none
  if x > 10 then
    result := some (x + 1)
  else if x == 10 then
    result := some x
  return result

def classifyOption (input : Option UInt64) : UInt64 := Id.run do
  let mut result := (0 : UInt64)
  if let some value := input then
    result := value + 1
  else
    result := 100
  return result

def classifyStatus (status : StepStatus) : UInt64 := Id.run do
  let mut result := (0 : UInt64)
  if let StepStatus.ok value := status then
    result := value + 1
  else
    result := 100
  return result

def scan (values : Array UInt64) : ScanState := Id.run do
  let mut state : ScanState := { count := 0, sum := 0 }
  for value in values do
    if value == 0 then
      continue
    state := { count := state.count + 1, sum := state.sum + value }
  return state

def boundedSum : UInt64 := Id.run do
  let mut i := (0 : UInt64)
  let mut sum := (0 : UInt64)
  while i < 10 do
    if i == 7 then
      break
    sum := sum + i
    i := i + 1
  return sum

def scanDigits (input : ByteArray) : Except UInt64 ScanState := Id.run do
  let mut pos : Nat := 0
  let mut sum := (0 : UInt64)
  let mut result : Except UInt64 ScanState := Except.ok { count := 0, sum := 0 }
  while pos < input.size do
    let byte := input[pos]!
    if (48 : UInt8) <= byte && byte <= (57 : UInt8) then
      sum := sum + (byte.toUInt64 - 48)
      pos := pos + 1
      result := Except.ok { count := pos.toUInt64, sum := sum }
    else
      result := Except.error pos.toUInt64
      break
  return result

def collectDigits (input : ByteArray) : BufferState := Id.run do
  let mut state : BufferState := { pos := 0, out := ByteArray.empty, ok := true }
  while state.pos < input.size do
    let byte := input[state.pos]!
    if (48 : UInt8) <= byte && byte <= (57 : UInt8) then
      state := { pos := state.pos + 1, out := state.out.push (byte - 48), ok := state.ok }
    else
      state := { state with ok := false }
      break
  return state

end LeanExe.Examples.ManualLoops
```

Ordinary pure `Id.run do` blocks may use mutable scalars, structures, byte arrays, arrays, `Option`, `Except`, products, supported tagged values, and internal recursive pointers.  State records may contain heap fields such as `ByteArray` and internal `Array` values.  Nested `if`, `match`, and `if let` branches are accepted when Lean's generated continuation lambdas stay local and first-order.  `if let` and catch-all matches over `Option` and nonrecursive user inductives are accepted when Lean elaborates them to sparse generated match helpers.  Parser-style loops may combine mutable cursors, `ByteArray` indexing, mutable output buffers, mutable arrays, and explicit `Except` status values.  If a local function escapes as a runtime value, the compiler rejects it under the normal higher-order-function rule.

Accepted `for` collections are `ByteArray`, fixed-width `Array` values, and ranges such as `[start:stop]` or `[start:stop:step]`, when the checked monad is `Id`, `Option`, or `Except ε`.  Source `while` loops compile through Lean's `Lean.Loop` iterator and repeat until the checked loop step returns `ForInStep.done`.  Loop accumulators may be scalars, byte arrays, internal arrays, products, structures, nonrecursive tagged values, or recursive-inductive pointers, with the same field-type limits used elsewhere in the language.

Nested loops are accepted when each loop has a supported monad, collection, and accumulator.  The body may contain ordinary `do`-notation binds, local `let` bindings, generated product or structure destructuring, `break`, `continue`, and nested accepted loops.  `Option` and `Except` loop bodies stop after `none`, `Except.error`, or `break`, so later iterations and later trapping computations are skipped.  The compiler still rejects monads other than `Id`, `Option`, and `Except ε`, runtime callback values, polymorphic iterators, and loop bodies whose hidden carried values have unsupported runtime types.

## Arrays

Use arrays when the element type has a fixed-width layout.  Public arrays cannot contain heap-reference fields such as `ByteArray`, nested arrays, or recursive data.  Internal arrays may contain `ByteArray`, nested arrays, recursive pointers, and structures or tagged values that contain those internal pointer fields.  A `ByteArray` element uses owner, pointer, and length slots internally; a nested array element uses owner and pointer slots internally.  Copied array elements retain compiler-owned child roots.

Stable array operations include literals, `Array.size`, `isEmpty`, indexing, safe indexing, `getD`, `back?`, `push`, `pop`, `append`, `extract`, `set`, `set!`, `setIfInBounds`, `modify`, `insertIdx`, `eraseIdx`, `swap`, `reverse`, `map`, `filter`, `find?`, `findIdx?`, `any`, `all`, `foldl`, and `foldlM`.  Bang operations trap on invalid indexes.  Updates allocate fresh arrays and preserve Lean value semantics.

Direct lambdas are the safest callback form:

```lean
namespace LeanExe.Examples.ManualArray

structure SumCount where
  sum : UInt64
  count : UInt64

def addItem (state : SumCount) (item : UInt64) : SumCount :=
  { sum := state.sum + item, count := state.count + 1 }

def averageFloor (values : Array UInt64) : UInt64 :=
  let state := values.foldl (fun state item => addItem state item) { sum := 0, count := 0 }
  if state.count == 0 then
    0
  else
    state.sum / state.count

end LeanExe.Examples.ManualArray
```

Avoid passing named higher-order callbacks around as runtime values.  Write the lambda at the call site, call a concrete helper inside the lambda, and keep the accumulator type concrete.  If a fold over `array.attach` is needed for a termination proof, match the attached element immediately and use the runtime value while ignoring the proof field.

Use `foldlM` when the fold should stop at the first `none` or `Except.error` and the direct callback form is clearer than `for` syntax.  The accepted monads are `Option` and `Except ε`, and the callback must be a direct lambda whose accumulator and error payload types have supported layouts.  Later elements are not evaluated after failure, so code in those callbacks may contain trapping expressions that Lean would skip.

```lean
def checkedSum (values : Array UInt64) : Except UInt64 UInt64 :=
  values.foldlM (m := Except UInt64)
    (fun acc value =>
      if value > 100 then
        Except.error value
      else
        Except.ok (acc + value))
    0
```

```lean
def foldAttached (items : Array UInt64) : UInt64 :=
  items.attach.foldl
    (fun acc item =>
      match item with
      | ⟨value, _hmem⟩ => acc + value)
    0
```

## Byte Arrays and ASCII Text

Use `ByteArray` for binary input, binary output, and command boundaries.  Public calls pass byte arrays as pointer-length pairs.  Compiled helpers carry an internal owner slot as well, which keeps an allocated byte-buffer root alive when a slice or byte array field is stored in an array, structure, or tagged value.  Supported operations include `size`, `isEmpty`, `get!`, safe indexing, `extract`, `empty`, `mk` from `Array UInt8`, compile-time ASCII `.toUTF8`, `push`, `append`, append notation, `set`, `set!`, `copySlice`, `foldl`, `foldlM`, `findIdx?`, `toUInt64LE!`, `toUInt64BE!`, and equality.

Use `LeanExe.AsciiString` for byte-indexed ASCII text after validation.  The public boundary should usually remain `ByteArray`; validate with `AsciiString.ofByteArray?` inside the program.  Runtime Lean `String` and `Char` are outside the language.

```lean
import LeanExe.Ascii.Decimal

namespace LeanExe.Examples.ManualAscii

def countDigits (input : ByteArray) : UInt64 :=
  match AsciiString.ofByteArray? input with
  | none => 0
  | some text =>
      let digits :=
        text.toByteArray.foldl
          (fun acc byte =>
            if Ascii.isDigit byte then
              acc + 1
            else
              acc)
          0
      digits

end LeanExe.Examples.ManualAscii
```

Compile-time ASCII string literals are accepted when consumed by supported string operations such as `.toUTF8`, `.length`, `.isEmpty`, `==`, and `!=`.  The compiler rejects non-ASCII literal bytes in this path.  Runtime strings remain unsupported even when the source type-checks in Lean.

## Fuel Recursion

Use explicit `Nat` fuel for loops that are not structural recursion over a recursive inductive.  Put fuel first, decrease it on every recursive call, and return a supported value when fuel reaches zero.  Tail-position calls compile to WASM loops in the accepted shapes.

```lean
namespace LeanExe.Examples.ManualFuel

def collatzStep (n : UInt64) : Option UInt64 :=
  if n == 0 then
    none
  else if n % 2 == 0 then
    some (n / 2)
  else
    let next := n * 3 + 1
    if next < n then none else some next

def collatzLengthFuel : Nat -> UInt64 -> UInt64 -> Option UInt64
  | 0, _n, _steps => none
  | fuel + 1, n, steps =>
      if n == 1 then
        some steps
      else
        match collatzStep n with
        | some next => collatzLengthFuel fuel next (steps + 1)
        | none => none

def collatzLength (n : UInt64) : UInt64 :=
  match collatzLengthFuel 10000 n 0 with
  | some steps => steps
  | none => 0

end LeanExe.Examples.ManualFuel
```

Fuel is part of source behavior.  Choose a bound that makes sense for the input protocol, return an error on exhaustion when failure should be observable, and avoid `partial`.  Bounded recursion is also useful for parsers whose state is a supported structure.

## Structural Recursion

Use structural recursion for internal recursive data.  Recursive calls should follow direct recursive fields or accepted array-child traversal shapes.  Public entries should accept ABI-friendly values, build the recursive value internally, process it, and return an ABI-friendly result.

```lean
namespace LeanExe.Examples.ManualList

def sumList : List UInt64 -> UInt64
  | [] => 0
  | head :: tail => head + sumList tail

def demo : UInt64 :=
  sumList [1, 2, 3, 4]

end LeanExe.Examples.ManualList
```

Monomorphic `List UInt64` is useful inside the program, but `List` has no public ABI.  Direct source-defined helpers are safer than arbitrary library combinations.  Use library calls such as `List.map`, `List.filter`, `List.find?`, `List.foldl`, `List.any`, and `List.all` only in shapes already covered by accepted examples, with direct lambdas and concrete types.

Structural helpers may put first-order parameters before the recursive argument.  Lean often lowers that source shape to expression-position structural recursion, and LeanExe compiles it by generating a private helper whose first parameter is the recursive value and whose later parameters carry the captured first-order values.  This supports ordinary helpers such as `contains needle tree`, provided the captured values have supported internal parameter types and recursive calls descend through Lean's generated below value.

## JSON Programs

LeanExe provides two JSON layers.  Use `LeanExe.Ascii.Json` range helpers for small top-level object or array scans.  Use `LeanExe.Ascii.Json.Value` when the program needs complete nested JSON parsing and rendering through a recursive AST.

Range-helper example:

```lean
import LeanExe.Ascii.Json

namespace LeanExe.Examples.ManualJsonField

def resultField : ByteArray :=
  "value".toUTF8

def transformAscii (text : AsciiString) : ByteArray :=
  match LeanExe.Ascii.Json.getUInt64Field text "n".toUTF8 with
  | some n => LeanExe.Ascii.Json.object1UInt64 resultField (n + 1)
  | none => LeanExe.Ascii.Json.errorJson

def transform (input : ByteArray) : ByteArray :=
  match AsciiString.ofByteArray? input with
  | some text => transformAscii text
  | none => LeanExe.Ascii.Json.errorJson

end LeanExe.Examples.ManualJsonField
```

AST-rendering example:

```lean
import LeanExe.Ascii.Json.Value

namespace LeanExe.Examples.ManualJsonAst

open LeanExe.Ascii.Json

def answerName : AsciiString :=
  AsciiString.ofTrustedByteArray "answer".toUTF8

def answerJson : ByteArray :=
  render (object1Value answerName (Value.num 42))

end LeanExe.Examples.ManualJsonAst
```

Typed AST decoders should use `LeanExe.Ascii.Json.Decode` when failures should flow through `Except ByteArray`.  The helper layer provides required-field lookup, duplicate rejection through `getUniqueField?`, object field whitelisting through `requireOnlyFields`, typed scalar assertions, `decodeRequiredField`, `decodeUInt64Array`, generic `decodeArray` with a direct decoder lambda, and `renderExcept`.  This style works well for small request structures whose schema is explicit in Lean source.

```lean
import LeanExe.Ascii.Json.Decode

namespace LeanExe.Examples.ManualJsonDecode

open LeanExe.Ascii.Json

structure Request where
  values : Array UInt64
  multiplier : UInt64

def valuesName : AsciiString :=
  AsciiString.ofTrustedByteArray "values".toUTF8

def multiplierName : AsciiString :=
  AsciiString.ofTrustedByteArray "multiplier".toUTF8

def decodeRequest (value : Value) : Except ByteArray Request := do
  let fields <- requireObject value
  let numbers <- decodeRequiredField fields valuesName
    (fun raw => decodeUInt64Array raw)
  let multiplier <- decodeRequiredField fields multiplierName
    (fun raw => requireUInt64 raw)
  pure { values := numbers, multiplier := multiplier }

end LeanExe.Examples.ManualJsonDecode
```

Use `decodeRequiredField` and `decodeArray` together when a JSON array field should become an array of source-defined structures.  The decoder argument should be a direct lambda at the call site, because LeanExe specializes that lambda into the helper body rather than compiling a runtime function value.

```lean
structure Item where
  id : UInt64
  weight : UInt64

def idName : AsciiString :=
  AsciiString.ofTrustedByteArray "id".toUTF8

def weightName : AsciiString :=
  AsciiString.ofTrustedByteArray "weight".toUTF8

def itemsName : AsciiString :=
  AsciiString.ofTrustedByteArray "items".toUTF8

def decodeItem (value : Value) : Except ByteArray Item := do
  let id <- requireUInt64Field value idName
  let weight <- requireUInt64Field value weightName
  pure { id := id, weight := weight }

def decodeItems (value : Value) : Except ByteArray (Array Item) :=
  decodeArray (fun item => decodeItem item) value

def decodeItemsField (fields : Array Field) : Except ByteArray (Array Item) :=
  decodeRequiredField fields itemsName
    (fun raw => decodeArray (fun item => decodeItem item) raw)
```

For recursive JSON decoders, prefer the pattern used by [JSON Tree WASI Demo](demo.md).  The important source shape is `fields.attach.foldl` with an immediate match on `⟨field, _hmem⟩`, because Lean's termination proof can use field membership to show recursive calls descend into smaller JSON values.  A generic object getter may be valid Lean but still lower to a well-founded-recursion shape that LeanExe does not yet compile in recursive decoders.

```lean
fields.attach.foldl
  (fun state item =>
    match item with
    | ⟨field, _hmem⟩ =>
        let name := Field.name field
        let value := Field.value field
        -- inspect name, decode value, and update state
        state)
  initialState
```

The JSON AST supports `null`, booleans, unsigned `UInt64` numbers, restricted unescaped ASCII strings, arrays, and objects.  It rejects signed numbers, fractional numbers, exponent notation, string escapes, Unicode, malformed nesting, trailing commas, trailing input, and non-ASCII bytes.  Use `Except ByteArray ByteArray` at WASI boundaries when malformed JSON should produce `{"error":1}` on stderr with a nonzero exit status.

## Matches That Compile Reliably

Prefer direct matches with explicit constructor arms:

```lean
def boolToU64 : Bool -> UInt64
  | true => 1
  | false => 0

def optionToU64 : Option UInt64 -> UInt64
  | some n => n
  | none => 0
```

For nonrecursive user inductives, sparse `if let` and catch-all matches are accepted when every arm stays first-order.  The fallback arm receives the source tagged value for each unmatched constructor path, so a fallback branch may rematch the value.  Recursive inductives still need explicit constructor arms in the accepted structural-recursion shapes.

Use `_` for unused payload fields, but avoid relying on wildcard catch-all arms over large inductives.  In source templates intended for LLM generation, spelling every constructor is more predictable than clever pattern compression.  This rule matters most for recursive ASTs such as JSON values.

## Compile-Time Strings

Use Lean string literals only when they are consumed at compile time.  The common accepted pattern is assigning a field name or literal output through `.toUTF8`, then converting to `AsciiString` when needed.

```lean
def okBytes : ByteArray :=
  "ok".toUTF8

def name : AsciiString :=
  AsciiString.ofTrustedByteArray "name".toUTF8
```

The accepted compile-time string operations are restricted ASCII `String.toUTF8`, `String.length`, `String.isEmpty`, `==`, `!=`, `String.append`, and append notation through `++`.  Runtime `String` parameters, results, indexed strings, `Char`, UTF-8 decoding, and Unicode semantics are unsupported.  Public text protocols should use `ByteArray` plus explicit ASCII validation.

## Debugging Rejections

Use the report command before changing the compiler.  The most useful information is usually the first rejected declaration or the first unsupported external dependency.  Read the dependency name carefully; it often tells you which Lean source form generated the unsupported shape.

```sh
.lake/build/bin/lean-wasm report \
  --module LeanExe.Examples.MyProgram \
  --entry LeanExe.Examples.MyProgram.entry
```

Use `ownership-report` when an accepted program's allocation or release behavior needs inspection.  The command compiles the same checked entry, then prints ownership data from the extracted IR: result owner offsets, helper fresh-result summaries, compiler-emitted releases, returned owner expressions, fold accumulator release offsets, and explicit `LeanExe.Runtime.release` expressions.  This report is meant for compiler development and for source-level ownership boundaries; ordinary source rejection should still start with `report`.

```sh
.lake/build/bin/lean-wasm ownership-report \
  --module LeanExe.Examples.MyProgram \
  --entry LeanExe.Examples.MyProgram.entry
```

Common rejections and source fixes:

| Report symptom | Likely cause | Source fix |
|----------------|--------------|------------|
| `_sparseCasesOn` | Sparse match outside the accepted `Option` or nonrecursive-inductive shape | Write explicit constructor arms. |
| Higher-order argument or closure | Callback escaped as runtime value | Use a direct lambda at the call site. |
| Unsupported function type | Public entry or helper uses unsupported ABI shape | Move recursive data or products to internal helpers; expose scalar, structure, tagged, array, or byte values. |
| Runtime `String` or `Char` dependency | Text was not consumed at compile time | Use `ByteArray` and `AsciiString`. |
| External Lean or Std dependency | Library function lacks a primitive or accepted specialization | Inline a first-order helper or use a supported operation. |
| Type-class instance dependency in behavior | Runtime dispatch survived elaboration | Add concrete types, avoid overloaded helpers, or rewrite with direct operations. |
| Unsupported recursion shape | Lean generated an unsupported recursor or well-founded helper | Use explicit fuel or direct structural recursion over the recursive argument. |
| Public nested array rejection | Entry ABI contains heap-reference element fields | Keep nested arrays internal or expose bytes/scalars instead. |

Do not fix source by adding dummy effects, unsafe definitions, hidden runtime calls, or unchecked host assumptions.  A program accepted by LeanExe should have behavior explainable through the specification.  If a natural source shape repeatedly fails, reduce it to a small example and add it to the compiler test plan.

## Comparing With Standard Lean

Use `tools/compare-standard.js` when an accepted program should match official Lean execution.  The tool generates a temporary Lean runner that imports the target module and calls the selected entry, then compares that result with the WASM produced by LeanExe and executed by Wasmtime.  Command modes compare observable process behavior: exit status, stdout bytes, and stderr bytes.  Pure mode compares library exports invoked with `wasmtime --invoke`, using a result-slot expression to print the standard Lean result in the same flattened `UInt64` slot shape returned by the WASM export.  Pure-bytes mode serializes a concrete pure result to `ByteArray`, compiles a generated wrapper through `compile-wasi`, and compares standard Lean's serialized bytes with the generated command output.

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
  --entry structureParam \
  --arg 2 \
  --arg 3 \
  --standard-call 'LeanExe.Examples.Correctness.structureParam ({ x := (2 : UInt64), y := (3 : UInt64) } : LeanExe.Examples.Correctness.Point)' \
  --result-slots '#[__leanexeValue]'
```

The supported command modes correspond to the WASI command compilers: `wasi`, `stdin`, `stdin-except`, `argv-except`, and `stdin-argv-except`.  Pure mode uses `compile` rather than a WASI adapter.  It works best for deterministic entries that do not inspect LeanExe runtime counters and do not rely on intentionally skipped trapping expressions.  Runtime counters are compiler intrinsics in generated WASM, while standard Lean evaluates their stub definitions.

Pure-bytes mode works best for heap-backed pure results whose observable value can be serialized by ordinary accepted Lean code.  The generated wrapper binds the result as `__leanexeValue`, then evaluates the caller's `--serializer` expression.  The serializer must have type `ByteArray` and should stay inside the accepted subset, because LeanExe compiles the generated wrapper as ordinary source.

## LLM Source Generation Checklist

Use this checklist when asking an LLM to write LeanExe source:

- Name the module and the fully qualified entry declaration.
- State the compile mode and required entry type.
- Require concrete first-order helper definitions.
- Require public entry types from the supported ABI.
- Require `UInt64` for external integers unless bounded `Nat` is needed.
- Require `ByteArray` for text or binary public input.
- Require `Except ByteArray ByteArray` for command errors.
- Require explicit constructor arms for recursive inductives and JSON AST matches.
- Require direct lambdas for array and byte-array folds.
- Require fuel for parser-like recursion and structural recursion for internal recursive data.
- Prohibit `IO`, `unsafe`, `partial`, runtime `String`, runtime `Char`, type classes as runtime behavior, closures, and arbitrary Std helpers.
- Ask for a compile command and a report command with the generated entry.

A good prompt says what should happen on malformed input, overflow, empty input, and fuel exhaustion.  It should also say whether duplicate JSON fields are allowed, whether unknown JSON fields are allowed, and whether output errors should go to stderr through an `Except` WASI adapter.  The compiler will not infer these protocol decisions from the type alone.

## Example Map

Use existing examples as templates:

| Need | Example |
|------|---------|
| Scalar arithmetic | [Collatz Example](LeanExe/Examples/Collatz.lean), [Prime Example](LeanExe/Examples/Prime.lean) |
| Compile-time strings and byte arrays | [ByteArray Programs](LeanExe/Examples/ByteArrayPrograms.lean) |
| ASCII validation and text processing | [ASCII String Programs](LeanExe/Examples/AsciiStringPrograms.lean) |
| Open-addressed table structure | [Integer Map Example](LeanExe/Examples/IntMap.lean) |
| Range-based JSON field lookup | [JSON Double Example](LeanExe/Examples/JsonDouble.lean), [JSON Add Example](LeanExe/Examples/JsonAdd.lean) |
| Typed JSON AST decoding | [JSON Typed Decode Example](LeanExe/Examples/JsonTypedDecode.lean), [JSON Object Array Decode Example](LeanExe/Examples/JsonObjectArrayDecode.lean) |
| JSON AST parsing and rendering | [JSON Tree Command](LeanExe/Examples/JsonTreeCommand.lean) |
| WASI stdin `Except` command | [JSON GCD Example](LeanExe/Examples/JsonGcd.lean) |
| End-to-end WASI pipeline | [JSON Tree WASI Demo](demo.md), [JSON Merge Tree Command](LeanExe/Examples/JsonMergeTreeCommand.lean) |
| Source-level release and GC counters | [JSON GC Tree Rewrite Example](LeanExe/Examples/JsonGcTreeRewrite.lean) |
| Broad compiler fixtures | [Correctness Examples](LeanExe/Examples/Correctness.lean) |

The examples are executable tests as well as documentation.  If a new source pattern matters, add a small example and run the test harness.  The safest authoring practice is to make each new feature compile in isolation before combining it with JSON, WASI, recursive data, or structured accumulators.
