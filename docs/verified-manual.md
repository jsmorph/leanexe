# Verified Compiler Manual

This manual describes the verified compiler, the library `Verified`: the Lean dialect that it accepts, the command that compiles a program and the theorems that the command adds, the bounds that make a call free of traps, the tests, and the examples.  [The LeanExe compiler manual](leanexe-manual.md) describes the other compiler, and [the README](../README.md) compares the two.  [The verified compiler's internals](../Verified/README.md) describe its code scheme and the structure of its proof, and [the design document](design.md) gives the decisions and the open work.

## Overview

### What the compiler does

The verified compiler is a Lean function, `compileWith` in [`Verified/Compile.lean`](../Verified/Compile.lean), from a typed source language to a module of Talos, the WebAssembly interpreter written in Lean.  One theorem, `Prog.correctWith` in [`Verified/Correct.lean`](../Verified/Correct.lean), states that the module of every program of the source language, with its tables and wrappers, computes the program's meaning, so no program needs a proof of its own.  `Prog.correct` states the same for a program without tables.  The command `verified_compile p := [f, g, …]` reads ordinary Lean definitions, writes each as a source function, and proves with kernel-checked equations that each source function means its definition.  It then states, for each definition `f`, that the module computes `f` with Lean's own types, and that the module's bytes decode to the module.  The reflector that writes the source functions is meta code and is not trusted: a wrong reflection makes an equation fail in the kernel and cannot produce a false theorem.

### What the theorems state

`p.f.implements` states `ImplementsA aborts p.module k f` ([`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean)), where `k` is the index of `f`'s function or entry in the module.  From any heap and store with the allocator invariant, a memory cap of at most 65,535 pages, and arguments that represent `x`, whose moved blocks lie apart from one another and from the memory that the call reads, a run returns words that represent `f x` and that the caller owns.  The run keeps the allocator invariant and the cap, keeps every region of the caller's heap that lies apart from the moved blocks, and places the result apart from those regions.  When `aborts` is true, a run may instead trap at `unreachable`, which the code does only when an allocation finds no memory, an array would hold `2^29` words or more, or a recursion reaches depth 1,000.  `aborts` is true when the function's result holds arrays, a parameter is owned, the body builds, updates, extends, inserts into, or removes from an array, or the body calls a function whose `aborts` is true, whose code takes the call depth, whose result holds arrays, or which owns a parameter.  Otherwise `aborts` is false, and the theorem excludes a trap.

`p.f.trapFree` states `ImplementsA false` for each source function, and `ImplementsTables false` for a wrapper whose callee takes no call depth: the call returns `f x` without a trap and raises `top` by at most the function's allocation bound.  When `aborts` is true, the theorem requires a store in which `top` can rise by the bound within the memory cap.  For a function whose code takes the call depth, it also requires a frames condition, which states that every call of the run to a function of this kind happens below depth 1,000.  The reflector also states the bound and the frames condition as Lean terms in the function's parameters, so a concrete bound follows by rewriting, as [Bounds](#bounds-and-total-execution) describes.

### Trusted base

The trusted base is that of the LeanExe compiler: Lean's kernel with the axioms `propext`, `Classical.choice`, and `Quot.sound`, Talos's semantics, the binary decoder, and the step from a constant to a file that [`tools/Emit.lean`](../tools/Emit.lean) performs.  [The LeanExe compiler manual](leanexe-manual.md#trusted-base) describes each part.  The statements of the verified compiler add definitions of their own: `Heap.Within` in [`Verified/Heap.lean`](../Verified/Heap.lean), which states that `top` plus a bound fits within the memory cap, the allocation bound of [`Verified/Bound.lean`](../Verified/Bound.lean), `ImplementsTables` for wrappers, and `initialHeap` and `tableAddr`, which `p.initial` uses.  The compiler, the reflector, and the bound equations are not trusted, since the kernel checks every theorem they produce.

### Outside the proofs

The theorems hold in Talos's semantics, which bounds no call depth and grows memory whenever the new page count is within the cap.  Wasmtime ends a deep recursion with a stack-overflow trap, so the code traps at depth 1,000, and the reflector limits the frame of every function whose code takes the call depth to 32 positions.  The tests run a frame of 32 positions, 26 of them live across the self-call, at depth 999 on Wasmtime 44 for aarch64.  `p.initial` proves that the store in which the module starts meets the allocator invariant and the cap and holds the tables, and no theorem covers the host or the I/O around a call.  The floating-point theorems describe the WebAssembly deterministic profile, as the LeanExe compiler's do.  The numerical examples have further theorems about mathematical functions, rounding, and exceptional values, with the domains and bounds listed in [the numerical index](../index.md) and each function's document.

## The dialect

[`Verified/Source.lean`](../Verified/Source.lean) defines the source language: the types `Ty`, the element types `Elem`, the expressions `Expr S Γ t`, typed by the callees' signatures `S` and the context `Γ`, and their meaning `denote`.  A program consists of ordinary Lean definitions, which the reflector translates into this language.  The reflector's error messages name the term or the type that it cannot translate.

### Programs and definitions

A program is the list of definitions in `verified_compile p := [f₁, …, fₙ]`.  A definition may call the definitions before it in the list and, when it is recursive, itself, so the only cycles are a definition's calls of itself.  When no source rule covers a term, the reflector unfolds a helper marked `@[inline]`, including an `abbrev`, and checks the equation for its expanded body.  A listed helper compiles as a function and takes precedence over unfolding.  A named constant that holds no array is reflected as its value.  The reflector reads a recursive definition through its unfolding equation `f.eq_def`, so it accepts structural and well-founded recursion, and it rejects a definition with universe parameters and a recursive definition that uses `sorry`.

### Types

| Type | Representation | Notes |
|---|---|---|
| `UInt64` | One i64 word | Arithmetic wraps modulo `2^64`. |
| `Bool` | One i64 word, 1 or 0 | |
| `Float` | One f64 word, its bit pattern | Lean's binary64, which equals Talos's `IEEE64` on bit patterns. |
| A pair of types without arrays | The first component's words, then the second's | Nested pairs are tuples. |
| A structure with a `Flat` instance whose tuple is its fields | Its fields' words | A nested structure is flattened in turn. |
| An enumeration with a `Flat` instance to a word | One word | An inductive type whose constructors have no fields. |
| `Array α`, for `α` a word, `Bool`, float, tuple, flat structure, or enumeration | The address of a length word followed by the elements' words | An element of `k` words occupies `k` consecutive words.  An array of tuples may only be a local value, since Lean has no `Represent` instance for it. |
| A pair that holds arrays, or a structure whose `Flat` tuple holds arrays | Its components' words | A structure of this kind is a record with array fields. |

`Nat`, `Int`, `Float32`, `String`, `Option`, `List`, recursive types, sum types with fields, and arrays of arrays are outside the dialect.  Integers are `UInt64`, so that a program and its module compute the same values, wraparound included.  A read past the end of an array gives Lean's default element, so a structure's default must take each field's default and an enumeration's default must have the word 0.

### Expressions

| Construct | Lean forms |
|---|---|
| Word arithmetic | `+`, `-`, `*`, `/`, `%`, `&&&`, `\|\|\|`, `^^^`, `<<<`, `>>>`, `min`, `max` |
| Word comparisons, unsigned | `==`, `!=`, `<`, `≤`, `>`, `≥`, `=`, `≠` |
| Float arithmetic | `+`, `-`, `*`, `/`, `Float.sqrt`, `Float.abs`, negation, `min`, `max`, literals |
| Float comparisons | `==`, `!=`, `<`, `≤`, `>`, `≥` |
| Conversions | `UInt64.toFloat`, `Float.toUInt64`, `Float.toBits`, `Float.ofBits` |
| `Bool` operations | `!`, `&&`, `\|\|`, `decide` |
| Bindings | `let`, and `match` on a pair, a tuple, or a structure |
| Conditionals | `if` on a `Bool` or a comparison, `if h : c` whose branches do not use `h`, and `match` on an enumeration |
| Calls | A listed definition applied to all its arguments, or an unfolded `@[inline]` helper |
| Combinators | `LeanExe.loop`, `LeanExe.repeatWhile`, `LeanExe.build` |
| Arrays | `#[]`, `xs.size.toUInt64`, `xs[i.toNat]!`, `xs.set! i.toNat v`, `xs.setIfInBounds i.toNat v`, `xs.push v`, `xs ++ ys`, `xs.insertIdxIfInBounds i.toNat v`, `xs.eraseIdxIfInBounds i.toNat`, `LeanExe.insertAt xs i v`, `LeanExe.eraseAt xs i` |
| Tuples and structures | `(a, b)`, `.1`, `.2`, constructors, `{ s with … }`, field reads |

Every construct has Lean's meaning.  Division by zero gives 0, the remainder by zero is the dividend, a shift uses its amount modulo 64, and an update, an insertion, or a removal past the end of an array leaves the array unchanged.  `min` and `max` are Lean's definitions, `if a ≤ b`, which on floats differ from `f64.min` and `f64.max` on NaN and on zeros of opposite sign.  `=` and `≠` on floats compare bit patterns, so `0.0 ≠ -0.0`, and no f64 instruction computes them, so the reflector rejects them and accepts `==` and `!=`.  Lean's other float functions, such as `Float.exp` and `Float.sin`, are opaque, so a program computes them with definitions of its own, as the ports of fdlibm and of Arm's optimized-routines among the examples do.

### Loops and builds

`LeanExe.loop n init f` applies `f` to the indices `0` to `n - 1` in order, starting from the state `init`.  `LeanExe.repeatWhile fuel init cond step` applies `step` while `cond` holds, at most `fuel` times, and `LeanExe.build n f` is the array of `n` elements whose element `i` is `f i`.  The modules of [`LeanExe/Dialect/`](../LeanExe/Dialect/) define the three, and the LeanExe compiler accepts them as well.  A state may have any type of the dialect, records with array fields included, and each part of a loop or a build is an expression of the dialect, which may hold further loops, builds, and calls.  `for`, `while`, `do` notation, `Array.foldl`, and `List.foldl` are outside the dialect, and tail recursion compiles as recursion under the depth guard, so an iteration over many steps uses one of the three combinators.

### Ownership

An array variable is borrowed or owned.  The reflector chooses each array parameter's mode with `Expr.paramChoice` in [`Verified/Reflect/Modes.lean`](../Verified/Reflect/Modes.lean): a parameter is owned when the body consumes it at its last use, as the array of an update, an extension, an insertion, or a removal, as an argument at an owned parameter, or as the result, and borrowed otherwise.  An owned parameter has type `Moved (Array α)` in the theorem, and the caller gives the array up.  The theorem holds for every choice of modes, so the choice affects only the code's cost.  When an update, an extension, an insertion, or a removal is the last use of an owned array, the code changes the array in its own block, and it copies any other array first.  An extension that finds no room moves the array to a block of at least twice its capacity, so the number of blocks that a loop of pushes allocates grows with the logarithm of its count.  The code releases each owned array after its last use, unless the array moves into the result or into an owned parameter.  A record parameter is always borrowed, so a callee that updates one of its arrays copies that array.

### Records, tuples, and enumerations

The reflector reads a structure through its `Flat` instance ([`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean)), which must map it to the tuple of its fields, each field once and in any order.  The reflector writes a constructor or `{ s with … }` as the tuple of the fields, a chain of field reads, `.1`, and `.2` as one projection, and a `match` on a structure as bindings of its fields.  A structure whose fields hold arrays is represented as its tuple by the instance `instRepresentOfFlat` of [`FlatRecords.lean`](../LeanExe/Pipeline/FlatRecords.lean), and it may be a parameter, a result, a local value, or a loop state.  An enumeration's `Flat` instance maps each constructor to a distinct word, by `ctorIdx` or by a `match`, and a `match` on an enumeration compiles to a chain of tests on the word.  `==` on an enumeration needs `LawfulBEq`, which `deriving DecidableEq` gives.  A `match` must have one discriminant and no `h :`.  [`Fields.lean`](../Verified/Examples/Fields.lean) and [`Enums.lean`](../Verified/Examples/Enums.lean) declare a record with array fields and an enumeration in this way:

```lean
open LeanExe.Pipeline

structure Book where
  prices : Array UInt64
  sizes : Array UInt64
  fills : UInt64
  deriving Inhabited

instance : Flat Book (Array UInt64 × Array UInt64 × UInt64) :=
  ⟨fun b => (b.prices, b.sizes, b.fills)⟩

inductive Phase where
  | solid | liquid | gas
  deriving Inhabited, DecidableEq

instance : Flat Phase UInt64 := ⟨fun | .solid => 0 | .liquid => 1 | .gas => 2⟩
```

### Calls and recursion

A call passes its arguments' words and receives its result's words, a pair or a record as several WebAssembly results.  The code of a recursive definition, and of every definition that calls one, takes the call depth as a first parameter, traps at `unreachable` when the depth reaches 1,000, and passes the depth plus one to the functions of this kind that it calls.  The module exports an entry under the definition's name that starts the call at depth 0.  A function whose code takes the call depth may use at most 32 positions, which count the call depth, the parameters' words, and the locals that the body's code uses.  Wasmtime keeps 8 bytes for each value live across a call and 16 bytes per frame, so 1,000 frames of 32 positions take at most 272,000 bytes of its 512 KiB default stack.  A recursive definition's meaning in the source is a solution of its body's fixed-point equation, and the reflector supplies the definition itself.  An enumeration may not appear in a parameter type of a recursive definition, since that meaning needs an inverse of the flattening, which an enumeration's words lack.

### Tables and wrappers

A table is a Lean constant of type `Array UInt64`, which the module writes in a data segment.  A function reads a table as a borrowed array parameter, and a wrapper is a listed definition of the form `f x := g T₁ … Tₖ x` that applies a listed function `g` to tables before its own parameters.  The module exports the wrapper as an entry that pushes the tables' addresses and calls `g`.  The wrapper's theorem, `ImplementsTables`, requires a store that holds each table at its address, apart from the blocks that the arguments move, and `p.initial` proves that the store in which the module starts holds them.  A wrapper is not a function of the program, so the other definitions pass tables as parameters, as `transformWith` in [`Fourier.lean`](../Verified/Examples/Fourier.lean) passes Trig's tables to `twiddleWith`, which passes them to `Trig.cosWith` and `Trig.sinWith`.

### Restrictions

| Message | Cause | Rewrite |
|---|---|---|
| `unsupported term …` | A term that no rule covers: an unlisted helper without `@[inline]`, `Array.foldl`, `for`, or an opaque float function | List the callee before its callers, mark a helper `@[inline]`, use the combinators, or define the float function. |
| `the type … is not UInt64, Bool, Float, a structure with a Flat instance, an array, or a pair` | A parameter, result, or binding of a type outside the dialect, such as `Nat` | Use the dialect's types, and give a structure a `Flat` instance. |
| `= and ≠ on Float compare bit patterns; use == and !=` | `=` or `≠` on floats | Use `==` or `!=`. |
| ``an index must be `i.toNat` for a word `i` ``, ``a position must be `i.toNat` for a word `i` `` | A read or an update at a position that is not a word's `toNat` | Index with `i.toNat` for `i : UInt64`. |
| `Lean has no Represent instance for …, so no theorem can be stated for it` | A parameter or result whose type has no instance, such as an array of tuples | Keep such an array local, or use an array of structures with a `Flat` instance. |
| `an array holds elements, not …` | An array of arrays, or of records with array fields | Store the inner arrays in one array at computed positions. |
| ``the `Flat` instance of … is not a tuple of its fields``, ``… repeats a field``, ``… does not hold all its fields`` | A `Flat` instance other than the tuple of the structure's fields | Map the structure to the tuple of its fields, each once. |
| `comparisons apply to words, floats, and enumerations, not …` | A comparison of other values | Compare the components. |
| `unsupported negation …` | `-x` on words | Write `0 - x`. |
| `… has universe parameters` | A universe-polymorphic definition | Define the function at one universe. |
| `a match on several values is not supported`, `` `match h : …` is not supported `` | A `match` with several discriminants or a named hypothesis | Nest the matches, and use `if` for tests. |
| `the branches of … use the hypothesis of the if` | `if h : c` with a branch that uses `h` | Read with `xs[i.toNat]!`, which needs no proof of the bound. |
| `… must be applied to all n arguments` | A partial application of a listed definition | Apply the definition to all its arguments. |
| `the code of … takes the call depth and needs k positions, more than the 32 …` | A recursive function, or a caller of one, with many live values | Move work into a function that calls no recursive function, or bind fewer values. |
| `the parameter type … of a recursive definition holds an enumeration …` | An enumeration parameter of a recursive definition | Pass the enumeration's word. |
| `the flattening of the default … is not the default element …` | A structure whose default does not take each field's default | Use `deriving Inhabited`. |
| `` `==` on … needs `LawfulBEq` `` | `==` on an enumeration without `LawfulBEq` | Use `deriving DecidableEq`. |
| `… must take the tables of … as borrowed arrays of words before its other parameters` | A wrapper whose callee takes the tables elsewhere | Put the table parameters first. |

## Compiling and running

### `verified_compile`

A program's file imports `Verified.Reflect.Command` and the definitions, and runs one command.  The definitions may be in another library, so a program of `Examples/` compiles unchanged, as [`Verified/Examples/Lcg.lean`](../Verified/Examples/Lcg.lean) shows for the generator of [`Examples/Lcg`](../Examples/Lcg/README.md).  The command lists the definitions in calling order, a callee before its callers.

```lean
import Verified.Reflect.Command
import Examples.Lcg.Jump

namespace Verified.Examples.Lcg

open _root_.Examples.Lcg

verified_compile compiled := [affine, step, advance, jumpPass, jump]
```

The command adds the program, the module, and every theorem in one step, and the kernel checks each.  The theorems use only the axioms `propext`, `Classical.choice`, and `Quot.sound`, as `#print axioms` shows for `Prog.correct`, `Prog.correctWith`, and each example's `compiled.bytes` and named theorems.  The declarations and the exports take the last component of a definition's name, so two listed definitions whose names end in the same component collide.

`set_option trace.Verified.reflect true` reports the reflection and proof-generation stages for each function and the encoding check for each function index.  Reflection entries include the remaining heartbeat budget in the units of `maxHeartbeats`.

### Generated declarations

| Declaration | Content |
|---|---|
| `p.program`, `p.funs`, `p.meaning` | The source program, the meanings of its functions, and the proof of `Prog.Meaning p.program p.funs`. |
| `p.tables`, `p.wrappers`, `p.module` | The tables, the wrappers, and the module `compileWith p.program p.tables p.wrappers`. |
| `p.initial` | The store in which the module starts meets the allocator invariant, caps the memory at 65,535 pages, and holds each table at its address. |
| `p.bytes` | `∃ bytes, encode p.module = .ok bytes ∧ decode bytes = .ok p.module ∧` the conjunction of the theorems `p.f.implements`. |
| `p.sections`, `p.bodies`, `p.data`, `p.encoding` | Literal byte lists for the sections, function bodies, and data, and their assembly into the module's bytes. |
| `p.func_ok_k`, `p.rest_ok`, `p.data_ok`, `p.codes_ok`, `p.funcs_count`, `p.funcs_length` | Kernel-checked encoding claims for each function, the other sections, and the sizes. |
| `p.encoded` | `encode p.module = .ok ⟨p.encoding.toArray⟩`, with the bound on each function's locals that `decode_encode` requires. |
| `p.f.func`, `p.f.denote_eq` | The source function of `f`, and the equation that it means `f`.  A wrapper has no source function, and its `denote_eq` states that it is its callee's meaning at the tables and its parameters. |
| `p.f.implements` | `ImplementsA aborts p.module k f` with Lean's instances for the argument tuple and the result, or `ImplementsTables` for a wrapper. |
| `p.f.argsAgree`, `p.f.resultAgree` | Lean's instances represent the arguments and the result as the source's instances represent their flattenings. |
| `p.f.bound`, `p.f.bound_eq` | The allocation bound in bytes on the argument tuple, and its equation in the parameters.  For a function whose code takes the call depth, the bound takes the number of frames first. |
| `p.f.cost`, `p.f.cost_eq` | For a function with a paid parameter: the bound without the credits of the paid arguments, and its equation. |
| `p.f.trapFree` | `ImplementsA false`, or `ImplementsTables false` for a wrapper.  When `aborts` is true, it requires room for the bound and, for a function whose code takes the call depth, the frames condition at 1,000 frames.  A wrapper whose callee takes the call depth has no `bound` and no `trapFree`. |
| `p.f.fits`, `p.f.fits_eq` | For a function whose code takes the call depth: the frames condition, and its equation. |
| `p.f.meaning`, `p.f.meaning_eq`, `p.f.fixed` | For a recursive definition: its meaning on source environments, the equation of its self-call, and the fixed-point equation. |
| `p.flat_injective.E` | For each enumeration that the program compares, with `E` its full name: its flattening is injective, which the comparisons of its words use. |
| `p.flat_eta.R`, `p.flat_field.R.f` | For each record with array fields that the reflector splits, with `R` its full name: the eta law of its flattening, and the equation of field `f` with its component of the flattening. |

Functions 0 and 1 of the module are the runtime's `alloc` and `release`, and function `2 + k` is the `k`-th listed definition that is not a wrapper, counted from 0.  In a program of `n` such definitions, the entry of the `j`-th definition whose code takes the call depth is function `2 + n + j`, and the wrappers follow the entries.  The module exports each definition under its name, at its entry when its code takes the call depth.

### Emitting and running

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/leanrun --timeout 60m lake build Verified.Examples.Lcg
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Verified.Examples.Lcg Verified.Examples.Lcg.compiled.module build/verified/lcg.wasm
wasm-tools validate build/verified/lcg.wasm
build/tools/leanexe-wasmtime-host call build/verified/lcg.wasm advance i64 i64:3 i64:1
```

`Verified` is not a default target, so `lake build` alone does not build it.  Every Lean command runs through `tools/leanrun`, which [the LeanExe compiler manual](leanexe-manual.md#toolsleanrun-and-the-single-lean-slot) describes.  `Emit.lean` evaluates the module, encodes it, checks that the decoder returns it, and writes the file.  The Wasmtime host is the LeanExe compiler's, whose argument and result kinds [the LeanExe compiler manual](leanexe-manual.md#the-wasmtime-host) lists: the host allocates an array argument through `alloc`, prints a float as its bit pattern, and reads a pair result with the kind `list:`.  `call-stats` also prints the runtime's allocation and release counts.  Besides the definitions, the module exports `alloc`, `release`, its memory as `memory`, and the counters `allocCount` and `freeCount`.

## Proving

### Using the generated theorems

The generated theorems state facts about Lean functions, so a theorem about a program combines with them in ordinary Lean.  `p.bytes` gives the bytes and their decoding, and `p.f.implements` gives a function's theorem.  `lcg_advance` in [`Lcg.lean`](../Verified/Examples/Lcg.lean) combines the module's bytes and theorem with the period theorem of [`Examples/Lcg/Period.lean`](../Examples/Lcg/Period.lean):

```lean
theorem lcg_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 4
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    ∀ x y : UInt64, ∃! n : UInt64, advance n x = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, advance_existsUnique⟩
```

A theorem for one function gives a theorem for an equal function by rewriting: `lcg_jump` rewrites `compiled.jump.implements` with `jump_eq`, which states that the jump-ahead program computes `advance`.  `ImplementsA.mono` strengthens a precondition or weakens a postcondition, and `drone_trapFree` in [`Drone.lean`](../Verified/Examples/Drone.lean) uses it to replace the planner's bound by the constant 2,251,064.  The drone's theorems `drone_compute` and `drone_safe` combine the bytes with the planner's optimality and safety theorems in the same way.

### Bounds and total execution

`p.f.bound x` counts the bytes by which the allocator's `top` can rise during the call: 48 bytes of header plus the payload for each copy, each built array, and each block of `push`, `++`, and `insertAt`, with no reuse of freed blocks.  `p.f.bound_eq` states the bound as a Lean term that follows the definition: the loop counts, states, and call arguments of the program, the block sizes `blockCost`, `growCost`, `paidGrowCost`, and `creditCost` of [`Verified/BoundFacts.lean`](../Verified/BoundFacts.lean), `loopCost` and `sumBelow` of [`Verified/Bound.lean`](../Verified/Bound.lean) for loops and builds, and `p.g.bound` at the arguments of a call, or, for a callee `g` with a paid parameter, `p.g.cost` and `creditCost` of each argument that the call charges.  A function that allocates nothing gets `p.f.bound x = 0`, and a record's arrays appear as its fields, such as `b.prices.size`.  `BoundFacts.lean` gives the closed forms, such as `blockCost_eq`, sums of `sumBelow`, `loopCost_const` for passes of equal cost, and `loopCost_le`, which bounds a loop's cost by an invariant of its index and state.  `pushSquare_bound` in [`Tables.lean`](../Verified/Examples/Tables.lean) shows the method:

```lean
theorem pushSquare_bound (xs : Array UInt64) (k : UInt64) :
    compiled.pushSquare.bound (⟨xs⟩, k) = 16 * (xs.size + 1) + 80 := by
  rw [compiled.pushSquare.bound_eq, compiled.pushWith.bound_eq, compiled.pushWith.cost_eq,
    creditCost, paidGrowCost_eq]
```

The bound charges an extension of an owned array by amortization.  An owned array of `n` words in a block of `c` bytes holds the potential `4 · 8 (n + 1) ∸ 2c`, and every owned array parameter of a function whose body extends an array, by `push`, `++`, `insertAt`, or a call with a paid parameter, is paid: the caller charges its credit, `creditCost`, 16 bytes per word and length word, and each extension of the paid array is charged `paidGrowCost`, a header and 32 bytes per added word.  The potential covers the bytes of the moves to larger blocks, so a loop of `n` pushes of one word onto a paid state is charged `80 n` bytes plus the credit.  For a function with a paid parameter, `p.f.cost` is the bound without the credits, and `p.f.bound` adds them.  [The internals](../Verified/README.md) give the rules that decide which values are paid.

The bound ignores the reuse of freed blocks and charges every extension of a dying owned array as a new block, so a precondition that fails says nothing about the program.  The bound also depends on the modes that `Expr.paramChoice` chooses.  The precondition `heap.Within store p.module (p.f.bound x)` states that `top` plus the bound is at most `65536` times the memory's cap, at most 4,294,901,760 bytes, and no theorem bounds the memory's size in pages.

### Recursion

For a function whose code takes the call depth, `p.f.bound k x` and `p.f.fits k x` take the number of frames `k` first, and `p.f.trapFree` holds under `p.f.fits 1000 x = true ∧ heap.Within store p.module (p.f.bound 1000 x)`.  `p.f.fits_eq` and `p.f.bound_eq` state `p.f.fits (k + 1) x` and `p.f.bound (k + 1) x` for every `k`, with `p.g.fits k` and `p.g.bound k` at each call of such a function `g`, the definition itself included.  For a function with a paid parameter, `p.f.cost_eq` states `p.f.cost (k + 1) x` in this way, with `p.g.cost k` and `creditCost` at a call of such a `g` with a paid parameter, and `p.f.bound_eq` states `p.f.bound k x` as the credits plus `p.f.cost k x`.  `p.f.fits 0 x = false` holds by `rfl`, so a property of `p.f.fits 1000 x` follows by induction on `k`.  In [`Recursion.lean`](../Verified/Examples/Recursion.lean), `chain_fits` shows in this way that `compiled.chain.fits k n` holds exactly when `n < k`, and `chain_trapFree` that the module computes `chain n` without a trap for every `n` below 1,000.  `fill_fits`, `fill_cost`, and `fill_trapFree` do the same for a recursion that extends a paid array parameter and moves it into the next call.

## Testing

### Module cases

[`tests/verified/run.sh`](../tests/verified/run.sh) writes each example's module to `build/verified/`, validates it with `wasm-tools`, and compares every case of [`Verified/Examples/Cases.lean`](../Verified/Examples/Cases.lean) between the Wasmtime host and native Lean.  `Cases.lean` prints one line per case, `module|export|result kind|host arguments|expected result`, computed by native Lean, with an optional sixth field, the number of blocks that must stay allocated after the call, and a seventh, a bound on the number of allocations, the host's included.  The expected result `trap` requires a trap at `unreachable`.  Native Lean writes a panic message for each read or update past the end, and the script counts these messages and fails on any other output to standard error.  The script needs `lake build Verified` first, the Wasmtime host `build/tools/leanexe-wasmtime-host`, and `~/.cargo/bin` on `PATH` for `wasm-tools`.

`tests/verified/run.sh --cases frontend` builds and emits the selected module, validates it, and compares its checked cases, including allocation counters.  The full invocation also runs the numerical byte/file proofs and native accuracy checks.  Each module has an entry in the driver and a checked corpus.

`tests/verified/run.sh --cases gpt` tests binary64 GPT with the existing corpus in [`tests/gpt/Cases.lean`](../tests/gpt/Cases.lean) and the release and cache-growth checks of [`tests/gpt/sessions.sh`](../tests/gpt/sessions.sh).  The full invocation includes these application checks.

The cases cover words near 0, `2^32`, `2^63`, and `2^64`, zero divisors, shift amounts of 64 or more, loop counts of 0, 1, and up to 65,537, empty arrays, reads and updates past the end, and floats that are zeros of both signs, infinities, NaN, and the smallest subnormal.  Native Lean returns the canonical NaN for every NaN result, and the host enables Cranelift's NaN canonicalization, so the cases compare float results bit for bit.  The release counts show that a call leaves allocated exactly the result's arrays and the host's arrays at borrowed parameters.  The allocation counts show the updates in place and the growth by doubling: a loop of `n` pushes allocates at most `2 + log₂ (n + 1)` blocks, and an insertion sort of `n` elements at most `3 + log₂ (n + 1)` with the host's array.  One case asks for an array of `2^29` words and must trap.  A recursion case runs `deep`, whose frame has 32 positions, 26 of them live across the self-call, to depth 999, where its deepest frame calls `top1` and `top2`, two functions without the call depth that hold many values live.  The drone's cases include the 116 terrains of [`tests/drone/corpus.txt`](../tests/drone/corpus.txt).

### Accuracy checks

Before the module cases, the driver builds the numerical byte-theorem modules and checks each file-theorem module against the file it emitted.  Each file module proves that its file holds the encoding and decodes to the module of the numerical theorem.  The driver requires both file theorems to report only `propext`, `Classical.choice`, and `Quot.sound`.  The native accuracy checks then compare implementations with integer references over the argument sets stated in each function's document, including the worst inputs of [`WorstCases.lean`](../Verified/Examples/WorstCases.lean).  They also check fused multiply-add, limb arithmetic, and the parser and printer fixtures in `data/strconv/`.

The checks of `Trig`, `Exp`, and `Log` also compare the stored tables with integer references.  `FourierAccuracy.lean` checks impulse and single-frequency transforms, the round trip, Parseval's identity, the power spectrum, and agreement with an exact transform within its stated tolerance.  Each function's document gives its argument sets, measured distances, and proved accuracy bound.

### The full check

The full library includes the numerical proofs and can take several hours.  The lgamma root-range proofs need `--memory-high 10G`, which sets a 12 GiB memory maximum.  The [compilation example](#compiling-and-running) builds only its selected module and imports at the default limits.

After a change to the verified compiler or its examples, `tools/leanrun --memory-high 10G --timeout 12h lake build Verified` must finish with no `sorry` warning, and `tests/verified/run.sh` must pass with no failed case.  A new example needs an import in [`Verified.lean`](../Verified.lean), an entry in the module list of `tests/verified/run.sh`, and checked cases.  An application port reuses its existing corpus.  Other examples add cases to `Verified/Examples/Cases.lean`.  [The LeanExe compiler manual's full check](leanexe-manual.md#the-full-check) covers the rest of the repository, and [the journal](../devnotes.md) records the counts of each run.

## Examples

[The numerical index](../index.md) lists the elementary and special functions, software fused multiply-add, limb arithmetic, decimal parsers and printers, and their numerical and byte theorems.  Each numerical function has a document beside its implementation with the proof modules, exceptional values, and limits.

Each example is a file of [`Verified/Examples/`](../Verified/Examples/) with one `verified_compile` command, of its own definitions or of a program in `Examples/` that it imports, and its `compiled.bytes` states that the module's bytes decode to the module, which computes the example's definitions.  `Tuples.lean` is the exception: it builds its program in the source language without the reflector.  The generators' directories in `Examples/` hold their programs in `Program.lean` and their theorems in `Period.lean` and the files beside it, and [`Examples/Orbit`](../Examples/Orbit/README.md) holds the lemmas about iterates that they share.

| Example | Contents |
|---|---|
| [`Poly`](../Verified/Examples/Poly.lean) | `a * b + c * c - 7`. |
| [`Mix`](../Verified/Examples/Mix.lean) | Division, remainder, the bitwise operations, and the shifts. |
| [`Lets`](../Verified/Examples/Lets.lean) | Four `let` bindings, the last of them inside an operand of `+`, with a division in its body. |
| [`Select`](../Verified/Examples/Select.lean) | `Bool` bindings, `if` on a `Bool` and on `<`, `>`, and `≠`, a `Bool` parameter, and a `Bool` result. |
| [`Pairs`](../Verified/Examples/Pairs.lean) | Pairs as parameters and results, `.1`, `.2`, and `match` on a pair, a pair inside a pair, calls that pass and return pairs, and patterns that take nested pairs apart on the left and on the right, skip a component, keep a pair whole, take apart a pair built in place, and take apart a triple that holds arrays. |
| [`Calls`](../Verified/Examples/Calls.lean) | Four definitions in which `sumSq` calls `sq` and `pick` calls the other three, with a call as an argument of a call and a `Bool`-valued call as the test of an `if`. |
| [Frontend forms](../Verified/Examples/Frontend.lean) | Nested `@[inline]` helpers and `abbrev`s, helper calls in loops and array expressions, listed inline callees, direct in-bounds array methods, and empty arrays of words, floats, and records, including a record without an `Inhabited` instance. |
| [Binary64 GPT-2](../Verified/Examples/Gpt.lean) | The 48 unchanged functions of [the GPT example](../Examples/Gpt/README.md), including full-sequence inference, cached steps, and sampling.  The compiler derives each function's execution, allocation-bound, and trap-free theorems and the module's bytes theorem. |
| [`Loops`](../Verified/Examples/Loops.lean) | Loops over a word, over a pair, and over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose body calls an earlier definition. |
| [`Arrays`](../Verified/Examples/Arrays.lean) | Sums, a dot product, a count, and a search over arrays in loops, reads at computed positions, a pair of arrays passed to calls, and an array chosen by an `if` and bound with `let`. |
| [`Owned`](../Verified/Examples/Owned.lean) | Array results, copies of parameters, owned call results that a reader, a call, a branch, or an unused binding releases, a moved result, a loop whose state is an owned array, a pair of owned arrays taken apart, and arrays built with `LeanExe.build`, one whose element builds and releases an array of its own and one whose element reads an owned array that the code releases after the build. |
| [`Updates`](../Verified/Examples/Updates.lean) | Updates of a parameter, of a built array, of a loop's state, two updates in a row, and an update of an array that stays live. |
| [`Grow`](../Verified/Examples/Grow.lean) | `push` and `++` on parameters, built arrays, and loop states, onto an array that stays live, an array appended to itself, and an owned right operand. |
| [`Modes`](../Verified/Examples/Modes.lean) | Parameters that a function returns, updates, or moves into an owned parameter, also from a loop's state and before a later argument reads the array, and parameters that stay borrowed because the body uses them again.  Its `byHand`, written without the reflector, has an owned parameter that the body never reads and one that it reads last. |
| [`Floats`](../Verified/Examples/Floats.lean) | A piecewise function, a scaled hypotenuse, float comparisons as conditions and as `Bool` values, `min`, `max`, negation, a loop over a pair of floats, a function with a word, a float, an array, and a pair as parameters and a pair result with a float, a call of float functions, the conversions between words and floats, a power of two built from its exponent field, and literal NaN patterns. |
| [`Records`](../Verified/Examples/Records.lean) | Structures with a nested structure and a `Bool` field, built, updated with `{ s with … }`, read field by field, taken apart with `match`, chosen with `if`, passed to calls, and used as a loop's state, with theorems stated for the structures. |
| [`Tuples`](../Verified/Examples/Tuples.lean) | Arrays of tuples of a float and a word and of a nested tuple, built, read along a path, updated in place, extended, and appended, written without the reflector, with an `example` per function stating by `rfl` that it means a Lean function. |
| [`Grids`](../Verified/Examples/Grids.lean) | Arrays of the structures of `Records.lean`, built, read element by element and field by field, also past the end, updated in place in a loop, extended with a new structure, appended, counted, reduced to a total and a `Bool`, and returned in a pair with a total, and a local array of pairs. |
| [`Repeat`](../Verified/Examples/Repeat.lean) | `LeanExe.repeatWhile` over words, a float, pairs that hold arrays, and a structure, stopping early under fuels up to `2 ^ 64 - 1`, with a condition that reads an owned array of the state and a step that updates it in place, and loops over literal data inside a pair result, under a `match`, behind a call with literal arguments, and in a closed term. |
| [`Enums`](../Verified/Examples/Enums.lean) | Four enumerations, flattened by `ctorIdx`, by a `match`, by a constant for the one with a single constructor, and by a `match` to the words 0 and 200, as parameters, results, a structure field, a loop state's field, and array elements, with `match` that has a wildcard binding the value, `match` on an array element, `==`, `!=`, `decide`, and `if` on enumerations, and an update in place. |
| [`Recursion`](../Verified/Examples/Recursion.lean) | Recursion once and twice per call over words, floats, a pair, a structure, an array of structures, and an owned array that each call extends and moves into the next, a function that calls two recursive ones, a recursion that returns at depth 999 and traps at depth 1,000, a recursion that calls another, and `spread`, which calls them inside a loop, a build, a `repeatWhile` condition, a destructured pair, an update, the argument of a function without the call depth, and conditions on a `Bool`, a float, and `≠`, with the theorems `chain_fits`, `chain_trapFree`, `fill_fits`, `fill_cost`, and `fill_trapFree`. |
| [`Fields`](../Verified/Examples/Fields.lean) | Records with array fields, built, read field by field and element by element, also past the end, updated with `{ r with … }` on a borrowed parameter and, in place, in a loop's state, passed to a call, taken apart with `match`, chosen with `if`, returned in a pair, and held in another record, with a `Flat` instance written as a pattern, a loop that extends a field's array, and bound equations that name the fields. |
| [`Trig`](../Verified/Examples/Trig.lean) | `sin` and `cos` ported from fdlibm, with its reduction by multiples of `π/2` below `2 ^ 20 · π/2`, a Payne–Hanek reduction in word arithmetic above, after Go's `math.trigReduce`, which reads the bits of `2/π` and `π/2` from tables so that no call allocates, `sinWith` and `cosWith` with the tables as parameters and `sin` and `cos` as wrappers, with theorems that allow no trap, and fdlibm's minimax kernels, written with the constants' bit patterns. |
| [`Fourier`](../Verified/Examples/Fourier.lean) | The discrete Fourier transform of a signal of interleaved complex floats by the `n²` products of the definition, its inverse, and the power spectrum of real samples, with factors from `Trig.cosWith` and `Trig.sinWith`, compiled in the same program, with Trig's tables passed by the wrappers `dft`, `inverse`, `powerSpectrum`, and `twiddle`. |
| [`Exp`](../Verified/Examples/Exp.lean) | `exp` ported from Arm's optimized-routines, with its table of 256 words in a data segment, `expWith` with the table as a parameter and `exp` as its wrapper, and the paths for results that overflow or underflow. |
| [`Tanh`](../Verified/Examples/Tanh.lean) | `expm1` and `tanh` ported from fdlibm, with fdlibm's signed reduction count represented as a sign and a magnitude. |
| [`Log`](../Verified/Examples/Log.lean) | `log` ported from Arm's optimized-routines, with two tables of 256 words in data segments and `log` as the wrapper that passes them. |
| [`Tables`](../Verified/Examples/Tables.lean) | Two tables read by wrappers, in range and past the end, and an owned array updated and extended from a table, with the theorem `pushSquare_bound` for a wrapper whose callee has a paid parameter. |
| [`Insert`](../Verified/Examples/Insert.lean) | `LeanExe.insertAt` and `LeanExe.eraseAt` on parameters, built arrays, an array that stays live, a loop's state in an insertion sort and in a removal loop, a local array of pairs, and arrays of structures, also past the end. |
| [`Clob`](../Verified/Examples/Clob.lean) | The bid side of an order book, as two arrays of prices and sizes, with insertions and removals of levels in place, a market buy, cancellations, and command streams, and the theorems that a stream run in two chunks gives the book of one run and that `runOut` leaves the book of `runCommands`. |
| [`Drone`](../Verified/Examples/Drone.lean) | The drone planner of [`Examples/Drone`](../Examples/Drone/README.md), compiled unchanged, with its named constants reflected as their values, and the theorems `drone_compute` and `drone_safe`, from the planner's `compute_correct` and `compute_safe`, that the module's results are optimal and safe flights, and `drone_trapFree`, from `compute_bound` on `compiled.compute.bound_eq`, that the module computes `compute` without a trap whenever `top` can rise by 2,251,064 bytes within the memory's cap. |
| [`Elements`](../Verified/Examples/Elements.lean) | A sum, a dot product, and a maximum over arrays of floats, a grid built from converted indices, an `axpy` that updates an owned array of floats in place, an extension, flags of negative elements, a count and a selection by flags, an update and a push of an owned array of `Bool`s, and a sieve of Eratosthenes. |
| [`Lcg`](../Verified/Examples/Lcg.lean), [`ParkMiller`](../Verified/Examples/ParkMiller.lean), [`Xorshift`](../Verified/Examples/Xorshift.lean) | The generators of [`Examples/Lcg`](../Examples/Lcg/README.md), [`Examples/ParkMiller`](../Examples/ParkMiller/README.md), and [`Examples/Xorshift`](../Examples/Xorshift/README.md), compiled unchanged, with the theorems `lcg_advance`, `parkMiller_advance`, and `xorshift_advance`, which combine each module's bytes with the generator's theorems about `advance`, and `lcg_jump` and `xorshift_jump`, which state that the modules' jump-ahead functions compute `advance`, the second when `top` can rise by 36,920 bytes, by `jump_bound`. |
