# LeanExe Manual

This manual describes the `deslop` branch as of 2026-10-05: the Lean dialect that the compiler accepts, the commands that compile and run a program, the theorems a proof establishes and the rules that build them, the tests, and the examples.  Statements about the dialect follow `Project/Compiler/Scalar.lean`, and the quoted error messages are the compiler's.  `deslop.md` records the design, the decisions, and the plan, and `devnotes.md` is the development journal that explains why each part has its present form.

## Overview

### What LeanExe does

LeanExe compiles Lean functions written in a restricted dialect to WebAssembly and proves, for each compiled function, that the bytes compute the Lean function.  The compiler runs during elaboration, reads a definition's unfolding equation, and produces a function of a small intermediate language (IR) together with hints for the prover.  `compile` (`Project/IR/Function.lean`) translates a list of IR functions to a `Wasm.Module` of Talos, a WebAssembly interpreter written in Lean, and `Wasm.Encoding.encode` produces the bytes.  A proof per function establishes `Implements`, and `decode_encode` carries the theorem to the module that the decoder reads back from the bytes.

The compiler is untrusted.  It emits the IR as a Lean definition and the module as `compile` applied to that definition, so a wrong translation makes a proof fail and cannot produce a false theorem.  The project proves the compiler's rules one at a time as lemmas about the compiled code of IR templates, such as `Func.tail_implements` for tail recursion and `Stmt.loop_spec` for `LeanExe.loop`, and each proved rule shortens every later proof that uses it.  The proved rules and the methods that apply them are entries of the LTG knowledge base in `ltg/`.

### What the theorems state

`Implements m k f` (`Project/Pipeline/Implements.lean`) states that entry `k` of module `m` computes `f`.  From any store that satisfies the allocator invariant `Heap.At`, with argument values that represent an input `x`, consumed blocks that are pairwise disjoint and apart from the memory the call reads, and a memory cap of at most 65,535 pages, every run either traps at `unreachable` or returns values that represent `f x` and that the caller owns.  After a return the allocator invariant holds again and the memory's maximum size is unchanged.  Every region of the heap that lay below `top`, outside the free blocks, and apart from the consumed blocks keeps its bytes, remains such a region, and lies apart from the result, so a caller keeps the arrays and trees it holds across a call.

`Implements` allows a trap.  `alloc` traps when memory cannot grow, the array templates trap at 2^29 or more words, and the internal function of a recursive definition traps at depth 1,000.  A module that always trapped would satisfy `Implements`, so a theorem that a call returns uses the abort flag: `ImplementsA false` with a memory budget, which the Euler solvers and the drone planner have (see [Total execution](#total-execution-and-memory-bounds)).

### Trusted base

| Component | Role |
|---|---|
| Lean's kernel, with `propext`, `Classical.choice`, and `Quot.sound` | Checks every proof.  Proofs may not use `bv_decide` or `native_decide`, which add an axiom that trusts compiled code. |
| Talos's semantics (`CodeLib`, revision `87e3aa5e` of `github.com/jsmorph/talos`) | Defines what a module does.  `Triple` and `Implements` are statements about Talos runs, and the IR has no semantics of its own. |
| The binary decoder, `Wasm.Encoding.decode` | Defines what the bytes mean.  `Project/Encoding/DecodeTest.lean` runs it over the official WebAssembly testsuite. |
| The step from a constant to a file | `Project/Pipeline/Emit.lean` evaluates `encode` with compiled Lean code and writes the file.  Only `gpt_file` proves the contents of a file, and it trusts the elaborator `binary_file%`, which reads the file. |

### Outside the proofs

No theorem covers the host, the instantiation of a module, or the I/O around a call.  The total-execution theorems take the allocator state of a fresh instance as a hypothesis, and no theorem connects the interpreter's instantiation of a module to that state.  Talos grows memory whenever the new page count is within the cap, while the WebAssembly specification lets an engine refuse growth, in which case `alloc` traps.

The floating-point theorems describe the WebAssembly deterministic profile, which Talos implements.  `tools/wasmtime-host.c` enables Cranelift's NaN canonicalization to match it, and browsers do not implement the profile.  The accuracy of the Lean definitions `exp` and `tanh` of the GPT example is measured by tests, while the theorems prove only that the compiled code computes those definitions bit for bit.

The tests, the hints, the LTG entries, the Python and JavaScript tools, and the C hosts are unproved.  The comparisons with native Lean test, on concrete inputs, the hosts and engines that the theorems do not cover.  The WGSL path proves its kernels under a device model with strict binary32 arithmetic and race-free dispatch, and a GPU outside that profile falls outside every theorem (see [WGSL kernels](#wgsl-kernels-and-the-browser-pages)).

## The dialect

The dialect is the set of Lean definitions that the compiler translates.  Integers are `UInt64`, so that a Lean program and its WebAssembly compute the same values, wraparound included, and `Nat` is outside the dialect.  Lean's panicking operations, such as `xs[i]!` out of bounds, return `default` in Lean's logic, and the compiled code returns the same value.  The only divergence between Lean and the bytes that `Implements` permits is a trap.

### Definitions the compiler reads

The compiler accepts a `def` whose unfolding equation exists (`getUnfoldEqnFor?`), so a recursive call appears as a call of the definition, whatever form of recursion Lean generated.  The compiler rejects a definition marked `@[implemented_by]` or `@[extern]` (`… has an implementation other than its definition`), and a constant that is not a definition gives `… is not a definition`.  A definition may take no parameters, as the drone's `initial` does.

The compiler unfolds a function marked `@[inline]`, which includes every `abbrev`, at its use when no compiler rule covers the term and the module does not compile the function.  The examples use this for small tests and constants, which stay in the source and out of the call graph: `floorAt` and `best` in `LeanExe/Examples/Drone.lean`, and `finite`, `positive`, and `fifths` in `LeanExe/Examples/Euler.lean`.  The Euler helpers are `abbrev`, reducible as well as inline, because with `@[inline] def` the proofs' `simp` calls unfolded a helper inside a `decide` but not inside its `Decidable` instance (`devnotes.md`, E5).

### Types

| Type | Representation | Notes |
|---|---|---|
| `UInt64` | One `i64` | Arithmetic wraps modulo 2^64, as in Lean. |
| `Float` | One `f64` holding the bit pattern | IEEE binary64, round to nearest even. |
| `Float32` | One `f32` holding the bit pattern | IEEE binary32. |
| `Bool` | One word: 0 for `false`, 1 for `true` | `Bool` is an enumeration. |
| Enumeration | One word, the constructor index | An inductive type without parameters or indices whose constructors have no fields. |
| Structure | Its fields' components in order, one WebAssembly value each | Fields are words, floats, enumerations, or structures and sums of these.  A structure parameter becomes several parameters and a structure result several results. |
| Sum | A tag word, then the components of every constructor's fields in order | Fields of an inactive constructor hold zeros.  A field of a sum is a word, a float, or an enumeration. |
| `α × β` | The components of `α`, then those of `β` | A pair result may contain arrays, lists, and trees, as several results.  A pair parameter has scalar components only. |
| `Array UInt64` | A pointer to an object: a 48-byte header, a length word, and the elements | The header holds the magic number, the count, the capacity, the kind, the element width, and the child mask. |
| `Array Float`, `Array Float32` | An `Array UInt64` of the elements' bit patterns | A binary32 pattern sits in the low 32 bits of its word. |
| `Array α` for a flat `α` | A word array of `n · k` words for `k` components | `α` is a structure, sum, enumeration, or `Bool` whose components are words and floats.  Element `i` occupies words `i · k` to `i · k + k - 1`. |
| `List UInt64` | The null pointer, or a record of two slots: the element and the pointer to the rest | A list parameter is borrowed. |
| A recursive type | The null pointer, or a record of one slot per field | Exactly two constructors, one without fields.  The compiler builds records whose fields are words or values of a recursive type. |

The compiler classifies a type by its structure, so a user type needs no declaration beyond its `inductive` or `structure` to compile.  Inductive types with parameters or indices, nested and mutual inductive types, `Int`, `String`, `Char`, `Option`, and type variables are outside the dialect.  A parameter whose type the compiler cannot classify, such as `Option UInt64`, gives `parameter … of … is not UInt64, Float, Float32, an array, a list of words, or a user type`, and a structure or sum with a field of an unsupported type gives `unsupported type …`.  A `Nat` parameter gives `parameter … of … is a Nat; integers in this dialect are UInt64`, and a `Nat` result gives `the result of … is a Nat; …`.

Arrays of arrays, arrays of trees, and structures with array or tree fields are not supported.  A structure with an array field gives `unsupported type Array UInt64`.  `devnotes.md` records these as the open items E2c and E3.

### Words and Booleans

| Source | Meaning in compiled code |
|---|---|
| `a + b`, `a - b`, `a * b` | Wrapping 64-bit arithmetic. |
| `a / b`, `a % b` | Unsigned division and remainder.  The IR tests the divisor, so `a / 0 = 0` and `a % 0 = a`, as in Lean. |
| `a &&& b`, `a \|\|\| b`, `a ^^^ b`, `a <<< b`, `a >>> b` | Bitwise operations and shifts. |
| Natural-number literals of type `UInt64` | Constants. |
| `min a b` | `if a ≤ b then a else b`, with each operand translated twice, so at the top of a body an operand may not contain a call. |
| `max a b` | Each operand assigned to a local first, then `if a ≤ b then b else a`. |
| `decide p` | 1 when the condition `p` holds, and 0 otherwise. |
| `a == b`, `a != b` | Equality of words, or IEEE equality of floats, as a `Bool`. |
| `a && b`, `a \|\| b` on `Bool`, `!a` | Bitwise and, or, and exclusive or with 1 on the 0-or-1 words.  Both operands are evaluated. |
| An enumeration constructor | Its index. |
| A structure projection, `c.value` | The field's component. |
| `xs[i.toNat]!` | A bounds-checked read (see [Arrays](#arrays)). |
| `xs.size.toUInt64` | The length word, divided by `k` for an array of records of `k` components. |
| `x.toUInt64` for a `Float` `x` | `i64.trunc_sat_f64_u`: NaN and negative values give 0, and values beyond the range give 2^64 - 1, as Lean's `Float.toUInt64`. |
| `x.toBits` for a `Float` `x`, `x.toBits.toUInt64` for a `Float32` `x` | The bit pattern as a word. |

Unary minus on `UInt64` is not covered and gives `unsupported term`, so a program writes `0 - x`.  Ordering comparisons apply to `UInt64` and floats only, so an enumeration or a `Bool` is compared with `=`, `≠`, `==`, or `!=`.  Literals may be decimal or hexadecimal, as the constants of `Prng` are.

A condition is the proposition of an `if` or of `decide`.  The compiler translates `a = b` and `a ≠ b` on words, `Bool`, and enumerations, `<`, `≤`, `>`, and `≥` on `UInt64`, `Float`, and `Float32`, the connectives `∧`, `∨`, and `¬`, a `Bool` `b` (which Lean elaborates as `b = true`), and `a == b`.  The compiler rejects `=` on floats with `unsupported equality type in x = y`, and `x == y` gives the IEEE comparison instead.  In `p ∧ q` and `p ∨ q`, the compiler translates `q` as a branch, so `q` follows the rules of a value-level branch (see [Conditionals](#conditionals-and-case-splits)).

### Floating point

| Operation | `Float` | `Float32` | Compiled form |
|---|---|---|---|
| `+`, `-`, `*`, `/`, `.sqrt` | Yes | Yes | The IEEE operation. |
| `-x` | Yes | Yes | `-0.0 - x`, which is exact and yields the canonical NaN for a NaN, as Lean's negation does. |
| `.abs` | Yes | Yes | `f64.abs` or `f32.abs`. |
| `min`, `max` | Yes | Yes | A comparison by `≤` and a selection, as Lean defines them, with each operand translated twice. |
| `<`, `≤`, `>`, `≥`, `==`, `!=` | Yes | Yes | IEEE comparisons. |
| `if` with a float value | Yes | Yes | A conditional expression. |
| Literals such as `0.5` and `(3 : Float)` | Yes | Yes | The compiler computes the bits, and proofs check them with `decide`. |
| `LeanExe.Float32.nearest` | No | Yes | `f32.nearest`, rounding to the nearest integer, ties to even. |
| `UInt64.toFloat` | Yes | No | `f64.convert_i64_u`. |
| `Float.ofBits w` | Yes | No | `f64.reinterpret_i64`. |
| `Float32.ofBits w.toUInt32` | No | Yes | `f32.reinterpret_i32` of the low word. |
| A match with a float value | Yes | No | A chain of conditional expressions. |
| A fold accumulator | Yes | No | See [Folds](#folds). |
| A loop state, array element, or argument | Yes | Yes | |

Lean 4.34 defines `Float` and `Float32` through `Float.Model` and `Float32.Model`, in which every NaN is the positive quiet NaN `0x7FF8000000000000` or `0x7FC00000`, and Talos's `IEEE64` and `IEEE32` return the same constants.  The compiled forms of negation, absolute value, `min`, and `max` remove the three places where Lean and WebAssembly instructions differ, which `deslop.md` lists under "Floating point".  `Float.ofBits` and `Float32.ofBits` keep a NaN payload in WebAssembly while Lean's model replaces it, so a proof that uses them shows that the argument is not a NaN pattern, as `F64Bits.shiftLeft_52_not_nan` does for `exp`.  Conversions between `Float` and `Float32`, Lean's opaque `Float.exp` and its relatives, and `Float.floor` have no rule.

### Bindings

A `let` or `have` of a word, a float, or a value whose components are all words and floats assigns the value to fresh locals before the body's value, and it may appear wherever a value is translated, inside loop bodies and build elements included.  A `let` of an array may appear only at the top of a function body, from a call or from any array term, and the array is a temporary that the function releases at its end unless the code moves it.  A `let` of a value of a recursive type may likewise appear only at the top of a body, and only from a call.  A `let` whose value is an array or tree variable is that variable.

The value of a `let` may move only the owned values that its body does not use.  The compiler translates the parts of a value so that a later part's statements run before an earlier part's expression, so a later part may not move an array or tree that an earlier part reads (`the value … moves before an earlier part of the same value reads it`).  Binding the read with `let` first orders it.

### Conditionals and case splits

The compiler translates a conditional in one of three ways, according to the type of its value.  A value-level conditional compiles to an IR conditional expression, whose branches are expressions.  A result-level conditional and a conditional on a recursive type compile to an IR `if` statement whose branches run their own statements.

| Kind | Source | Branches may contain | Branches may not contain |
|---|---|---|---|
| Value-level | `if` or `match` on an enumeration or sum, with a word, `Bool`, enumeration, or float value | Expressions, array reads, and `let`s of words, floats, and records | Folds, loops, array sizes, array constructions, and calls.  Inside a loop body or a build element a call of scalars is accepted, and it runs before the conditional on every evaluation. |
| Result-level | `if` or `match` on an enumeration or sum whose value is an array, a pair, a structure, or a sum | Calls, loops, array builds, copies, and updates | `let` of an array or a tree.  Each branch releases the owned parameters that it does not move. |
| Recursive type | `if` whose value is of a recursive type, or `match` on a value of a recursive type | Calls, record allocation, and record reuse | Both branches must move the same owned values and rewrite the same records, and the compiler adds releases to equalize them. |

A match on an enumeration or a sum compiles to a chain of tests of the constructor index, with the last alternative unguarded.  A match on a pair or a structure binds its fields to their components and needs no test.  A `match` on a word with literal patterns elaborates to a dependent `if`, which the compiler rejects (`unsupported term: dite …`), and `if k = 0 then … else …` replaces it.

In the body of a tail-recursive definition, an `if` or a `match` in tail position becomes a statement-level branch of the loop body.  `deslop.md` gives the reason for the restrictions on value-level branches: the compiler never hoists a value's statements out of an `if`, since hoisting a load out of a guarding branch could trap where Lean returns a value.  The calls of scalars that loop bodies and build elements accept are the exception, and a proof covers them through callee theorems that keep the store.

### Calls

A call of a definition compiled into the same module compiles to a `call` statement that runs before the expression that uses its result.  The callee is a definition listed in the same `leanexe_compile` command, the definition itself in a recursive body, or an `@[inline]` definition, which the compiler unfolds instead.  A call must supply every argument (`a call must supply every argument`), and a word, float, or user-type argument becomes the values of its components.

| Position | Calls accepted |
|---|---|
| Top of a function body, result-level branches, top-level `let` values, and arguments | Any call. |
| Branches of a value-level conditional at the top of a body, the right operand of `∧` or `∨`, and fold bodies | None: `a call may not appear in a branch, a fold body, or a recursive definition`. |
| Loop bodies and build elements | Calls whose arguments and results are words and floats.  A loop body may also lend a value of a recursive type to a borrowed position.  The caller's proof needs a callee theorem that states that the call keeps the store, such as `ImplementsPure`. |
| Tail-recursive bodies | None. |
| Bodies of other recursive definitions | Recursive definitions, entered through their internal functions at the caller's depth plus one, and leaves: definitions that call no compiled function and hold at most 24 values in their frame. |

An array argument at a borrowed position must be an array variable.  At an owned position, an owned variable at its last use that no other array argument names moves into the call, any other array term is evaluated into a new array that the call consumes, and a borrowed array or an array that the code uses again is copied (`Stmt.copy`).  Values of recursive types follow the same rules, with copies made by a copy function that the compiler generates for the type.

`leanexe_compile p := [f, g, …]` compiles each definition after the listed definitions it calls, and otherwise in list order, so that each caller knows the owned parameters of its callees.  The compiler finds the calls in a definition's body and in the bodies of the `@[inline]` and reducible definitions that the body uses.  Listed definitions that call each other in a cycle give `the definitions … call each other; a module list may not contain mutual recursion`.  The order of compilation leaves the function indices in list order: the `i`-th listed definition is function `2 + i`.

### Folds

`xs.foldl f init` compiles to a counted loop (`Stmt.fold`) when the element is `UInt64` or `Float` and the accumulator is `UInt64` or `Float`.  The fold must use the default bounds, starting at index 0 and stopping at the size of its array, and it runs over an array variable or an `Array UInt64` literal, which becomes a temporary that the code releases after the fold.  `xs.foldl f init` over a `List UInt64` runs over a list variable or a call that returns a list, which the code releases after the fold.  The body `f acc x` is an expression, so it may not contain calls, folds, loops, or array sizes.

A fold may not appear in a branch of a value-level conditional, a fold or loop body, or a recursive definition, since its statements run before the value that contains it.  A fold over an array of records gives ``a fold over an array of records is written as `LeanExe.loop` over its indices, reading `xs[i.toNat]!` ``, and that loop form is the dialect's only fold over such an array.  `Float32` folds and folds with tuple accumulators are not covered, and `LeanExe.loop` with a tuple state replaces them.

### Loops and builds

The combinators live in `LeanExe/`.  Each has a Lean definition that the theorems use as its meaning and a template whose rule is proved once.  `Project/IR/Loop.lean`, `Build.lean`, `BuildRecord.lean`, `ArrayLoop.lean`, and `RepeatWhile.lean` hold the templates and their rules.

```lean
def LeanExe.loop (n : UInt64) (init : α) (f : UInt64 → α → α) : α :=
  Nat.fold n.toNat (fun i _ state => f (UInt64.ofNat i) state) init

def LeanExe.build (n : UInt64) (f : UInt64 → α) : Array α :=
  Array.ofFn (n := n.toNat) fun i => f (UInt64.ofNat i)

def LeanExe.repeatWhile (fuel : UInt64) (init : α) (cond : α → Bool) (step : α → α) : α :=
  go fuel.toNat init
where
  go : Nat → α → α
    | 0, s => s
    | k + 1, s => if cond s then go k (step s) else s
```

#### `LeanExe.loop`

`LeanExe.loop n init f` applies `f` to the indices 0 to `n - 1` in order and has no early exit.  The loop evaluates the count once, before the first iteration, and its index is a `UInt64`.  The compiler chooses one of three templates by the type of the state.

| State | Template | Requirements |
|---|---|---|
| Words, floats, `Bool`, enumerations, and pairs, structures, and sums of these, a `List UInt64`, or a value of a recursive type | `Stmt.loop` | A tuple state starts from a constructor application of components (`a loop state must be a tuple of components`).  The body returns the next state: a scalar value, a constructor application of the next components, which may include a list cell or a constructor of the recursive type, or one call of a compiled function that returns the tuple. |
| `Array Float` or `Array Float32` | `Stmt.arrayLoop` | The initial state is an array variable, which the loop copies.  The body is one call of a compiled function that returns the next array, and each iteration releases the previous state. |
| A nest of at least two word arrays, `Array UInt64 × Array UInt64 × …` | `Stmt.tupleLoop` | The initial arrays are distinct owned arrays, which move into the loop.  The body is one call of a compiled function that consumes every array of the state. |

A loop body may read arrays, bind `let`s of scalars and records, call functions of scalars, and lend trees to borrowed positions.  It may not contain folds, nested loops, array sizes, or array constructions, so a program binds a size with `let` before the loop and places an inner loop over an array in the element of a `LeanExe.build`, as `matVec` and the drone's `advance` do.  A loop may not appear in a branch of a value-level conditional, a fold or loop body, or a recursive definition.  A build element may contain a loop.

#### `LeanExe.build`

`LeanExe.build n f` makes the array whose element `i` is `f i`.  An element of type `UInt64`, `Float`, or `Float32` is stored as one word through `Stmt.buildWith`, and an element of a flat record type is stored as its `k` component words through `Stmt.buildRecords`.  The element may run loops, folds over array variables, array sizes, and calls of scalars, and it may not allocate, so the compiler rejects an array construction or a fold over an array literal inside it.  The template traps when the array would hold 2^29 or more words, and a build may appear wherever an array construction may (see [Arrays](#arrays)).

#### `LeanExe.repeatWhile`

`LeanExe.repeatWhile fuel init cond step` applies `step` while `cond` holds, at most `fuel` times.  The state is a tuple of words, floats, and arrays, which the compiler keeps in one local per component.  `cond` must compile to an expression over the state with no statements, and `step`, after it takes the state apart, must be one call of a compiled function that consumes every array of the state, with no statements before the call.  The template `Stmt.repeatWhile` allocates and releases nothing, the initial state's arrays move into the loop, and the loop may not appear in a branch, a fold or loop body, a build element, or a recursive definition.

The requirement that the step consume every array shapes the step function.  A compiled function owns an array parameter only when its body moves the array, so a step that builds a new array and drops the old one fails with `the call in a repeatWhile step must consume every array of the state`.  The step of the Euler retry loop, `attempt`, returns either the new grid, releasing the old one, or the old grid, and the drone's `extend` returns its table itself on the final path, which moves it.

### Recursion

A definition whose recursive calls are all in tail position compiles to a `while` loop over a `done` flag (`Func.tail_implements`).  Its parameters are words and values of recursive types, its result is a word, and every value in its body must compile without statements, so the body contains no calls, folds, loops, or array sizes.  `Gcd.gcd` and `Words.sumAcc` are examples.

A definition that calls itself other than in tail position must be compiled in a module list (`… calls itself other than in tail position; compile it in a module list, which adds its internal function`).  The compiler emits an entry function that calls an internal function `f.rec` with a depth parameter, and the internal function traps at `unreachable` at depth 1,000.  Its parameters are words and values of recursive types, its result is a word or a value of a recursive type, and its frame of parameters, locals, and scratch holds at most 24 values, so that the deepest accepted recursion fits Wasmtime's default stack.  A recursive call may appear only at the top of the body or in a branch of a match on a value of a recursive type.  An owned parameter and a temporary must move on every path, since a recursive definition cannot release them yet.

A match on a value of a recursive type tests the pointer against 0, and the record's branch loads the fields into fresh locals.  When the matched value is owned, a constructor of the same type in the record's branch rewrites the record in place and releases the children it drops.  A branch that moves some children without rebuilding the record stores 0 in their slots and releases the record, and a branch that moves none of them leaves the record owned.

### Arrays

| Operation | Element types | Compiled form |
|---|---|---|
| `xs[i.toNat]!` | All arrays | A read that compares the position with the length word and gives 0 past the end, which is Lean's default.  The position must be `i.toNat` for a `UInt64` `i`. |
| `xs[i.toNat]!.field` | Arrays of records | Each component the term needs is read as word `i · k + j`, guarded by `i < 2^29`. |
| `xs.size.toUInt64` | Array variables | A load of the length word, divided by `k` for records.  It may not appear in a branch of a value-level conditional, a fold or loop body, or a recursive definition. |
| `#[a, b, …]` | Word elements, and `#[]` of any element type | An allocation of `48 + 8 (k + 1)` bytes and stores. |
| `LeanExe.build n f` | `UInt64`, `Float`, `Float32`, flat records | See [`LeanExe.build`](#leanexebuild). |
| `xs.set! i.toNat v`, `xs.setIfInBounds i.toNat v` | `UInt64` | In place for an owned array at its last use, and otherwise a copy. |
| `xs.insertIdx! i.toNat v`, `xs.push v` | `UInt64` | In place for an owned array at its last use, moved first to a block of twice the capacity when the block is full, and otherwise a copy. |
| `xs.eraseIdxIfInBounds i.toNat` | `UInt64` | In place for an owned array at its last use, and otherwise a copy. |
| `xs ++ ys` | `UInt64`, `Float`, `Float32` | `xs` must be an owned array parameter at its last use, and `ys` an array variable.  In place when the block has room, and otherwise into a new block. |
| An array variable as a result | All | A move for an owned array, and a copy otherwise. |
| A call that returns an array | All | The caller owns the new array. |

An update may apply to the result of another update, as in `(xs.push a).push b`, and then writes the intermediate array in place.  An update of a borrowed array, or of an array that the code uses again, copies through the copying template, and the lemmas `set!_eq_build`, `insertIdx!_eq_build`, `eraseIdxIfInBounds_eq_build`, and `push_eq_build` equate each operation with that template's result.  `insertIdx!` past the end returns `#[]` in Lean and in the compiled code.

An array construction, meaning a literal, a build, an update, an append, a copy, or an array loop, may appear in a result, in a result-level branch, in a top-level `let`, and in an argument at an owned position.  It may not appear in a branch of a value-level conditional, a fold or loop body, a recursive definition, or a build element.  An `Array Float` literal with elements gives `unsupported term`, and `LeanExe.build 2 fun i => if i == 0 then x else 2.0` builds the same array.  A read of an array of records needs an element type whose `default` has every component 0 (`a read of an array of records needs an element type whose default has every component 0`), because a read past the end yields zero words.

### Records and user types

An enumeration is a word, and a structure or a sum is a tuple of components that the compiler keeps in locals, passes as several arguments, and returns as several results.  A `let` binds a record to locals, a projection reads its component locals, and `{ c with value := v }` elaborates to a constructor application, which the compiler translates part by part.  `Calc` and `Shape` in `LeanExe/Examples` show enumerations, structures, and sums, and `Grids` shows arrays of records.

A recursive type has exactly two constructors, one without fields, which is the null pointer, and one with fields, which is a record with one slot per field and a child mask that marks the slots holding children.  The compiler builds records whose fields are words or values of a recursive type, and a constructor may allocate a record at the top of a body, in a branch of a match or an `if` on values of a recursive type, or as the next state of a loop.  `List UInt64` has the same layout as `Words` in `LeanExe/Examples/Words.lean`, and a list cell may appear only as the next state of a loop.

A value of a recursive type that a call consumes and the code uses again, or that a value holds while it is borrowed, is copied by the copy function `T.copy`, which the module command appends.  Copying needs the module-list form of `leanexe_compile`, the children must have the record's own type, and the copy runs under the same depth limit as recursive definitions.  A copy may appear only at the top of a body or in a branch of a match or an `if` on values of a recursive type.

### Ownership

Every heap object has one owner, so the runtime keeps a count of 1 and has no `retain`.  A parameter of array or recursive type is borrowed or owned.  A borrowed parameter is read and stays the caller's, and an owned parameter is handed over by the caller and moved, updated in place, or released by the function.  Results are new objects that the caller owns, and `Implements` states that they lie apart from every region of the caller's heap outside the consumed blocks.

The compiler infers the modes from the result term.  In a definition without recursion, an array or tree parameter is owned when the result term moves it on some path: by returning it, as the left operand of `++`, as the array of `set!`, `setIfInBounds`, `insertIdx!`, `eraseIdxIfInBounds`, or `push`, at an owned position of a callee compiled earlier, in the initial state of a `LeanExe.loop` over arrays or of a `LeanExe.repeatWhile`, or inside a constructor of a recursive type.  A match on an owned tree moves the tree when its record branch moves a child, and a value at an owned position that another argument also names is copied and does not move.  A list parameter is always borrowed.

A recursive definition that returns a tree owns the parameters of the greatest fixed point of that rule, starting from all tree parameters, except that a parameter that every self-call passes unchanged in its own position and that the body moves nowhere else is borrowed.  A recursive definition that returns a word owns no parameter.  A caller may lend an owned tree to a borrowed position of a callee or of a self-call, and keeps it.

At the end of each path, the compiler releases the owned parameters that the path has not moved and the temporaries that the code has not moved.  A temporary is an array or tree bound by `let` at the top of the body, or a heap component of a call's result that a match takes apart, and a projection of a call's result releases the other heap components right after the call.  In a result-level conditional each branch releases the owned parameters that it does not move, and in a conditional on a recursive type each branch releases the owned values that the other branch moves, so both branches leave the same objects owned.

The theorems state the modes through types.  A consumed argument has type `Moved α` in the function's argument tuple, as in `fillTuple (x : Moved (Array UInt64) × UInt64 × UInt64)` of `Project/Clob/Verify.lean`, and a borrowed argument has its plain type.  A host must not use or release an argument that a call consumed, and it owns every result.

### Restrictions and how to write around them

| Compiler message | Cause | Rewrite |
|---|---|---|
| `a call may not appear in a branch, a fold body, or a recursive definition: …` | A call inside a value-level branch, a fold body, or a tail-recursive body | Bind the call with `let` before the conditional (`let t := twice x; if c = 0 then t else x`), or write the fold as `LeanExe.loop`, whose body may call functions of scalars. |
| `a loop may not appear in a branch, a fold or loop body, or a recursive definition: …` | A loop inside a value-level branch or another loop | Select the count instead of the loop, `LeanExe.loop (if c = 0 then n else 0) …`, or place an inner loop in the element of a `LeanExe.build`. |
| `a fold may not appear in a branch, a fold body, or a recursive definition: …` | A fold inside a value-level branch or a loop body | Bind the fold with `let` at the top of the body. |
| `an array size may not appear in a branch, a fold body, or a recursive definition: …` | `xs.size.toUInt64` inside a loop body or a branch | Bind `let size := xs.size.toUInt64` before the loop. |
| `an array may not be built in a branch, a fold or loop body, or a recursive definition: …` | An array construction inside a value-level context | Build the array in a result-level branch or a top-level `let`. |
| ``an array may not be built in an element of `LeanExe.build`: …`` | Allocation inside a build element | Build the inner array outside and read it. |
| `a call in a loop body or an array element may not take an array: …` | A call that passes an array from a loop body or build element | Place the loop that reads the array in a build element, and give it a helper marked `@[inline]`, as the drone's `best` is. |
| `a call in a loop body or an array element may not return an array: …`, `… must return words and floats: …` | A call there that allocates | Call the function at the top of the body and bind its result. |
| `unsupported equality type in …` | `=` or `≠` on floats or records | Use `==` or `!=` on floats, and compare record fields one at a time. |
| `unsupported term: dite …` | `if h : …` or a `match` on a word with literal patterns | Use `if` with a decidable condition. |
| `unsupported operation Bind.bind in do …` | `for`, `while`, or `do` notation | Use `LeanExe.loop`, `LeanExe.build`, or `LeanExe.repeatWhile`. |
| `unsupported type …` | A structure field or tuple component of an unsupported type, such as an array | Pass arrays as separate parameters and return them in a pair. |
| `parameter … of … is a Nat; integers in this dialect are UInt64`, `the result of … is a Nat; …` | A `Nat` parameter or result | Use `UInt64`. |
| `the definitions … call each other; a module list may not contain mutual recursion` | Listed definitions that call each other in a cycle | Combine them into one recursive definition. |
| `unsupported term: …` | A term no rule covers, such as unary minus on `UInt64`, `Nat` arithmetic, or an `Array Float` literal | Rewrite in covered terms: `0 - x`, `UInt64` arithmetic, or `LeanExe.build`. |
| `a loop state must be a tuple of components: …` | A tuple state that starts from a variable | Write the initial state as a constructor application, such as `(a, b)`. |
| ``a loop over an array must have an `Array Float` state: …`` | `LeanExe.loop` with an `Array UInt64` state | Use a nest of two or more word arrays, or `LeanExe.repeatWhile` with a counter in its state. |
| `the call in a repeatWhile step must consume every array of the state: …` | A step that drops its array argument | Return the array on every path of the step, as the drone's `extend` does. |
| `the condition of a repeatWhile must need no statements: …` | A call or a size in the condition | Compute the needed value in the step and keep it in the state. |
| ``the left operand of `++` must be an array parameter at its last use: …`` | `xs ++ ys` with a borrowed or reused `xs` | Make `xs` an owned parameter that the code does not use afterward. |
| `… calls itself other than in tail position; compile it in a module list, which adds its internal function` | Non-tail recursion in the single form | Compile with `leanexe_compile p := [f]`. |
| `a recursive definition may take only UInt64 and values of recursive types, and return only UInt64 …` | An array, float, or tuple parameter or result in a recursive definition | Use a loop over the array, or a tree. |
| `the internal function of … holds more than 24 values in its frame` | Too many locals live in a recursive body | Move work into a leaf function or reduce the `let`s alive across the recursive calls. |
| `an owned parameter of … must move on every path; releasing it is not supported yet` | A recursive path that drops an owned tree | Return or rebuild the tree on every path. |
| `a read of an array of records needs an element type whose default has every component 0: …` | A record type whose `default` holds a nonzero field | Order the constructors or field defaults so that `default` is all zeros. |
| ``an array may be bound by `let` only at the top of a function body: …`` | A `let` of an array inside a branch | Move the `let` to the top of the body. |
| `the value … moves before an earlier part of the same value reads it` | A later part of a value moves what an earlier part reads | Bind the earlier read with `let`. |
| ``both branches of an `if` must move the same owned values and rewrite the same records: …`` | Branches that consume different trees in a way the compiler cannot equalize | Move or rebuild the same values in both branches. |

### Summary of constructs

| Construct | Supported |
|---|---|
| `UInt64` arithmetic, bitwise operations, shifts, comparisons, `min`, `max` | Yes |
| `Float` and `Float32` arithmetic, `sqrt`, `abs`, negation, comparisons, `min`, `max`, literals | Yes |
| `UInt64.toFloat`, `Float.toUInt64`, `Float.ofBits`, `Float.toBits` | Yes, binary64 |
| `Float32.ofBits w.toUInt32`, `x.toBits.toUInt64`, `LeanExe.Float32.nearest` | Yes, binary32 |
| Conversions between `Float` and `Float32`, `Float.exp` and other opaque functions | No |
| `Bool` values, `decide`, `&&`, `\|\|`, `!`, `==`, `!=` | Yes |
| Enumerations, structures, and sums of words and floats | Yes |
| Recursive types with one constructor without fields and one with fields | Yes |
| `List UInt64` | Yes: borrowed parameters, results, folds, loop states |
| Types with parameters or indices, nested and mutual types, `Option`, `Nat`, `Int`, `String` | No |
| `let` and `have` | Yes, with the placement rules above |
| `if` and `match` | Yes, with the rules of each kind |
| Dependent `if h :`, matches on word literals | No |
| Calls between functions of one module | Yes |
| `@[inline]` and `abbrev` definitions | Yes, inlined |
| Tail recursion | Yes |
| Non-tail recursion over words and recursive types | Yes, in a module list, with a depth limit of 1,000 |
| `Array.foldl` over `Array UInt64` and `Array Float`, `List.foldl` | Yes |
| `LeanExe.loop`, `LeanExe.build`, `LeanExe.repeatWhile` | Yes |
| `for`, `while`, `do` notation, `Id.run` | No |
| Array reads, sizes, literals of words, builds | Yes |
| `set!`, `setIfInBounds`, `insertIdx!`, `eraseIdxIfInBounds`, `push` | Yes, `Array UInt64` |
| `xs ++ ys` | Yes, owned `xs` |
| `Array.map`, `Array.filter`, `Array.extract`, and other array operations | No |
| Arrays of flat records | Yes |
| Arrays of arrays or trees, records with array fields | No |

## Compiling and running

### `leanexe_compile`

`Project/Compiler/Command.lean` defines the command in two forms.  `leanexe_compile p := f` compiles one definition and adds `p.ir`, the IR function, `p.hints`, and `p.module`, defined as `compile [(p.ir, name)]`, where `name` is the last component of `f`'s name and `f` is function 2.  `leanexe_compile p := [f, g, …]` compiles the listed definitions into one module and adds `p.f.ir` and `p.f.hints` for each, `p.funcs`, and `p.module := compile p.funcs`, in which the `i`-th listed definition is function `2 + i`.

The list form also adds the functions that the listed definitions need.  A definition that calls itself other than in tail position gets an internal function `p.f.rec.ir`, exported as `f.rec`, and the internal functions follow the listed ones in list order.  A recursive type that the code copies gets a copy function `p.T.copy.ir`, exported as `T.copy`, after the internal functions in the order of first use.

```lean
import LeanExe.Examples.Clob
import Project.Compiler.Command

namespace Project.Clob

open LeanExe.Examples.Clob in
leanexe_compile clob := [marketBuy, fillLevel, insertLevel, setLevel, addBid, depth,
  findLevel, removeLevel, cancelBid, applyCommand, runCommands, stepCommand, runOut,
  fillTwice, fillKeep]

end Project.Clob
```

Every module has the same layout.  Function 0 is the runtime's `alloc` and function 1 its `release`, both exported, and the module exports the compiled functions by name, the memory as `memory`, and the allocation and free counters as the globals `allocCount` and `freeCount`.  The memory starts at 16 pages with a maximum of 65,535, and the allocator's globals start with `top` at the heap base 4096 and an empty free list.  `alloc` takes the first free block that fits (Knuth's Algorithm A), and `release` inserts a block in address order and merges it with free neighbors (Algorithm B).

The IR and hints are ordinary Lean definitions.  `#eval p.f.ir.body` prints the IR statement of a function, and `p.f.hints` lists, for every IR node, its rule name, its source term, its instruction path in the module, and the names of the locals.  Hints need not be exact: a wrong hint costs proof time and cannot produce a false theorem.

### Emitting and validating bytes

`Project/Pipeline/Emit.lean` evaluates a module constant, encodes it, checks that the decoder reads the bytes back as the same module, and writes the file.  Its arguments are the Lean module that defines the constant, the constant, and the output path, whose directory must exist.  The Lean module must be built first, since `lake env lean --run` loads the existing build of every import.

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 60m lake build Project.Gcd.Module
mkdir -p build/gcd
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Gcd.Module Project.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
```

The convention is `build/NAME/NAME.wasm`, where `NAME` is the name given to `leanexe_compile`, and the module tests read the files there.  The constant is `Project.<Dir>.<name>.module`, defined in `Project.<Dir>.Module`, except for `treeMoves` and `treeFrame`, which `Project.Trees.Moves` and `Project.Trees.Frame` define.  The repository pins `wasm-tools` 1.251.0 in `.wasm-tools-version`, and `tools/check-wasm-tools-version.sh` checks the installed version.

### The Wasmtime host

`tools/download-wasmtime.sh` fetches the C API of Wasmtime 44.0.0, and `tools/build-wasmtime-host.sh` builds `build/tools/leanexe-wasmtime-host` from `tools/wasmtime-host.c`.  On an ARM Mac, `tools/bootstrap-macos.sh` installs the pinned tools in repository-local paths.  The host enables Cranelift's NaN canonicalization so that float results follow the deterministic profile.

```sh
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
build/tools/leanexe-wasmtime-host call-stats build/sumCount/sumCount.wasm sumCount array-u64 \
  array-u64:1,2,3
build/tools/leanexe-wasmtime-host call build/clob/clob.wasm insertLevel \
  list:array-u64,array-u64 array-u64:105,101 array-u64:4,6 i64:1 i64:103 i64:5
```

The form is `call MODULE.wasm FUNCTION RESULT-KIND ARG …`.  The first command prints `6`, the second prints `[6, 3]` and `stats 2 0`, the allocation and free counters after the call, and the third prints `[105, 103, 101]` and `[4, 5, 6]` on separate lines.  A structure, sum, or pair argument is passed as one argument per component.

| Argument | Meaning |
|---|---|
| `i64:N` | A word. |
| `f64:BITS`, `f32:BITS` | A float given by its bit pattern as a decimal word. |
| `array-u64:N,N,…` | An `Array UInt64` that the host allocates through `alloc`.  `array-u64:` is the empty array, and a float array passes the elements' bit patterns. |
| `file-u64:PATH` | An `Array UInt64` read from a file of little-endian words. |
| `chain-u64:N,N,…` | A `List UInt64` as a chain of records. |
| `tree-u64:K,L,R` | A tree of the `KeyTree` layout in preorder, with `.` for a leaf, such as `tree-u64:5,3,.,.,.`. |
| `bytes:HEX`, `bytes-file:PATH` | A byte object, passed as a pointer and a length. |

| Result kind | Output |
|---|---|
| `i64`, `f64`, `f32` | One decimal word, the bit pattern for floats. |
| `array-u64` | The elements, as `[a, b, …]`. |
| `chain-u64`, `tree-u64` | The list as `[a, b, …]`, or the tree in the preorder form of its argument, after the host checks each record's header. |
| `file-u64:PATH` | The array, written to a file. |
| `list:K1,K2,…` | Several results, one line each. |
| `slots:N` | `N` words on one line. |
| `bytes` | Two results, a pointer and a length, printed as the bytes in hexadecimal. |

`session MODULE.wasm` reads commands from standard input, one per line, and keeps the instance between calls, which the GPT-2 generation and the memory tests use.  `script` mode reads the same commands and allows one call.  A value in a command is a decimal word, `result:K` for result `K` of the last call, or `u64:V` for a variable that `read-u64` set.

| Command | Effect |
|---|---|
| `alloc ID SIZE`, `bytes ID HEX`, `bytes-file ID PATH`, `file-u64 ID PATH` | Allocate an object and name its pointer `ID`. |
| `write-u64 ID OFFSET VALUE`, `write-ptr ID OFFSET ID2`, `write-bytes ID OFFSET HEX` | Write into an object. |
| `arg-u64 VALUE`, `arg-ptr ID`, `arg-f64 BITS` | Push an argument for the next call. |
| `call FUNCTION NRESULTS` | Call an export and print `results r0 r1 …`. |
| `keep ID VALUE` | Name a value, such as a returned pointer, `ID`. |
| `save-u64 VALUE PATH` | Write the array at a pointer to a file. |
| `read-u64 V PTR OFFSET`, `read-memory PTR LEN` | Read memory after a call. |
| `stats`, `memory-size`, `done` | Print the counters, print the memory size, or stop. |

A host releases an object it owns by calling the export `release` with the pointer.  `release` traps when the header lacks the magic number or the count is not 1, so a second release of one pointer traps.  The host also has test commands for the allocator (`release-reuse`, `free-alias`, `temp-byte-call`, `temp-array-call`, `noarg-temp-reuse`, and `allocator-grows`), which `tools/wasmtime-host.c` documents.

### Native runs and tools

A Lean file with a `main` runs natively with `tools/leanrun --timeout 10m lake env lean --run FILE ARGS`, which is how the test-case generators produce their expected results.  `tools/leanrun --timeout 60m lake build euler-native` builds `Project/Euler/Native.lean`, which runs either Euler solver natively and writes its output words, and `uv run tools/euler-run.py WASM first|reconstructed N OUTDIR` runs one solve export in the Wasmtime host and records its runtime, peak resident size, and the SHA-256 of its words.  `uv run tools/gpt2.py --output-tokens 32 --prompt "…"` generates text with `gpt.wasm`, greedily or with `--top-k`, `--temperature`, and `--seed`, from the weight files that `tests/gpt/gpt2_compare.py` writes.

### WGSL kernels and the browser pages

Iteration 24 added a GPU path for binary32 kernels.  `Project/WGSL/` defines a WGSL subset with a printer, a parser proved to invert it, a semantics, and a proved translation of IR builds into kernels, and `Project/Gpt32/` proves GPT-2's binary32 kernels and the host program of a generation step (`generate_host`), under a device model with strict binary32 arithmetic, race-free dispatch, and no dynamic errors.  `Project/WGSL/Emit.lean` prints a kernel after checking that the parser reads the text back as the kernel, and `tools/build-webgpu-host.sh`, after `tools/download-wgpu-native.sh`, builds `build/tools/leanexe-webgpu-host`.

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/.  The kernel page runs the WGSL kernel cases on the browser's WebGPU and compares every word with native Lean's, and the GPT-2 page runs GPT-2 124M in binary32 with its kernels on WebGPU, in `gpt32.wasm`, or on both with their scores compared.  The GPT-2 page needs the weights that `uv run tests/gpt32/generate.py --export` writes, and `tests/web/README.md` describes the setup, the controls, and what is proved about the pages.

## Proving

### The `Implements` family

| Predicate | Statement |
|---|---|
| `Runs aborts env m k store args P` | Every run of entry `k` with enough fuel returns values satisfying `P` or, when `aborts`, traps at `unreachable`.  `ReturnsOrAborts` is `Runs true`. |
| `TripleA aborts m s scratch P R` | From any store and IR state satisfying `P`, the compiled code of statement `s` ends in a store and state satisfying `R` or, when `aborts`, traps.  `Triple` is `TripleA true`. |
| `Implements m k f` | The statement of the [overview](#what-the-theorems-state), with a trap allowed. |
| `ImplementsPureA aborts m k f` | For scalar arguments and results: from any store, the call returns the values of `f x` and leaves the store unchanged, or traps when `aborts`.  `ImplementsPure` is the `true` case, and `ImplementsPure.implements` derives `Implements`. |
| `ImplementsA aborts m k f Pre Post` | `Implements` with the abort flag, a precondition `Pre x heap store`, and a postcondition `Post x heap store heap' final`.  `ImplementsA.implements_of` derives `Implements` from `ImplementsA true` when `Pre` always holds. |
| `Satisfies m k P Q` | For inputs satisfying `P`, the call traps or returns an owned `y` with `Q x y`.  `Implements.transfer` derives it from `Implements` and `∀ x, P x → Q x (f x)`. |

A function's theorem takes its parameters as one tuple in declaration order, such as `gcdTuple (x : UInt64 × UInt64)` in `Project/Gcd/Verify.lean`, and the entry index is the function's position in the module.  The arguments are reversed in `Runs` because Talos lists them with the top of the stack first.  The examples define each tuple function beside its theorem, such as `fillTuple` for `fillLevel` in `Project/Clob/Verify.lean`.

### Representations

`Represent α` says how a value appears to a compiled function: its WebAssembly values, the heap data they point to when borrowed and when owned, the blocks its owned objects occupy, the regions a call reads, and the pointers a call consumes.  `Scalar` covers values without heap data: `UInt64`, `Float`, `Float32`, `Unit` for a function without parameters, pairs, and any type with a `Flat α β` instance, which represents `α` as the scalar `β`.  `Bool` has the instance `cond b 1 0` built in, and a user enumeration, structure, or sum needs its own `Flat` instance, such as `Flat Calc (UInt64 × UInt64 × Op)` in `Project/Calc/Flat.lean`.  The instances are part of what the theorem states.

Arrays have instances for `Array UInt64`, `Array Float`, `Array Float32`, and `Array α` for a flat `α`, which is stored as `flatWords xs`.  A type with an `Encode` instance is represented by the records that `encode` gives, a `Node` tree of words and children, and `List UInt64` has one built in.  A user recursive type needs an `Encode` instance, and some rules also need `EncodeSlotted`, as in `Project/Words/Encode.lean`.  `Moved α` represents a consumed argument for `Array UInt64`, `Array Float`, arrays of records, and types with `Encode`.

### Structure of a proof

A proof starts from the rule that matches the function's body.  The rules for bodies without recursion take the module's function list, the function's index and IR, a lookup proved by `rfl`, the Lean function, and an arity lemma, and they leave one obligation: a `TripleA` for the body from the function's initial state.  Its postcondition says that the result expressions evaluate to values that represent `f x`, and for a body that allocates, that some heap satisfies `Heap.At`, the memory caps are unchanged, and `Heap.Keeps` holds.  Each rule has an `A` form with the abort flag and `Pre` and `Post`.

| Rule | Body |
|---|---|
| `Func.implements` | Keeps the store, with scalar results. |
| `Func.implementsPure` | Keeps the store, with scalar arguments and results, giving `ImplementsPure`. |
| `Func.implements_heap` | May allocate and release, and consumes nothing. |
| `Func.implements_moves` | Consumes `Moved` arguments. |
| `Func.tail_implements`, `Func.tailIn_implements` | A tail-recursive loop.  The obligation `TailStep` (or `TailStepIn` for tree parameters) covers one iteration with a decreasing measure. |
| `Func.recursion`, `Func.entry_implements` | Non-tail recursion through the internal function, by strong induction on a measure, with `Stmt.selfCall_spec` for the calls. |
| `Func.rebuildRecursion`, `Func.implements_rebuilt`, `Func.entry_rebuilds` | Non-tail recursion that consumes a tree, with `Stmt.selfCall_rebuilds`. |

The body's triple follows the IR.  `Project/IR/Stmt.lean` gives one rule per statement (`Stmt.assign_spec`, `seq_spec`, `ite_spec`, `while_spec`, `load_spec`, `store_spec`, `call_spec`, `abort_spec`), with `TripleA.mono` and `TripleA.of_forall` to adjust conditions.  Straight-line code is computed rather than stepped: `Stmt.run` gives the effect of call-free statements, `Stmt.run_spec` and `Stmt.run_triple` turn it into a triple, `Stmt.seq_run` continues after a statement, and `Stmt.seq_callPure` continues after a call whose callee has an `ImplementsPure` theorem.  The proofs of the Euler and drone kernels work this way, assignment by assignment with one `simp` call each.

| Template | Rule |
|---|---|
| Fold, size, literal, release | `Stmt.fold_spec`, `Stmt.listFold_spec`, `Stmt.arraySize_spec`, `Stmt.arrayLiteral_spec`, `Stmt.release_spec`, `Stmt.releaseNode_spec` |
| Reads | `Expr.read_spec`, `Expr.readValue_at`, `getElem!_map_toBits` for float arrays, `Expr.readValue_record` and `flatWords_read` for records |
| `LeanExe.loop` with a scalar state | `Stmt.loop_spec`, whose obligation is one iteration of the body on states described by `State.Holds` |
| `LeanExe.build` | `Stmt.buildWith_spec`, `Stmt.build_spec`, `Stmt.buildRecords_spec` |
| Copies and updates | `Stmt.copy_spec`, `Stmt.pushBuild_spec`, `Stmt.setInPlace_spec`, `Stmt.insertInPlace_spec`, `Stmt.eraseInPlace_spec`, `Stmt.pushInPlace_spec`, `Stmt.append_spec` |
| Records of recursive types | `Stmt.record_spec` |
| Calls | `Stmt.callImplements_spec`, `Stmt.callPure_spec`, `Stmt.callKeeps_spec` |
| `LeanExe.repeatWhile` | `Stmt.repeatWhile_spec`, `Stmt.repeatWhile_pure_spec` for a step that keeps the store |

A body that calls allocating functions and releases temporaries is proved under `Live` (`Project/IR/Live.lean`), an invariant that records the allocator invariant, the unchanged caps, the frame of the caller's heap, and the live temporaries, each owned and apart from the others.  `Live.start` begins a body, `Live.call`, `Live.call_seq`, `Live.callMove`, and `Live.callScalar_seq` run calls, `Live.callOne` and `Live.callOne_seq` run a call whose result is scalars followed by one array (`OneArray`), and `Live.releaseFirst`, `Live.releaseSecond`, and `Live.releaseAt` release temporaries.  `Live.arrayLoop`, `Live.tupleLoop`, and `Live.repeatWhileOne` cover the loops over arrays, and `Live.finish`, `Live.finish_moved`, and `Live.finish_results_one` give the rule's postcondition.  `tools/gpt_composites.py` generates the GPT composites' proofs in `Project/Gpt/Composites.lean` from a description of each function's calls.

Two files hold lemmas that recur across programs.  `Project/IR/Combinators.lean` states facts about the combinators' Lean definitions: `loop_induction` carries an invariant through `LeanExe.loop`, `loop_congr` equates loops whose steps agree, and `build_size`, `build_get`, and `build_get_out` give the size and the elements of `LeanExe.build`.  `Project/IR/Words.lean` holds lemmas about the words that the compiler computes from tests, such as `word_and` and `word_or` for `&&` and `||` on 0-or-1 words and `divU_eq` and `remU_eq` for the IR's tested division, and the tactics `eval_body` and `eval_state`, which evaluate a compiled body or a run of statements with one `simp` call.

Floats enter through equality theorems: ProofKit proves that Lean's binary64 and binary32 operations equal Talos's `IEEE64` and `IEEE32` functions on bit patterns for all inputs, and `F64Bits.toBits_add` and its siblings state them as `simp` lemmas.  Large proofs close float literals with bit lemmas proved by `decide +kernel`, as in `Project/Euler/Words.lean`.  `devnotes.md` (E6) records the proof patterns that keep symbolic evaluation of large bodies tractable, such as computing every value in straight-line code and selecting the result once at the end.

### The bytes theorem

`Wasm.Encoding.round_trip m locals ok` gives `∃ bytes, encode m = .ok bytes ∧ decode bytes = .ok m` from a bound on each function's locals and the evaluation of the encoder to success.  The first premise holds by `decide`, and the second by `decide +kernel`, which evaluates the encoder in the kernel.  A program's bytes theorem combines it with the `Implements` theorems, as `gcd_bytes` does.

```lean
theorem gcd_bytes : ∃ bytes, Wasm.Encoding.encode gcd.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 gcdTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip gcd.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, gcd.module, decoded, gcd_implements⟩
```

`decide +kernel` adds no axiom and takes about half a second per module.  Every compiled module has a bytes theorem named `NAME_bytes` except `treeFrame`, a module for the depth test only, and `gpt32`, whose kernels have WGSL theorems and no WebAssembly theorem.  `gcd_bytes`, `clob_bytes`, `euler_bytes`, and `drone_bytes` are typical.  `gpt_file` in `Project/Gpt/File.lean`, checked with `lake env lean` after `Emit.lean` writes `build/gpt/gpt.wasm`, proves that the file holds `encode gpt.module`.

### Source-level theorems

A property of the Lean function reaches the bytes through `Implements`: `Implements.transfer` turns a proof of `∀ x, P x → Q x (f x)` into `Satisfies`, and a bytes theorem may conjoin the property directly.  The source theorems are ordinary Lean proofs about the definitions in `LeanExe/Examples`, with no reference to WebAssembly.  The examples carry several.

| Theorem | Statement |
|---|---|
| `euler_solve`, `euler_reconstructed_solve` | The bytes decode to a module whose solve exports compute `solve` and `reconstructedSolve`, and output words whose first word is 0 are those of a successful run: `n` from 2 to 800, time 0.8, and `n²` admissible cells. |
| `solve_hyperbolic`, `reconstructedSolve_hyperbolic`, `reconstructedRun_steps`, `run_balance`, `reconstructedRun_balance` | Hyperbolicity of the final states, the CFL bound of accepted steps in exact arithmetic, and conservation with rounding residuals bounded from the run's words. |
| `drone_compute` | The bytes compute `compute`, whose output for valid terrain encodes an admitted flight of least cost (`compute_correct`) and is `#[]` for invalid terrain. |
| `drone_safe` | The flight of every valid nonempty terrain is safe in continuous time (`WholeFlight.compute_safe`). |
| `forward_prefix`, `steps_exact` | Row `i` of GPT's `forward` depends only on tokens 0 to `i`, and the cached `step` and `scores` give `forward`'s rows bit for bit. |

### Total execution and memory bounds

`ImplementsA false` excludes the trap, so it states that the call returns.  The allocation rules (`alloc_spec_runs`, `Stmt.buildWith_specA`, `Stmt.buildRecords_specA`, `Stmt.arrayLiteral_specA`) take a room premise only when the flag is `false`, and their postconditions name the exact heap after the allocation.  A function proved generically in the flag has one proof that yields both the trap-tolerant theorem and the total one, and the old theorem is the `true` case.

The budget counts blocks of a fixed size `g` (`Project/Pipeline/Budget.lean`).  `units g free` is the number of blocks of `g` payload bytes, with their 48-byte headers, that the free list can supply by splitting, a number that merging cannot decrease.  `Heap.Budget heap g spare limit` states `top + (spare - units g free) · (g + 48) ≤ limit`, so an allocation of at most `g` bytes consumes one spare and a release of a block of at least `g` bytes returns one.  `Heap.Bounded heap store m g spare pages` adds that memory has at most `pages` pages and that the cap allows them, with the limit `pages · 65536`.

An allocating function's total theorem states its use of the budget in spare counts: under `a = false`, if the heap is bounded with `spare + k` spares before the call, it is bounded with `spare + k - d` spares after.  The Euler theorems fix the grid's byte count through `GridBytes cells g` and leave `spare` and `pages` free, so a caller applies them inside its own budget.  Both conditions are vacuous when `a = true`, and `ImplementsA.implements_of` then gives `Implements`.

```lean
theorem sweep_implementsA {a : Bool} {cells : Nat} {g : UInt64} (hg : GridBytes cells g)
    (spare pages : Nat) :
    ImplementsA a euler.module 11 sweepTuple
      (fun x heap store => a = false → x.2.2.2.size = cells ∧
        heap.Bounded store euler.module g (spare + 1) pages)
      (fun _ _ _ heap' final => a = false → heap'.Bounded final euler.module g spare pages)
```

| Euler functions | `k` | `d` |
|---|---:|---:|
| `sweep`, `reconstructedSweep`, `initialCells`, `pack` | 1 | 1 |
| `finishStep`, `reconstructedFinish` | 1 | 0 |
| `step`, `reconstructedStepGrid` | 2 | 1 |
| `tryStep`, `attempt`, `advanceWith`, `advanceStep`, and their reconstructed counterparts | 2 | 0 |
| `runFrom`, `run`, and their reconstructed counterparts | 3 | 1 |
| `solve`, `reconstructedSolve` | 3 | 2 |

`euler_solve_total` in `Project/Euler/Total.lean` applies these theorems with `spare = 0`.  From the allocator state of a fresh instance (`top` at 4096, no free block, 16 pages) and a memory cap of at least 1,407 pages, both solve exports return the words of the Lean functions without a trap and end with at most 1,407 pages (88 MiB): the heap base and three grids of 800 × 800 cells with their headers, rounded up to pages.  The fresh state is a hypothesis, since no theorem connects instantiation to it.

`drone_compute_total` in `Project/Drone/Total.lean` counts blocks of `tableBytes`, 69,128 bytes, which bounds every allocation of the planner.  The forward loop uses a different number of spares at each step, so `extend`'s theorem quantifies its budget, and the loop invariant holds `spare + (count - i)` spares at station `i`.  From an allocator with no free block and `top` at most 8192, below which the host has placed the terrain, and a cap of at least 70 pages, `compute` returns its words without a trap and ends with at most 70 pages (4.375 MiB).

### LTG entries

`ltg/entries/` holds 37 entries, each a directory with an `entry.json` and a `README.md`.  `entry.json` names the modules, declarations, premises, and result of a rule or method, and its `annotationKinds` list the hint rules that select it, such as `repeat while` or `tail-recursion-loop`.  A prover finds an entry by searching for a hint's rule name or for a declaration, and the README explains how to apply the entry, with the consumers that serve as worked examples.

`Project/LTG/Check.lean` imports every module the entries list and reports each listed declaration that does not exist, so a renamed declaration fails the check until its entry changes.  A new rule lemma gets an entry when it is proved.  An entry that is narrow or specific to one program stays as a worked example unless it is invalid, stale, unsafe to disclose to a measured proof task, or a duplicate without a distinct lesson, as `AGENTS.md` requires.

```sh
tools/leanrun --timeout 10m lake env lean --run Project/LTG/Check.lean ltg/entries
```

### Axiom checks

A theorem may depend only on `propext`, `Classical.choice`, and `Quot.sound`.  The check is a Lean file outside the repository that imports a program's `Verify` module and prints the axioms of its theorems, run through `tools/leanrun`.  Any further axiom, such as `sorryAx` from an incomplete proof or the axiom that `native_decide` adds, is a failure.

```lean
import Project.Gcd.Verify
#print axioms Project.Gcd.gcd_bytes
```

```text
'Project.Gcd.gcd_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Testing

### Module tests

`tests/modules/Cases.lean` computes test cases with native Lean for every module other than `gpt`, `gpt32`, and `prng`, one line each: the module, the export, the result kind, the host arguments, and the expected result.  `tests/modules/run.sh` runs each case in the Wasmtime host on `build/MODULE/MODULE.wasm` and compares the output.  The cases include special floats, indices at and past the ends of arrays, and values that wrap.

The same script checks the allocation counters.  The release-count cases call CLOB, list, and tree functions through `call-stats` and compare the allocations and frees with the counts that ownership predicts, such as in-place updates that allocate nothing and consumed trees whose records are freed.  The depth-guard cases call recursive functions, the 24-value frame of `treeFrame`, and the copy function on chains of 999 and 1,000 nodes, and they check that the first call returns and the second traps at `unreachable`.

```sh
tests/modules/run.sh
uv run tests/modules/chunks.py
```

`tests/modules/chunks.py` runs a stream of CLOB commands three ways in host sessions, through `runCommands`, through calls over chunks, and one command at a time, and checks that the books agree.  Whether an insert or an append grows its array depends on the capacity that the allocator gave its block, which differs between sessions, so the script checks that exactly the results and the command arrays stay allocated.  It does the same for `runOut` and `stepCommand`, which also append the best bid after each command to an output array.

### Other comparisons

| Command | Comparison |
|---|---|
| `tests/gpt/run.sh` | Every export of `gpt.wasm` against native Lean on the cases of `tests/gpt/Cases.lean`. |
| `tests/gpt/sessions.sh` | Sessions that call each GPT function with arrays, release everything, and check that every allocation was freed. |
| `uv run tests/gpt/hf_compare.py`, `uv run tests/gpt/gpt2_compare.py` | GPT's `forward` against Hugging Face's model in float64, on random weights and on the GPT-2 124M weights. |
| `uv run tests/gpt/sample_frequencies.py` | Top-k sampling frequencies against their probabilities. |
| `uv run tests/prng/compare.py` | `prng.wasm` against the reference SplitMix64. |
| `tests/drone/run.sh` | `drone.wasm` against the results of main's planner, run natively by `tests/drone/oracle.sh`, on 1,975 calls and 116 terrains. |
| `uv run tools/euler-run.py …` | One Euler solve, with the SHA-256 of its words, which the data READMEs compare with main's. |

`data/euler-riemann-complete-v1/README.md` and `data/euler-reconstructed-v1/README.md` describe this branch's Euler binary, its theorems, and its runs on the 192 and 800 grids.  The output words of every run equal main's, with the same SHA-256.  The READMEs also list the results of main that this branch does not prove, such as the reconstruction accuracy theorems.  `data/drone/README.md` describes the drone planner's program, theorems, and tests in the same way.

### WGSL tests

`tests/wgsl/run.sh` emits the seventeen kernels with `Project/WGSL/Emit.lean`, computes the cases of `tests/wgsl/Cases.lean` with native Lean, and runs every case on the SwiftShader and llvmpipe Vulkan drivers with `leanexe-webgpu-host`, comparing each output word.  `tests/gpt32/native.sh` runs small random GPT-2 models through the Lean driver of `Project/Gpt32/Generate.lean` on both drivers and compares each step's scores with native Lean's `step32`.  `uv run tests/gpt32/generate.py` generates text with GPT-2 124M on the kernels and compares each step with Hugging Face's float32 model.

### The full check

`devnotes.md` records a full check after each change to the compiler or the pipeline, with the counts of the cases that passed.  The build comes first, and the byte comparison and the tests follow it.  An earlier order emitted the modules before the build, so it compared stale bytes and hid compiler changes.

1. `tools/leanrun --timeout 60m lake build`, with no `sorry` warning.
2. Emit every module with `Emit.lean` into a scratch directory and compare its bytes with `build/NAME/NAME.wasm`.  A module whose source did not change must have the same bytes, and a changed module's new file replaces the old one before the tests.
3. `tests/modules/run.sh`, with the module cases, the release counts, and the depth guard, and `uv run tests/modules/chunks.py`.
4. `tests/drone/run.sh`, and `tests/gpt/run.sh` and `tests/gpt/sessions.sh` when the GPT module changed.
5. The LTG check.
6. `tests/wgsl/run.sh` on both Vulkan drivers.

The decoder test, `tools/leanrun --timeout 60m lake env lean --run Project/Encoding/DecodeTest.lean "$(command -v wasm-tools)" build/decode-test`, runs the decoder over the WebAssembly testsuite: each valid module in the supported subset must decode to the reference module and round-trip, and each malformed module must be rejected.  It expects `build/decode-test` to hold the `wasm-tools json-from-wast` output of the testsuite scripts in the CodeLib checkout.  `Project/Encoding/README.md` describes the encoder's theorems and the review of its specification against the published WebAssembly rules.

## Worked examples

The program of an example is `LeanExe/Examples/<Name>.lean`, and its module and proofs are in `Project/<Name>/`, where `Module.lean` usually holds `leanexe_compile` and `Verify.lean` the theorems.  Larger examples split their proofs over more files, such as `Total.lean` in `Project/Euler` and `Project/Drone` for complete execution.  The module column gives the name that `leanexe_compile` assigns, which the tests use.

| Example | Module | Demonstrates |
|---|---|---|
| `Scale` | `scale` | Word arithmetic and Lean's division by zero, proved with `Func.implements` and one `simp` call. |
| `Gcd` | `gcd` | Tail recursion as a loop, proved with `Func.tail_implements` and a one-iteration obligation. |
| `SumArray` | `sumArray` | A fold over a borrowed array, proved with `Stmt.fold_spec`. |
| `PairSum` | `pairSum` | An array literal as a temporary released after its fold, proved with `Func.implements_heap`. |
| `SumCount` | `sumCount` | An array result that the caller owns, and the array size. |
| `Axpy`, `ScaledHypot`, `Piecewise` | `axpy`, `scaledHypot`, `piecewise` | Binary64 arithmetic, square root, comparisons, `==`, negation, `abs`, `min`, `max`, and nested `if`. |
| `SumSquares`, `Mean`, `Bucket` | `sumSquares`, `mean`, `bucket` | Folds over `Array Float` and the conversions between `UInt64` and `Float`. |
| `Prng` | `prng` | SplitMix64 with a pair result, and `ImplementsPure` theorems that hold in any module containing the functions. |
| `Bools` | `bools` | `Bool` parameters, results, record fields, and loop states. |
| `Calc`, `Shape` | `calculator`, `shapes` | Enumerations, structures, and sums, with their `Flat` instances, and a loop whose state is a structure. |
| `Lists`, `Words` | `lists`, `words` | `List UInt64` and a user list type: folds, matches, tail recursion over records, and loops that build lists. |
| `Trees` | `trees`, `treeMoves`, `treeFrame` | Non-tail recursion with the depth guard, record reuse, moves, copies, lending, and pair results with trees. |
| `Updates` | `updates` | Chains of in-place updates and a `push` that copies a borrowed array. |
| `Clob` | `clob` | Loops over arrays, `set!`, `insertIdx!`, `eraseIdxIfInBounds`, calls with `Moved` arguments, pair results, a loop over two arrays, and a `push` in place. |
| `Grids` | `grids` | Reads, sizes, builds, and loops over arrays of records. |
| `Binary32` | `binary32` | `Float32` scalars, arrays, comparisons, and conditionals, and kernels translated to WGSL. |
| `Gpt` | `gpt` | GPT-2 in binary64: calls of `ImplementsPure` functions in loops, temporaries under `Live`, a loop over layers with an array state, `++` in place, the cached step, top-k sampling, and the causal and exactness theorems. |
| `Gpt32` | `gpt32` | GPT-2 in binary32 on WGSL, with the theorem of the host program. |
| `Euler`, `EulerReconstructed` | `euler` | Arrays of records, `repeatWhile` with moved grids, `ImplementsA` budgets, complete execution within 1,407 pages, and the admissibility, CFL, balance, and hyperbolicity theorems. |
| `Drone` | `drone` | `UInt64` throughout, loops inside build elements, `@[inline]` helpers, `repeatWhile` with a status, optimality and flight safety, and complete execution within 70 pages. |

## Development practice

### `tools/leanrun` and the single Lean slot

Every `lean` and `lake` command runs through `tools/leanrun`, as `AGENTS.md` requires.  The runner limits memory and CPU through a systemd user scope, sets `LEAN_NUM_THREADS=1`, and takes a machine-wide lock, so the machine runs one Lean process at a time and other sessions wait for the slot.  `--timeout` sets the command's limit and `--lock-timeout` the seconds to wait for the lock, 900 by default.

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 30m --lock-timeout 1200 lake env lean FILE
```

After a target reaches its timeout without a diagnostic, `AGENTS.md` requires dividing it, or adding a reusable lemma that reduces its elaboration, before running it again.  `LEANRUN_LOCAL=1` runs without the cgroup limits and only with the user's explicit authorization.  `tools/leanrun-dev` runs Lean on the remote development machine (`sync`, `check`, or a command).

`lake env lean FILE` loads the existing build of each import without rebuilding it, so a check of a file whose imports changed must follow `lake build` of those imports.  `lake build` of a target rebuilds its imports from source.  `devnotes.md` (D1) records a case in which stale builds of main's drone proofs, with the same module names, made such a check use main's theorems.

### Procedures

`AGENTS.md` sets the procedures that bind agents in this repository: the runner and its limits, the approval boundaries for repository drivers, and the handling of LTG entries.  `CLAUDE.md` sets the style of prose, comments, and commit messages.  Python tools carry their dependencies as PEP 723 metadata and run with `uv run`.

`deslop.md` records the design, the decisions with their reasons, what is proved and tested, and the plan with its checkboxes.  One of its decisions makes development iterative: each iteration carries one program from source to bytes, a theorem, a comparison with native Lean, an axiom check, and a commit, adding only what that program needs.  `devnotes.md` records each step in dated prose: the analysis, the options, the decision, what was built, and the measurements.
