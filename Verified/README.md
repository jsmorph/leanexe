# Verified: a compiler with a correctness theorem

## What it is

This library is a second compiler for LeanExe, written as an ordinary Lean function with one
theorem that covers every program it accepts.  The `LeanExe` compiler is meta code over
`Lean.Expr` and is untrusted, so each of its programs needs its own proof.  This compiler takes a
program in a source language with a meaning in Lean, `denote`, and its theorem states that the
compiled module computes `denote` of the program.  It grows in small iterations, each ending with
bytes, a theorem, and a test in Wasmtime.

The library shares the trusted base and the statement of correctness with `LeanExe`: Talos's
semantics, the encoder and decoder with `decode_encode`, `Implements` and its relatives in
[`LeanExe/Pipeline/`](../LeanExe/Pipeline/), and the runtime.  It copies, and will change, the
parts of the IR it needs, so ordinary development of `LeanExe` does not affect it.  Nothing in
`LeanExe` or `Examples` imports it, and it is not a default target of `lake build`.

## What it covers

A program is a list of functions in which each function may call the functions after it in the list,
so the calls have no cycles.  A function's parameters and result are 64-bit words, `Bool`s, floats,
arrays of words, `Bool`s, or floats, or pairs of these, and its body is a typed expression.  The
element types, `Elem`, are a sub-inductive of the types: `Ty.elem e` is the type of an element and
`Ty.array e` the type of an array of elements, so an array never holds an array or a pair.  An
expression of type `t` over a context `Γ` of types that may call functions with the signatures `S`
has type `Expr S Γ t`, so every expression is well typed, reads only variables in scope, and calls
only functions that exist.  Expressions are constants, variables, `let` bindings, calls, pairs and
their destructuring, the operations `+`, `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, and `>>>`
on words, the unsigned comparisons `==`, `!=`, `<`, and `≤`, float literals, the operations `+`,
`-`, `*`, `/`, `Float.sqrt`, `Float.abs`, negation, `min`, and `max` on floats, the comparisons
`==`, `!=`, `<`, and `≤` on floats, the conversions `UInt64.toFloat`, `Float.toUInt64`,
`Float.toBits`, and `Float.ofBits`, the `Bool` operations `!`, `&&`, and `||`, `if`, `LeanExe.loop`,
an array's size `xs.size.toUInt64`, the read `xs[i.toNat]!`, the update `xs.set! i.toNat v`, the
extensions `xs.push v` and `xs ++ ys`, and `LeanExe.build`, each with Lean's meaning.  Arithmetic
wraps modulo 2^64, division by zero gives 0, the remainder by zero is the dividend, a shift uses its
amount modulo 64, a read past the end of an array gives Lean's default element, 0, `false`, or
`0.0`, and an update past the end leaves the array unchanged.  A float operation has the meaning of
Lean's `Float`, which [`F64Bits.lean`](../LeanExe/ProofKit/F64Bits.lean) proves equal on bit
patterns to Talos's `IEEE64` functions, the semantics of WebAssembly's f64 instructions in the
deterministic profile, in which every NaN result is the canonical NaN.  `LeanExe.loop n init f`
applies `f` to the indices 0 to `n - 1` in order, starting from the state `init`, and the state may
have any of the types.  `LeanExe.build n f` is the array of `n` elements whose element `i` is `f i`.
A variable is numbered by its distance from the front of the context: a binding's value is variable
0 of its body, parameter `i` is variable `i` of the function's body, a loop's body has the state as
variable 0 and the index as variable 1, and a build's element has the index as variable 0.  The
size, the read, the update, and the extensions take array variables, and a call's argument that
holds arrays is a place, a variable or a pair of places, and a variable at an owned parameter.

A value is carried as words, as `Implements` passes it: a word as itself, a `Bool` as 1 or 0, a
float as its bit pattern in an f64 word, a pair as its first component's words followed by its
second's, and an array as the address of its length word and its elements' words in memory, each
element as a word holds it: a `Bool` as 1 or 0 and a float as its bit pattern.  `Elem.words` gives
these words, the identity for an array of words, as Lean's instances for `Array UInt64`,
`Array Float`, and arrays of `Flat` types such as `Bool` store them.  A function with a pair result
returns several WebAssembly results.  Each value holds its arrays in a mode, borrowed or owned,
which `Expr.mode` computes from the modes of the variables.  A function's signature gives each array
parameter a mode.  The function reads a borrowed parameter and leaves it in place, and it consumes
an owned parameter's array, releasing it at entry when the body does not use it.  A call's result, a
function's result, and a built, updated, or extended array are owned, so a function copies a
borrowed value that it returns.  Each expression consumes the owned variables that die in it, those
live before it and not after: an owned variable moves into the value where it dies and is copied
where it stays live, a reader or a call releases an owned variable that dies there, and a branch, a
binding, and a loop release the owned variables that die without a use.  A pair has one mode, and a
loop's state is owned when its initial value or its body's value is owned, so a borrowed component
or state is copied.  A copy allocates through the runtime's `alloc` and writes the length word and
the elements.  A function's locals are its parameters, an i64 local for each further position, and
an f64 local for every position.  A word of type f64 occupies its position's f64 local and any other
word its i64 local, and a function copies its f64 parameter words to their positions' f64 locals at
entry.  Negation compiles to the subtraction of the operand from −0, which is Lean's negation on
every input, since `f64.neg` turns the canonical NaN into a NaN with the sign bit set.
`Float.ofBits` compiles to `f64.reinterpret_i64` followed by the addition of −0, which gives the
canonical NaN for a NaN pattern and leaves every other float unchanged.  A float constant's code
holds its canonical bit pattern, which the compiler computes with integer operations, so the bytes
that `tools/Emit.lean` writes by evaluating the compiler natively do not depend on Lean's native
float code.  Each binding's value is stored in positions of its own, and a call pushes its
arguments' words in order and calls the function, which the module places before its callers.  An
argument at an owned parameter moves its variable into the call when the variable is owned, dies at
the call, and no other argument with arrays reads it, and is copied otherwise.  Every argument's
variables stay live until the call, so a later argument may read a moved array, and the call then
releases the owned variables that die there and that it does not consume.  An `if` stores the words
of its value in locals in each branch and loads them after it, because the encoder writes block
types of at most one result.  A loop keeps its count, its index, and its state in locals, compares
the index with the count at the top of a WebAssembly `loop` inside a `block`, and branches out of
the block when the index reaches the count.  A build keeps its count, the array's address, and the
index in locals, traps at `unreachable` when the count is `2^29` or more, since the array would not
fit in 32-bit memory, allocates the array and writes its length word, and stores each element after
the element's code runs.  The outer variables that only the element reads stay live through the loop
and are released after it.  An update runs its position's and value's code first and then takes the
array in an owned position: an owned array that dies there is updated in its own block, and any
other array is copied first.  An extension takes the array with room for the result: an owned array
that dies there grows in its own block when the block has room and otherwise moves to a block of at
least twice its capacity, which releases the old block, and any other array is copied once into a
block with room.  `push` then writes the new element, and `++` copies the other array's elements
after the first's and releases the other array when it is owned and dies there.  A read keeps the
array's address and the position in locals, compares the position with the length word, loads the
element's word or yields 0, and converts a float's word to an f64 with `f64.reinterpret_i64`.  An
update, a push, and a build convert a float to its word with `i64.reinterpret_f64` before the store.
WebAssembly traps on a zero divisor, so the compiled division and remainder save their operands in
scratch locals, test the divisor, and return Lean's result for zero.  [`Source.lean`](Source.lean)
defines the syntax and `Func.denote`, [`Compile.lean`](Compile.lean) the compiler,
[`State.lean`](State.lean) the representation of values in the heap and the facts about variables,
[`Heap.lean`](Heap.lean) the specifications of the allocation, copy, and release code, and
[`Correct.lean`](Correct.lean) the theorem.  The compiled module has the layout of `LeanExe`'s
modules, with the runtime's `alloc` and `release` at functions 0 and 1.

The theorem for each function is `ImplementsA aborts`, the heap form of `Implements` in
[`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean).  From any heap and store
with the allocator invariant and arguments that represent `x`, the function returns words that
represent `f x` and own its arrays, keeps the allocator invariant and the memory caps, keeps every
region of the caller's heap, and places the result's arrays apart from those regions.  `aborts` is
part of each function's signature.  It is true when the result holds arrays, a parameter is owned,
the body builds, updates, or extends an array, or the body calls a function whose `aborts` is true,
whose result holds arrays, or which owns a parameter, since only then can the function allocate, and
an allocation traps at `unreachable` when memory runs out.  A function whose `aborts` is false
returns without a trap.

The reflector, `verified_compile p := [f, g, …]` in [`Reflect/Command.lean`](Reflect/Command.lean),
writes ordinary Lean definitions as a source program.  For each definition `f` it adds the source
function `p.f.func`, the equation `p.f.denote_eq` that it means `f`, and `p.f.implements`, which
states that function `2 + k` of the module `p.module` computes `f` on the tuple of its arguments,
with the `Represent` instances that Lean synthesizes for the tuple and the result.  `p.bytes` states
that the module's bytes decode to a module that computes every listed definition.  The reflector is
meta code and is not trusted: it builds each equation from the lemmas of
[`Reflect/Lemmas.lean`](Reflect/Lemmas.lean), one per Lean form, and Lean's kernel checks it.  An
`if` on a `Prop` comparison needs a lemma, because Lean elaborates it with `UInt64`'s `Decidable`
instance, which is not definitionally the source's test of a `Bool`.  A call of an earlier listed
definition becomes a source call, proved from the callee's equation, and `LeanExe.loop` becomes a
loop whose body is the reflection of the loop function's body.  The reflector chooses the parameter
modes with `Expr.paramChoice` in [`Reflect/Modes.lean`](Reflect/Modes.lean): an array parameter is
owned when the body consumes it where it dies, as the array of an update or an extension, at a call
that moves it into an owned parameter, or as the result, directly or through a binding, a branch, a
pair, or a loop's state, and borrowed otherwise.  The choice is not trusted, since the theorem holds
for every choice of modes.  The reflector binds with `let` an array that a size or a read reads, a
call's argument with arrays that is not a place, and an argument at an owned parameter that is not a
variable.  It replaces a `let` of a place by its body with the place for the variable, and splits
every variable of a pair type into variables for its components, so that a projection reads a
component without a copy of the pair.  It writes `min a b` and `max a b` on floats as `if a ≤ b`,
which is Lean's definition and differs from `f64.min` and `f64.max` on NaN and on zeros of opposite
sign, after binding with `let` an operand that is not a variable.  Each of these rewritings leaves
the meaning unchanged.  The reflector computes the bit pattern of a float literal, of `Float.ofBits`
or `UInt64.toFloat` of a word literal, and of a negated literal, and the kernel checks by `decide`
that the literal has it.  It rejects `=` and `≠` on floats, which compare bit patterns, so that
`0.0 ≠ -0.0`, and which no f64 instruction computes.

| Theorem | Statement |
|---------|-----------|
| `Prog.correct` | For every program and every function in it, the function's index in the compiled module computes the function's meaning in the sense of `ImplementsA`, and returns without a trap when its signature's `aborts` is false. |
| `Func.correct` | A function in a module whose functions at the call indices compute the functions it calls computes its own meaning.  `Env.Rep.apart` turns the callee's `Separate` into the facts of `Holds` for the parameters at entry. |
| `Expr.code_spec` | From any heap and store with the allocator invariant, in which the variables live before an expression hold words that represent their values in their modes and the blocks of the owned ones lie apart from the other variables' arrays, the code of the expression ends with words that represent the expression's value in its mode.  The step of the heap and store consumes only the blocks of the owned variables that die in the expression, the variables live after it hold their values, an owned value's blocks are new, and the value lies apart from the variables live after it.  The code changes no parameter and no local below the locals it uses.  One lemma per construct proves it, `spec_word` through `spec_append`; `After.seq`, `After.bind`, `After.bind2`, and `After.release` combine the facts of consecutive codes, of a binding and its body, and of a release.  The loop case uses `wp_loop_cons` with an invariant: the index `i` is at most the count, and the state locals hold the state after `i` iterations with the facts of `After` for the variables live in the loop.  The build case's invariant is an owned array of the count's length whose elements below the index are built, with the facts of `After`; `wp_allocArray` gives the array, and `After.writeElement` stores each element in place.  The update case takes the array with `spec_ownedVar`, which moves an owned variable that dies and copies any other, and writes the element with `After.writeElement`.  The extension cases take the array with `spec_room`, which proves the growth in place, the move to a larger block with `After.replace`, and the copy; `wp_allocCopy` and `wp_copyInto` give the allocation and the copy loop that the copy of a value also uses, and `After.rewrite` the writes inside an owned block.  The call case takes the arguments with `args_spec`, which proves that the owned arguments' blocks lie apart from one another and from the borrowed arguments' arrays, as the callee's `Separate` requires, and that the caller's live variables lie apart from the blocks that the call consumes. |
| `ImplementsA.lean` | A function's theorem for the verified compiler's representation gives the theorem with the instances that Lean synthesizes for its argument tuple and result, in which an owned array parameter has type `Moved (Array α)`.  The instances for arrays and their `Moved` forms are those of [`Implements.lean`](../LeanExe/Pipeline/Implements.lean) for `Array UInt64`, `Array Float`, and arrays of `Flat` types, which include `Bool`.  `Ty.leanInst`, `Ty.argInst`, and `argsInst` rebuild those instances by recursion over the types and modes, so no signature needs a proof of its own. |
| `compiled.bytes` | In each example, the bytes of the module decode to a module that computes the example's Lean functions: [`Poly.lean`](Examples/Poly.lean), `a * b + c * c - 7`; [`Mix.lean`](Examples/Mix.lean), division, remainder, the bitwise operations, and the shifts; [`Lets.lean`](Examples/Lets.lean), four nested `let` bindings, one inside the operand of a division; [`Select.lean`](Examples/Select.lean), `Bool` bindings, `if` on a `Bool` and on `<`, `>`, and `≠`, a `Bool` parameter, and a `Bool` result; [`Pairs.lean`](Examples/Pairs.lean), pairs as parameters and results, `.1`, `.2`, and `match` on a pair, a pair inside a pair, and calls that pass and return pairs; [`Calls.lean`](Examples/Calls.lean), four definitions in which `sumSq` calls `sq` and `pick` calls the other three, with a call as an argument of a call and a `Bool`-valued call as the test of an `if`; [`Loops.lean`](Examples/Loops.lean), loops over a word, over a pair, and over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose body calls an earlier definition; [`Arrays.lean`](Examples/Arrays.lean), sums, a dot product, a count, and a search over arrays in loops, reads at computed positions, a pair of arrays passed to calls, and an array chosen by an `if` and bound with `let`; and [`Owned.lean`](Examples/Owned.lean), array results, copies of parameters, owned call results that a reader, a call, a branch, or an unused binding releases, a moved result, a loop whose state is an owned array, a pair of owned arrays taken apart, and arrays built with `LeanExe.build`, one whose element builds and releases an array of its own and one whose element reads an owned array that dies after the build; and [`Updates.lean`](Examples/Updates.lean), updates of a parameter, of a built array, of a loop's state, two updates in a row, and an update of an array that stays live; and [`Grow.lean`](Examples/Grow.lean), `push` and `++` on parameters, built arrays, and loop states, onto an array that stays live, an array appended to itself, and an owned right operand; and [`Modes.lean`](Examples/Modes.lean), parameters that a function returns, updates, or moves into an owned parameter, also from a loop's state and before a later argument reads the array, and parameters that stay borrowed because the body uses them again.  Its `byHand`, written without the reflector, has an owned parameter that the body never reads and one that it reads last; and [`Floats.lean`](Examples/Floats.lean), a piecewise function, a scaled hypotenuse, float comparisons as conditions and as `Bool` values, `min`, `max`, negation, a loop over a pair of floats, a function with parameters of every kind and a pair result with a float, a call of float functions, the conversions between words and floats, a power of two built from its exponent field, and literal NaN patterns; and [`Elements.lean`](Examples/Elements.lean), sums, a dot product, and a maximum over arrays of floats, a grid built from converted indices, an `axpy` that updates an owned array of floats in place, an extension, flags of negative elements, a count and a selection by flags, an update and a push of an owned array of `Bool`s, and a sieve of Eratosthenes. |

The proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  Every example is
an ordinary Lean file: its definitions and one `verified_compile` command.

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified
tests/verified/run.sh
```

The commands build the library and its theorems, write each example's module to `build/verified/`,
validate it with `wasm-tools`, and compare every case of [`Cases.lean`](Examples/Cases.lean) between
the Wasmtime host and native Lean.  The setup is that of [the repository
README](../README.md#commands).  The cases cover words near 0, 2^32, 2^63, and 2^64, where the
arithmetic wraps, zero divisors, shift amounts of 64 or more, equal words in comparisons, loop
counts of 0, 1, and up to 65,537, empty arrays, reads and updates past the end of an array, and
floats that are zeros of both signs, infinities, NaN, and the smallest subnormal.  Native Lean
returns the canonical NaN for every NaN result, and the host enables Cranelift's NaN
canonicalization, so the cases compare float results bit for bit.  Native Lean writes a panic
message with a backtrace for each read past the end and returns 0, and for each update past the end
and leaves the array unchanged; the script counts these messages and fails on any other output to
standard error.  For each case of `Owned.lean`, `Updates.lean`, `Grow.lean`, `Modes.lean`, and
`Elements.lean` the script also reads the runtime's allocation and release counters after the call
and requires the blocks still allocated to be exactly the host's array arguments and the result's
arrays, which shows that the code releases every block it owns.  Cases of `Updates.lean`,
`Grow.lean`, and `Elements.lean` also bound the number of allocations, which shows the in-place
updates and the growth by doubling: a loop of `n` pushes allocates at most `2 + log₂ (n + 1)`
blocks.  One case builds an array of `2^29` words and must trap at `unreachable`.

## Related work

[The journal](../devnotes.md) records the analysis that led to this library and its plan.  The
`LeanExe` rule for expressions, `Expr.program_spec` in
[`LeanExe/IR/Expr.lean`](../LeanExe/IR/Expr.lean), proves the same kind of fact for one IR program
at a time.  [`Scale`](../Examples/Scale/README.md)
and [`Axpy`](../Examples/Axpy/README.md) are the closest programs of the `LeanExe` compiler.

## References

- X. Leroy, "Formal Verification of a Realistic Compiler," *Communications of the ACM*
  52(7):107–115, 2009.
- E. Mullen, S. Pernsteiner, J. R. Wilcox, Z. Tatlock, and D. Grossman, "Œuf: Minimizing the Coq
  Extraction TCB," *Proceedings of CPP 2018*.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
