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

A program is a list of functions in which each function may call the functions after it in the
list, so the calls have no cycles.  A function's parameters are 64-bit words, `Bool`s, arrays of
words, or pairs of these, its result is a word, a `Bool`, or a pair of them, and its body is a
typed expression.  An expression of type `t` over a context `Γ` of types that may call functions
with the signatures `S` has type `Expr S Γ t`, so every expression is well typed, reads only
variables in scope, and calls only functions that exist.  Expressions are constants, variables,
`let` bindings, calls, pairs and their destructuring, the operations `+`, `-`, `*`, `/`, `%`,
`&&&`, `|||`, `^^^`, `<<<`, and `>>>` on words, the unsigned comparisons `==`, `!=`, `<`, and `≤`,
the `Bool` operations `!`, `&&`, and `||`, `if`, `LeanExe.loop`, an array's size
`xs.size.toUInt64`, and the read `xs[i.toNat]!`, each with Lean's meaning.  Arithmetic wraps
modulo 2^64, division by zero gives 0, the remainder by zero is the dividend, a shift uses its
amount modulo 64, and a read past the end of an array gives 0.  `LeanExe.loop n init f` applies
`f` to the indices 0 to `n - 1` in order, starting from the state `init`, and the state may have
any of the types.  A variable is numbered by its distance from the front of the context: a
binding's value is variable 0 of its body, parameter `i` is variable `i` of the function's body,
and a loop's body has the state as variable 0 and the index as variable 1.

A value is carried as words, as `Implements` passes it: a word as itself, a `Bool` as 1 or 0, a
pair as its first component's words followed by its second's, and an array as the address of its
length word and elements in memory.  An array parameter is borrowed: the function reads it and
leaves it in place.  A function with a pair result returns several WebAssembly results.  Each
binding's value is stored in locals of its own, and a call pushes its arguments' words in order
and calls the function, which the module places before its callers.  An `if` stores the words of
its value in locals in each branch and loads them after it, because the encoder writes block
types of at most one result.  A loop keeps its count, its index, and its state in locals,
compares the index with the count at the top of a WebAssembly `loop` inside a `block`, and
branches out of the block when the index reaches the count.  A read keeps the array's address and
the position in locals, compares the position with the length word, and loads the element or
yields 0.  WebAssembly traps on a zero divisor, so the compiled division and remainder save their
operands in scratch locals, test the divisor, and return Lean's result for zero.
[`Source.lean`](Source.lean) defines the syntax and `Func.denote`, [`Compile.lean`](Compile.lean)
the compiler, [`State.lean`](State.lean) the representation of values in the heap and the facts
about variables, and [`Correct.lean`](Correct.lean) the theorem.  The compiled module has the
layout of `LeanExe`'s modules, with the runtime's `alloc` and `release` at functions 0 and 1.

The theorem for each function is `ImplementsA aborts`, the heap form of `Implements` in
[`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean).  From any heap and
store with the allocator invariant and arguments that represent `x`, the function returns words
that represent `f x`, keeps the allocator invariant and the memory caps, and keeps every region of
the caller's heap.  `aborts` is part of each function's signature and is true only when the
function allocates, directly or through a call, which no construct does yet, so every function
returns without a trap.  `Expr.code` takes the variables live after an expression, and each
variable has a mode, borrowed or owned, for the allocation and ownership iterations that follow.

The reflector, `verified_compile p := [f, g, …]` in
[`Reflect/Command.lean`](Reflect/Command.lean), writes ordinary Lean definitions as a source
program.  For each definition `f` it adds the source function `p.f.func`, the equation
`p.f.denote_eq` that it means `f`, and `p.f.implements`, which states that function `2 + k` of the
module `p.module` computes `f` on the tuple of its arguments, with the `Represent` instances that
Lean synthesizes for the tuple and the result.  `p.bytes` states that the module's bytes decode to
a module that computes every listed definition.  The reflector is meta code and is not trusted: it
builds each equation from the lemmas of [`Reflect/Lemmas.lean`](Reflect/Lemmas.lean), one per Lean
form, and Lean's kernel checks it.  An `if` on a `Prop` comparison needs a lemma, because Lean
elaborates it with `UInt64`'s `Decidable` instance, which is not definitionally the source's test
of a `Bool`.  A call of an earlier listed definition becomes a source call, proved from the
callee's equation, and `LeanExe.loop` becomes a loop whose body is the reflection of the loop
function's body.

| Theorem | Statement |
|---------|-----------|
| `Prog.correct` | For every program and every function in it, the function's index in the compiled module computes the function's meaning in the sense of `ImplementsA`, and returns without a trap when its signature's `aborts` is false. |
| `Func.correct` | A function in a module whose functions at the call indices compute the functions it calls computes its own meaning. |
| `Expr.code_spec` | From any heap and store with the allocator invariant, in which the variables live before an expression hold words that represent their values in their locals, the code of the expression ends after a step of the heap and store with words that represent the expression's value, and changes no parameter and no local below the locals it uses.  One lemma per construct proves it, `spec_word` through `spec_get`.  The loop case uses `wp_loop_cons` with an invariant: the index `i` is at most the count, and the state locals hold the state after `i` iterations. |
| `ImplementsA.lean` | A function's theorem for the verified compiler's representation gives the theorem with the instances that Lean synthesizes for its argument tuple and result.  `Ty.leanInst` and `argsInst` rebuild those instances by recursion over the types, so no signature needs a proof of its own. |
| `compiled.bytes` | In each example, the bytes of the module decode to a module that computes the example's Lean functions: [`Poly.lean`](Examples/Poly.lean), `a * b + c * c - 7`; [`Mix.lean`](Examples/Mix.lean), division, remainder, the bitwise operations, and the shifts; [`Lets.lean`](Examples/Lets.lean), four nested `let` bindings, one inside the operand of a division; [`Select.lean`](Examples/Select.lean), `Bool` bindings, `if` on a `Bool` and on `<`, `>`, and `≠`, a `Bool` parameter, and a `Bool` result; [`Pairs.lean`](Examples/Pairs.lean), pairs as parameters and results, `.1`, `.2`, and `match` on a pair, a pair inside a pair, and calls that pass and return pairs; [`Calls.lean`](Examples/Calls.lean), four definitions in which `sumSq` calls `sq` and `pick` calls the other three, with a call as an argument of a call and a `Bool`-valued call as the test of an `if`; [`Loops.lean`](Examples/Loops.lean), loops over a word, over a pair, and over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose body calls an earlier definition; and [`Arrays.lean`](Examples/Arrays.lean), sums, a dot product, a count, and a search over arrays in loops, reads at computed positions, a pair of arrays passed to calls, and an array chosen by an `if` and bound with `let`. |

The proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  Every example is
an ordinary Lean file: its definitions and one `verified_compile` command.

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified
tests/verified/run.sh
```

The commands build the library and its theorems, write each example's module to
`build/verified/`, validate it with `wasm-tools`, and compare every case of
[`Cases.lean`](Examples/Cases.lean) between the Wasmtime host and native Lean.  The setup is that
of [the repository README](../README.md#commands).  The cases cover words near 0, 2^32, 2^63, and
2^64, where the arithmetic wraps, zero divisors, shift amounts of 64 or more, equal words in
comparisons, loop counts of 0, 1, and up to 65,537, empty arrays, and reads past the end of an
array.  Native Lean writes a panic message with a backtrace for each read past the end and returns
0; the script counts these messages and fails on any other output to standard error.

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
