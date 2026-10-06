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
list, so the calls have no cycles.  A function's parameters and result are 64-bit words or
`Bool`s, and its body is a typed expression.  An expression of type `t` over a context `Γ` of
types that may call functions with the signatures `S` has type `Expr S Γ t`, so every expression
is well typed, reads only variables in scope, and calls only functions that exist.  Expressions
are constants, variables, `let` bindings, calls, the operations `+`, `-`, `*`, `/`, `%`,
`&&&`, `|||`, `^^^`, `<<<`, and `>>>` on words, the unsigned comparisons `==`, `!=`, `<`, and `≤`,
the `Bool` operations `!`, `&&`, and `||`, and `if`, each with Lean's meaning.  Arithmetic wraps
modulo 2^64, division by zero gives 0, the remainder by zero is the dividend, and a shift uses its
amount modulo 64.  A variable is numbered by its distance from the front of the context: a
binding's value is variable 0 of its body, and parameter `i` is variable `i` of the function's
body.

Every value is one word: a `Bool` is 1 or 0, as `Implements` passes a `Bool`.  Each binding's
value is stored in a local of its own, and a call pushes its arguments in order and calls the
function, which the module places before its callers.  WebAssembly traps on a zero divisor, so the compiled
division and remainder save their operands in scratch locals, test the divisor, and return Lean's
result for zero.  [`Source.lean`](Source.lean) defines the syntax and `Func.denote`,
[`Compile.lean`](Compile.lean) the compiler, and [`Correct.lean`](Correct.lean) the theorem.  The
compiled module has the layout of `LeanExe`'s modules, with the runtime's `alloc` and `release`
at functions 0 and 1.

| Theorem | Statement |
|---------|-----------|
| `Prog.correct` | For every program and every function in it, the function's index in the compiled module returns the word of the function's meaning from any store, without a trap, and leaves the store unchanged (`ImplementsPureA false`). |
| `Func.correct` | A function in a module whose functions at the call indices compute the functions it calls computes its own meaning. |
| `Expr.code_spec` | From any frame in which every variable holds the word of its value in its local, the code of an expression pushes the word of the expression's value and changes no parameter and no local below the locals it uses. |
| `poly_bytes` | The example [`Poly.lean`](Examples/Poly.lean): the bytes of the module for `a * b + c * c - 7` decode to a module that computes the Lean function `poly`. |
| `scramble_bytes` | The example [`Lets.lean`](Examples/Lets.lean): the bytes of the module for a function of four nested `let` bindings, one inside the operand of a division, decode to a module that computes the Lean function `scramble`. |
| `select_bytes` | The example [`Select.lean`](Examples/Select.lean): the bytes of the module for `median`, with three `Bool` bindings and nested conditionals, and `inBand`, which returns a `Bool`, decode to a module that computes both Lean functions. |
| `calls_bytes` | The example [`Calls.lean`](Examples/Calls.lean): the bytes of the module for `sq`, `sumSq`, which calls `sq`, `small`, which returns a `Bool`, and `pick`, which calls the other three, with a call as an argument of a call, decode to a module that computes the four Lean functions. |
| `mix_bytes` | The example [`Mix.lean`](Examples/Mix.lean): the bytes of the module for `((a / b + a % c) ^^^ ((a &&& b) \|\|\| (c <<< b))) - (a >>> c)` decode to a module that computes the Lean function `mix`. |

The proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  The examples'
source functions are written by hand, and a theorem for each, such as `pick_denote`, proves by
`rfl` that it means its Lean function.

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified
tests/verified/run.sh
```

The commands build the library and its theorems, write each example's module to
`build/verified/`, validate it with `wasm-tools`, and compare every case of
[`Cases.lean`](Examples/Cases.lean) between the Wasmtime host and native Lean.  The setup is that
of [the repository README](../README.md#commands).  The cases cover words near 0, 2^32, 2^63, and
2^64, where the arithmetic wraps, zero divisors, shift amounts of 64 or more, and equal words in
comparisons.

## Related work

[The journal](../devnotes.md) records the analysis that led to this library and its plan.  The
`LeanExe` rule for expressions, `Expr.program_spec` in [`LeanExe/IR/Expr.lean`](../LeanExe/IR/Expr.lean),
proves the same kind of fact for one IR program at a time.  [`Scale`](../Examples/Scale/README.md)
and [`Axpy`](../Examples/Axpy/README.md) are the closest programs of the `LeanExe` compiler.

## References

- X. Leroy, "Formal Verification of a Realistic Compiler," *Communications of the ACM*
  52(7):107–115, 2009.
- E. Mullen, S. Pernsteiner, J. R. Wilcox, Z. Tatlock, and D. Grossman, "Œuf: Minimizing the Coq
  Extraction TCB," *Proceedings of CPP 2018*.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
