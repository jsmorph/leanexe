# Gcd: Euclid's algorithm

This example stands for [main's Demo
6](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-6/README.md),
which maps a one-word array `[x]` to `[gcd(x, 42)]` and returns an array of any other length
unchanged.  [The request](request.txt) here asks for the greatest common divisor of any two words,
by Euclid's remainder loop, with `gcd a 0 = a`.  Main's function is this one with the second
argument fixed at 42 and an array wrapper.  [The specification](Spec.lean) states it with Mathlib's
`Nat.gcd`, as main's did.

[The program](Program.lean) is tail recursive: `gcd a b` is `a` when `b = 0` and `gcd b (a % b)`
otherwise, and it terminates because `a % b < b`.  [The module definition](Module.lean) compiles it
into a 1,445-byte `gcd.wasm` that exports `gcd`.

| Theorem | Statement |
|---------|-----------|
| `gcd_eq` | The program equals the specification on every pair of words. |
| `gcd_implements` | Function 2 computes `gcd` on its two arguments. |
| `gcd_bytes` | The module's bytes decode to a module whose `gcd` export implements `expected`: from any store that satisfies the runtime invariant, a call returns `expected (a, b)` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), and they use only `propext`,
`Classical.choice`, and `Quot.sound`.  `gcd_implements` follows from `gcd_step`, one theorem about
a run of the loop body, by the rule of the tail-recursion template, and `gcd_eq` follows from
`Nat.gcd_rec` by induction on the second argument.  Main's annotation-free proof took 191 lines
for one 1,770-byte binary.  The module tests compare 49 pairs in Wasmtime against `expected`,
including `(0, 0)`, `(1, 2^64 − 1)`, and consecutive Fibonacci numbers.

```sh
tools/leanrun --timeout 60m lake build Examples.Gcd.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Gcd.Module Examples.Gcd.gcd.module build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:60 i64:42
```
