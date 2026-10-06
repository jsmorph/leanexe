# Gcd: Euclid's algorithm

## What it is

This example stands for [main's Demo
6](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-6/README.md),
which maps a one-word array `[x]` to `[gcd(x, 42)]` and returns an array of any other length
unchanged.  [The request](request.txt) here asks for the greatest common divisor of any two words,
by Euclid's remainder loop, with `gcd a 0 = a`.  Main's function is this one with the second
argument fixed at 42 and an array wrapper.  [The specification](Spec.lean) states it with Lean's
`Nat.gcd`, as main's did.

[The program](Program.lean) is tail recursive: `gcd a b` is `a` when `b = 0` and `gcd b (a % b)`
otherwise, and it terminates because `a % b < b`.  The compiler translates the tail recursion into a
loop, so a call makes no further calls.  [The module definition](Module.lean) compiles it into a
1,445-byte `gcd.wasm` that exports `gcd`.

## What it shows

| Theorem | Statement |
|---------|-----------|
| `gcd_eq` | The program equals the specification on every pair of words. |
| `gcd_implements` | Function 2 computes `gcd` on its two arguments. |
| `gcd_bytes` | The module's bytes decode to a module whose `gcd` export implements `expected`: from any store that satisfies the runtime invariant, a call returns `expected (a, b)` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), and they use only `propext`, `Classical.choice`, and
`Quot.sound`.  `gcd_implements` follows from `gcd_step`, one theorem about a run of the loop body,
by the rule of the tail-recursion template, and `gcd_eq` follows from `Nat.gcd_rec` by induction on
the second argument.  Main's annotation-free proof took 191 lines for one 1,770-byte binary.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Gcd.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Gcd.Module Examples.Gcd.gcd.module build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:60 i64:42
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The call prints 6.  [The module
tests](../../tests/modules/run.sh) of [`Cases.lean`](Cases.lean) compare 49 pairs in Wasmtime
against `expected`, including `(0, 0)`, `(1, 2^64 − 1)`, and consecutive Fibonacci numbers.

## Related examples

[`PrimeFactors`](../PrimeFactors/README.md) is tail recursion with a measure of two values instead
of one.  [`Words`](../Words/README.md) has tail recursion over records, and
[`Scale`](../Scale/README.md) shows how the IR tests a divisor.  The LTG entry
[`tail-recursion-loop`](../../ltg/entries/tail-recursion-loop/README.md) describes the rule.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 2, *Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, section 4.5.2, on Euclid's algorithm.
- Lean core's
  [`Nat.gcd`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Gcd.html), which
  the specification uses, and Mathlib's lemmas about it, which the proof of `gcd_eq` uses.
