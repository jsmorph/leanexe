# Prime factors: a count with multiplicity

This example is [main's Demo
1](https://github.com/jsmorph/leanexe/blob/eef07963d28004e9333876d8ef0673cbe09ff69a/demos/demo-1/README.md),
carried to this branch's pipeline.  [The request](request.txt) asks for the number of prime factors
of a word, counted with multiplicity, with 0 for 0 and 1.  [The specification](Spec.lean) states
that count with Mathlib's `Nat.primeFactorsList`, as main's did.

[The program](Program.lean) divides out each divisor in increasing order while the divisor is at
most the remaining value divided by it, and then counts what remains, which is 1 or a prime.
`countFactors` is tail recursive and terminates by a measure of the remaining value and the distance
from the divisor to it, so it needs no fuel parameter, where main's program took one.  [The module
definition](Module.lean) compiles `countFactors` and `compute` into a 1,613-byte `primeFactors.wasm`
that exports both.

| Theorem | Statement |
|---------|-----------|
| `countFactors_eq` | When every prime factor of `remaining` is at least `divisor`, which is at least 2, `countFactors` adds the number of prime factors of `remaining` to `count`. |
| `compute_eq` | The program equals the specification on every word. |
| `countFactors_implements` | Function 2 computes `countFactors` on its three arguments. |
| `primeFactors_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call returns `expected n` or stops at `unreachable`. |

The theorems are in [the proofs](Verify.lean), and they use only `propext`, `Classical.choice`, and
`Quot.sound`.  Main's proof concerned one binary and took 329 lines.  Here the loop rule of the
tail-recursion template proves `countFactors_implements` from one theorem about a run of the loop
body, and the number theory stays in `countFactors_eq`, which concerns the Lean program alone.  The
module tests run 13 inputs in Wasmtime against `expected`, including 0, 1, 2^63, and 2^64 − 1.

```sh
tools/leanrun --timeout 60m lake build Examples.PrimeFactors.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.PrimeFactors.Module Examples.PrimeFactors.primeFactors.module \
  build/primeFactors/primeFactors.wasm
build/tools/leanexe-wasmtime-host call build/primeFactors/primeFactors.wasm compute i64 i64:60
```
