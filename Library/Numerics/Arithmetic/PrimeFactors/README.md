# Prime factors: a count with multiplicity

## Request, specification, and program

[The request](request.txt) asks for the number of prime factors of a word, counted with
multiplicity, with 0 for 0 and 1.  [The specification](Spec.lean) states that count with Mathlib's
`Nat.primeFactorsList`.  [The program](Program.lean) divides out each divisor in increasing order
while the divisor is at most the remaining value divided by it, and then counts what remains, which
is 1 or a prime.  `countFactors` is tail recursive and terminates by a measure of the remaining
value and the distance from the divisor to it, so it needs no fuel parameter.  [The module
definition](Module.lean) compiles `countFactors` and `compute` into a 1,613-byte `primeFactors.wasm`
that exports both, and [the verified compilation](Compiled.lean) compiles the same definitions with
the verified compiler into a 1,619-byte module.

## The bytes count prime factors

| Theorem | Statement |
|---------|-----------|
| `countFactors_eq` | When every prime factor of `remaining` is at least `divisor`, which is at least 2, `countFactors` adds the number of prime factors of `remaining` to `count`. |
| `compute_eq` | The program equals the specification on every word. |
| `countFactors_implements` | Function 2 computes `countFactors` on its three arguments. |
| `primeFactors_bytes` | The module's bytes decode to a module whose `compute` export implements `expected`: from any store that satisfies the runtime invariant, a call returns `expected n` or stops at `unreachable`. |

`countFactors_eq` and `compute_eq` are in [the proof of the specification](Proof.lean), which the
theorems of both compilers use, and the other theorems are in [the proofs](Verify.lean).  They use
only `propext`, `Classical.choice`, and `Quot.sound`.  The loop rule of the tail-recursion template proves `countFactors_implements` from
one theorem about a run of the loop body, and the number theory stays in `countFactors_eq`, which
concerns the Lean program alone.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.PrimeFactors.Verify
mkdir -p build/primeFactors
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.PrimeFactors.Module Library.Numerics.Arithmetic.PrimeFactors.primeFactors.module \
  build/primeFactors/primeFactors.wasm
build/tools/leanexe-wasmtime-host call build/primeFactors/primeFactors.wasm compute i64 i64:60
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../../../README.md#commands).  The call prints 4, since 60 = 2 · 2 · 3 · 5.
[The module tests](../../../../tests/modules/run.sh) of [`Cases.lean`](../../../../tests/TestSupport/Modules/PrimeFactors.lean) run 13 inputs in
Wasmtime against `expected`, including 0, 1, 2^63, and 2^64 − 1.

## The verified compiler's module

`verified_compile compiled := [countFactors, compute]` in [the verified compilation](Compiled.lean)
compiles the tail recursion into a loop.  The reflector reads the condition
`remaining ≤ 1 ∨ divisor ≤ 1` as the disjunction of its two decisions, and the termination proof
of the loop splits each case of Lean's functional induction on the step's conditions, since Lean
states the negated condition as `1 < remaining ∧ 1 < divisor`.  Both functions take and return
words and allocate nothing, so the generated `compiled.compute.pure` states that function 3
computes `compute` from every store without a trap and leaves the store unchanged.

| Theorem | Statement |
|---------|-----------|
| `compute_export` | The export `compute` is function 3. |
| `primeFactors_call` | Called with the word `n` from any store, function 3 returns `expected n`, the number of prime factors of `n` counted with multiplicity, without a trap and leaves the store unchanged. |

`primeFactors_bytes` allows a trap at `unreachable` and requires a store that satisfies the runtime
invariant, and `primeFactors_call` excludes the trap and requires nothing of the store.  The
measure of `countFactors`, `remaining.toNat * 2 ^ 64 + …`, made the kernel exhaust its recursion
when it unfolded the definition to check the reflector's equations, and the reflector now states
those equations so that the kernel does not unfold the function, as [the
journal](../../../../devnotes.md#2026-10-30-array-literals-and-conditions-on-propositions-in-the-reflector)
records.  The generated `compiled.countFactors.native` and `compiled.compute.native` state the
computations of the C functions of the module's translation.

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.PrimeFactors.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.PrimeFactors.Compiled \
  Library.Numerics.Arithmetic.PrimeFactors.compiled.module build/verified/primeFactors.wasm
build/tools/leanexe-wasmtime-host call build/verified/primeFactors.wasm compute i64 i64:60
tests/verified/run.sh --cases primeFactors
tests/native/verified.sh --module primeFactors
```

The call prints 4, as the LeanExe module's call does.  [The verified
driver](../../../../tests/verified/run.sh) runs the 13 inputs of
[`Cases.lean`](../../../../tests/TestSupport/Modules/PrimeFactors.lean) in Wasmtime against
`expected` and checks that no call allocates.  [The native driver](../../../../tests/native/verified.sh)
runs them on the module's translation to C, compiled with CompCert.

## Related examples

[`Gcd`](../Gcd/README.md) is tail recursion with a one-word measure.
[`Lookup`](../../../../Examples/Lookup/README.md) and [`TreeLookup`](../../../../Examples/TreeLookup/README.md) are the other demos that
return a value computed by a loop.  The LTG entry
[`tail-recursion-loop`](../../../../ltg/entries/tail-recursion-loop/README.md) describes the rule.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 2, *Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, section 4.5.4, on factoring by trial division.
- Mathlib's
  [`Nat.primeFactorsList`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factors.html),
  which the specification uses.
