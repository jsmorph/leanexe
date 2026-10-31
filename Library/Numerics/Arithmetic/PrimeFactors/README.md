# Prime factors: a count with multiplicity

## Request, specification, and program

[The request](request.txt) asks for the number of prime factors of a word, counted with
multiplicity, with 0 for 0 and 1.  [The specification](Spec.lean) states that count with Mathlib's
`Nat.primeFactorsList`.  [The program](Program.lean) divides out each divisor in increasing order
while the divisor is at most the remaining value divided by it, and then counts what remains, which
is 1 or a prime.  `countFactors` is tail recursive and terminates by a measure of the remaining
value and the distance from the divisor to it, so it needs no fuel parameter.

## The bytes count prime factors

`verified_compile compiled := [countFactors, compute]` in [the verified compilation](Compiled.lean)
compiles the definitions into a 1,619-byte module and the tail recursion into a loop.  The reflector
reads the condition `remaining ≤ 1 ∨ divisor ≤ 1` as the disjunction of its two decisions, and the
termination proof of the loop splits each case of Lean's functional induction on the step's
conditions, since Lean states the negated condition as `1 < remaining ∧ 1 < divisor`.  The measure
of `countFactors`, `remaining.toNat * 2 ^ 64 + …`, made the kernel exhaust its recursion when it
unfolded the definition to check the reflector's equations, and the reflector now states those
equations so that the kernel does not unfold the function, as [the
journal](../../../../devnotes.md#2026-10-30-array-literals-and-conditions-on-propositions-in-the-reflector)
records.  Both functions take and return words and allocate nothing, so the generated
`compiled.compute.pure` states that function 3 computes `compute` from every store without a trap
and leaves the store unchanged.  The generated `compiled.countFactors.native` and
`compiled.compute.native` state the computations of the C functions of the module's translation.

| Theorem | Statement |
|---------|-----------|
| `countFactors_eq` | When every prime factor of `remaining` is at least `divisor`, which is at least 2, `countFactors` adds the number of prime factors of `remaining` to `count`. |
| `compute_eq` | `compute n = expected n` for every word `n`. |
| `compute_export` | Export `compute` of `compiled.module` is function 3. |
| `primeFactors_call` | Called with the word `n` from any store, function 3 returns `expected n`, the number of prime factors of `n` counted with multiplicity, without a trap and leaves the store unchanged. |
| `primeFactors_file`, `primeFactors_file_decode` | `build/verified/primeFactors.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`, as [the file module](File.lean) states. |

`countFactors_eq` and `compute_eq` are in [the proof of the specification](Proof.lean), and the
number theory stays in `countFactors_eq`, which concerns the Lean program alone.  `compute_eq`
applies `countFactors_eq` with the divisor 2 and the count 0, since every prime is at least 2.
`primeFactors_call` composes `compiled.compute.pure` with `compute_eq` and requires nothing of the
store.  The verified compilation prints the axioms of `primeFactors_call`, which are `propext`,
`Classical.choice`, and `Quot.sound`.

## Building, running, and testing

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

The commands build the theorems, write the module, call it in the Wasmtime host, and run the tests,
with the setup of [the repository README](../../../../README.md#commands).  The call prints 4, since
60 = 2 · 2 · 3 · 5.  [The verified driver](../../../../tests/verified/run.sh) runs 13 inputs in
Wasmtime against `expected` and checks that no call allocates.  The inputs, `primeFactorInputs` of
[the prime-factor case inputs](../../../../tests/TestSupport/Modules/PrimeFactors.lean), include 0,
1, 2^63, and 2^64 − 1, and [the verified library
cases](../../../../tests/TestSupport/LibraryCases.lean) print each with its expected result.  [The
native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C,
compiled with CompCert.  Without `--cases`, the verified driver also checks the file module against
the file it wrote, and it fails unless `primeFactors_file` and `primeFactors_file_decode` report
only `propext`, `Classical.choice`, and `Quot.sound`.

## Related examples

[`Gcd`](../Gcd/README.md) is tail recursion with a one-word measure.
[`Lookup`](../../../../Examples/Lookup/README.md) and
[`TreeLookup`](../../../../Examples/TreeLookup/README.md) also return a value computed by a loop.
[The forms example](../../../../Verified/Examples/Forms.lean) has a tail recursion that stops on a
disjunction, as `countFactors` does.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 2, *Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, section 4.5.4.
- Mathlib,
  [`Mathlib.Data.Nat.Factors`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factors.html),
  `Nat.primeFactorsList`.
