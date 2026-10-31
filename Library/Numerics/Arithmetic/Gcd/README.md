# Gcd: Euclid's algorithm

## Request, specification, and program

[The request](request.txt) asks for the greatest common divisor of any two words, by Euclid's
remainder loop, with `gcd a 0 = a`.  [The specification](Spec.lean) states it with Lean's `Nat.gcd`.
[The program](Program.lean) is tail recursive: `gcd a b` is `a` when `b = 0` and `gcd b (a % b)`
otherwise, and it terminates because `a % b < b`.  `gcd_eq`, in [the proof of the
specification](Proof.lean), states that the program equals the specification on every pair of
words, and it follows from `Nat.gcd_rec` by induction on the second argument.

## The bytes compute `Nat.gcd`

`verified_compile compiled := [gcd]` in [the verified compilation](Compiled.lean) compiles the
definition into a 1,461-byte module.  The compiler translates the tail recursion into a loop, so a
call makes no further calls.  `gcd` allocates nothing, so the generated `compiled.gcd.implements`
excludes the trap, and the generated `compiled.gcd.pure` states that function 2 computes `gcd` from
every store and leaves the store unchanged.  The generated `compiled.gcd.native` states the same
computation for the C function of the module's translation.

| Theorem | Statement |
|---------|-----------|
| `gcd_eq` | `gcd a b = expected (a, b)` for all words `a` and `b`. |
| `gcd_export` | Export `gcd` of `compiled.module` is function 2. |
| `gcd_call` | Called with the words `a` and `b` from any store, function 2 returns `expected (a, b)`, the word of `Nat.gcd a.toNat b.toNat`, without a trap and leaves the store unchanged. |
| `gcd_callSpec` | From a ready store in which `top` can rise by `compiled.gcd.bound (a, b)` bytes, function 2 returns `expected (a, b)` and leaves a ready store, as `Verified.CallSpec` states. |
| `gcd_file`, `gcd_file_decode` | `build/verified/gcd.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`, as [the file module](File.lean) states. |

`gcd_call` composes `compiled.gcd.pure` with `gcd_eq`, requires nothing of the store, and lists the
arguments as `Runs` takes them, `b` before `a`, since Talos lists them with the top of the stack
first.  `gcd_callSpec` follows from `compiled.gcd.trapFree` and `gcd_eq` through
`Verified.ImplementsTables.call` and `Verified.Call.spec` of [the call
module](../../../../Verified/Call.lean).  The verified compilation prints the axioms of `gcd_call`
and `gcd_callSpec`, which are `propext`, `Classical.choice`, and `Quot.sound`.  The GCD of [the
native tests](../../../../tests/TestSupport/Native/Gcd.lean), which the bare-metal program runs, is
a separate definition with its own theorems.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.Gcd.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.Gcd.Compiled Library.Numerics.Arithmetic.Gcd.compiled.module \
  build/verified/gcd.wasm
build/tools/leanexe-wasmtime-host call build/verified/gcd.wasm gcd i64 i64:60 i64:42
tests/verified/run.sh --cases gcd
tests/native/verified.sh --module gcd
```

The commands build the theorems, write the module, call it in the Wasmtime host, and run the tests,
with the setup of [the repository README](../../../../README.md#commands).  The call prints 6.
[The verified driver](../../../../tests/verified/run.sh) runs 49 pairs in Wasmtime against
`expected` and checks that no call allocates.  The pairs, `gcdPairs` of [the GCD case
inputs](../../../../tests/TestSupport/Modules/Gcd.lean), include `(0, 0)`, `(5, 0)`, and
`(1, 2^64 − 1)`, and [the verified library cases](../../../../tests/TestSupport/LibraryCases.lean)
print each with its expected result.  [The native driver](../../../../tests/native/verified.sh)
runs them on the module's translation to C, compiled with CompCert.  Without `--cases`, the
verified driver also checks the file module against the file it wrote, and it fails unless
`gcd_file` and `gcd_file_decode` report only `propext`, `Classical.choice`, and `Quot.sound`.

## Related examples

[`PrimeFactors`](../PrimeFactors/README.md) is tail recursion with a measure of two values instead
of one.  [`Words`](../../../../Examples/Words/README.md) has tail recursion over records.
[`Scale`](../../../../Examples/Scale/README.md) divides by a word that may be zero, and the compiled
code tests the divisor before the division, as it does before the remainder in `gcd`.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 2, *Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, section 4.5.2.
- Lean core,
  [`Init.Data.Nat.Gcd`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Gcd.html),
  `Nat.gcd` and `Nat.gcd_rec`.
