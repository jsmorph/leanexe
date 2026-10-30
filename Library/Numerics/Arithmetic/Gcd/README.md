# Gcd: Euclid's algorithm

## Request, specification, and program

[The request](request.txt) asks for the greatest common divisor of any two words, by Euclid's
remainder loop, with `gcd a 0 = a`.  [The specification](Spec.lean) states it with Lean's `Nat.gcd`.
[The program](Program.lean) is tail recursive: `gcd a b` is `a` when `b = 0` and `gcd b (a % b)`
otherwise, and it terminates because `a % b < b`.  The compiler translates the tail recursion into a
loop, so a call makes no further calls.  [The module definition](Module.lean) compiles it into a
1,445-byte `gcd.wasm` that exports `gcd`, and [the verified compilation](Compiled.lean) compiles the
same definition with the verified compiler into a 1,461-byte module.

## The bytes compute `Nat.gcd`

| Theorem | Statement |
|---------|-----------|
| `gcd_eq` | The program equals the specification on every pair of words. |
| `gcd_implements` | Function 2 computes `gcd` on its two arguments. |
| `gcd_bytes` | The module's bytes decode to a module whose `gcd` export implements `expected`: from any store that satisfies the runtime invariant, a call returns `expected (a, b)` or stops at `unreachable`. |

`gcd_eq` is in [the proof of the specification](Proof.lean), which the theorems of both compilers
use, and the other theorems are in [the proofs](Verify.lean).  They use only `propext`,
`Classical.choice`, and `Quot.sound`.  `gcd_implements` follows from `gcd_step`, one theorem about a run of the loop body,
by the rule of the tail-recursion template.  `gcd_eq` follows from `Nat.gcd_rec` by induction on the
second argument.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.Gcd.Verify
mkdir -p build/gcd
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Arithmetic.Gcd.Module Library.Numerics.Arithmetic.Gcd.gcd.module build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:60 i64:42
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../../../README.md#commands).  The call prints 6.  [The module
tests](../../../../tests/modules/run.sh) of [`Cases.lean`](../../../../tests/TestSupport/Modules/Gcd.lean) compare 49 pairs in Wasmtime
against `expected`, including `(0, 0)`, `(1, 2^64 − 1)`, and consecutive Fibonacci numbers.

## The verified compiler's module

`verified_compile compiled := [gcd]` in [the verified compilation](Compiled.lean) compiles the tail
recursion into a loop.  `gcd` allocates nothing, so the generated `compiled.gcd.implements` excludes
the trap, and the generated `compiled.gcd.pure` states that function 2 computes `gcd` from every
store and leaves the store unchanged.  `gcd_call` composes `compiled.gcd.pure` with `gcd_eq`, and
`compiled.gcd.native` states the same computation for the C function of the module's translation.

| Theorem | Statement |
|---------|-----------|
| `gcd_export` | The export `gcd` is function 2. |
| `gcd_call` | Called with the words `a` and `b` from any store, function 2 returns `expected (a, b)`, the word of `Nat.gcd a.toNat b.toNat`, without a trap and leaves the store unchanged. |

`gcd_bytes` allows a trap at `unreachable` and requires a store that satisfies the runtime
invariant, and `gcd_call` excludes the trap and requires nothing of the store.  `gcd_call` lists the
arguments as `Runs` takes them, `b` before `a`, since Talos lists them with the top of the stack
first.  The GCD of [the native tests](../../../../tests/TestSupport/Native/Gcd.lean), which the
bare-metal program runs, is a separate definition with its own theorems.

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

The call prints 6, as the LeanExe module's call does.  [The verified
driver](../../../../tests/verified/run.sh) runs the 49 pairs of
[`Cases.lean`](../../../../tests/TestSupport/Modules/Gcd.lean) in Wasmtime against `expected` and
checks that no call allocates.  [The native driver](../../../../tests/native/verified.sh) runs them
on the module's translation to C, compiled with CompCert.

## Related examples

[`PrimeFactors`](../PrimeFactors/README.md) is tail recursion with a measure of two values instead
of one.  [`Words`](../../../../Examples/Words/README.md) has tail recursion over records, and
[`Scale`](../../../../Examples/Scale/README.md) shows how the IR tests a divisor.  The LTG entry
[`tail-recursion-loop`](../../../../ltg/entries/tail-recursion-loop/README.md) describes the rule.

## References

- D. E. Knuth, *The Art of Computer Programming*, Vol. 2, *Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, section 4.5.2, on Euclid's algorithm.
- Lean core's
  [`Nat.gcd`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Gcd.html), which
  the specification uses, and Mathlib's lemmas about it, which the proof of `gcd_eq` uses.
