# Euclidean GCD

This implementation computes the greatest common divisor of two `UInt64` values with Euclid's remainder loop.  Zero inputs are accepted, including `gcd 0 0 = 0`.  It belongs to the number-theory library.

The [binary GCD component](../binary-gcd/README.md) implements a different algorithm for the same task.  Its fraction client uses the same input and output conventions.

## Use

From a configured repository checkout, the command builds the Lean source and compiler, compiles the imported functions to WASM, and executes them in Wasmtime:

```sh
tools/seminum gcd 48 18
# 6
tools/seminum fraction 48 18
# 8/3
tools/seminum ratio 2 1,3,2 2,2
# 5/2
```

The [setup guide](../../README.md#setup-and-commands) lists prerequisites.  Arguments are decimal integers from zero through `18446744073709551615`.  Fraction reduction requires a positive denominator.  Invalid input exits with status 2 and a diagnostic on stderr.

```lean
import LeanExe.Lib.NumberTheory.Gcd

def LeanExe.Examples.commonFactor (a b : UInt64) : UInt64 :=
  LeanExe.Lib.NumberTheory.gcd a b
```

The API is `gcd (a b : UInt64) : UInt64`.  The [source](../../../LeanExe/Lib/NumberTheory/Gcd.lean) contains the loop.  The [client programs](../../../LeanExe/Examples/Seminum.lean) use it for fraction reduction and for a polynomial ratio that also calls the polynomial library.

## Specification and tests

The intended result is `Nat.gcd a.toNat b.toNat`, represented as a word.  This implementation uses one remainder per iteration and constant working storage.  Correctness proofs are deferred.

`node test/seminum.js` compares WASM and native Lean on boundary values and client cases.  The native GCD results also agree with `Nat.gcd` on those inputs.  The [technical report](report.pdf) explains the recurrence and clients and includes the executable source.  Rebuild it with `tools/seminum reports`.

## Annotated references

- [Paul E. Black, “Euclid's algorithm,” NIST DADS](https://xlinux.nist.gov/dads/HTML/euclidalgo.html): supplies the remainder recurrence used here.  This component extends the entry's positive-input description with explicit zero-input behavior and a `UInt64` API.
