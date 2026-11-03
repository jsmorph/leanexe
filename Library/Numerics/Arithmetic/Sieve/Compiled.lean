import Library.Numerics.Arithmetic.Sieve.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of the sieve.  By the compiler's rules, which the verified
compiler's manual states, the compiler translates the loops of `crossOff`, `countUnmarked`, and
`primes` and the tail recursion of `sieveFrom` into loops, so no theorem of the module has a
call-depth premise.  `primes` takes a word and builds two arrays, the flags and the result.
`primes_implements` composes the generated `compiled.primes.trapFree` with `primes_eq`, and
`primes_bound` states the generated bound as a block of `N` flags and a block of the result's
words. -/

namespace Library.Numerics.Arithmetic.Sieve

open Wasm LeanExe.Pipeline

verified_compile compiled := [crossOff, sieveFrom, countUnmarked, primes]

theorem primes_export :
    ({ name := "primes", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `primes`, called with a word `N` from a heap with the allocator
invariant, a memory cap of at most 65,535 pages, and room for `compiled.primes.bound N`, returns
without a trap the owned array `expected N`, the primes below `N` in increasing order, and raises
`top` by at most the bound. -/
theorem primes_implements :
    ImplementsA false compiled.module 5 expected
      (fun x heap store => heap.Within store compiled.module (compiled.primes.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.primes.bound x) :=
  Verified.implementsA_congr compiled.primes.trapFree fun _ _ _ x _ => primes_eq x

/-- The generated bound is a block of `N` flags and a block of the words of the result. -/
theorem primes_bound (N : UInt64) :
    compiled.primes.bound N =
      Verified.blockCost N.toNat + Verified.blockCost (expected N).size := by
  rw [compiled.primes.bound_eq, countUnmarked_eq, expected_eq]
  simp

#print axioms primes_implements

end Library.Numerics.Arithmetic.Sieve
