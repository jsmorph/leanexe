import Library.Strings.Kmp.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of the occurrences of a pattern.  By the compiler's rules, which
the verified compiler's manual states, the compiler translates the tail recursion of `fall` and the
loops of `failure`, `count`, and `occurrences` into loops, so no theorem of the module has a
call-depth premise.  The caller lends the pattern and the text.  For a nonempty pattern the module
builds the table of `failure` and the result, and for the empty pattern it builds the positions
below `n` and extends that array by `n`.  `occurrences_implements` composes the generated
`compiled.occurrences.trapFree` with `occurrences_eq`, and `occurrences_bound` states the generated
bound. -/

namespace Library.Strings.Kmp

open Wasm LeanExe.Pipeline LeanExe.Dialect

verified_compile compiled := [byte, fall, step, failure, count, occurrences]

theorem occurrences_export :
    ({ name := "occurrences", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 7, the export `occurrences`, called with a lent pattern, its length, a lent text, and
its length, from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and
room for `compiled.occurrences.bound`, returns without a trap the owned array `expected`, the
positions of the occurrences in increasing order, and raises `top` by at most the bound. -/
theorem occurrences_implements :
    ImplementsA false compiled.module 7 (fun x => expected x.1 x.2.1 x.2.2.1 x.2.2.2)
      (fun x heap store => heap.Within store compiled.module (compiled.occurrences.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.occurrences.bound x) :=
  Verified.implementsA_congr compiled.occurrences.trapFree fun _ _ _ x _ =>
    occurrences_eq x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The generated bound: for the empty pattern, a block of `n + 1` words, or for `n = 2^64 - 1` a
block of `n` words and its growth by one word, and otherwise a block for the table of `m` lengths
and a block for the result. -/
theorem occurrences_bound (pat : Array UInt64) (m : UInt64) (txt : Array UInt64) (n : UInt64) :
    compiled.occurrences.bound (pat, m, txt, n) =
      if m = 0 then
        (if n < 0xffffffffffffffff then Verified.blockCost (n.toNat + 1)
        else Verified.blockCost n.toNat + Verified.growCost (n.toNat + 1) 1)
      else Verified.blockCost m.toNat + Verified.blockCost (expected pat m txt n).size := by
  rw [compiled.occurrences.bound_eq, compiled.failure.bound_eq]
  by_cases h : m = 0
  · rw [ite_eq_left h, ite_eq_left h]
    by_cases hmax : n < 0xffffffffffffffff
    · rw [ite_eq_left hmax, ite_eq_left hmax]
      have := UInt64.lt_iff_toNat_lt.mp hmax
      congr 1
      simp only [UInt64.toNat_add, UInt64.reduceToNat] at *
      omega
    · rw [ite_eq_right hmax, ite_eq_right hmax, build_size]
  · rw [ite_eq_right h, ite_eq_right h, count_eq_size pat m txt n (by
      rcases Nat.eq_zero_or_pos m.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) h
      · exact e)]

#print axioms occurrences_implements
#print axioms occurrences_bound

end Library.Strings.Kmp
