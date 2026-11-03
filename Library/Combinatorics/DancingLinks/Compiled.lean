import Library.Combinatorics.DancingLinks.Proof
import Verified.Reflect.Command
import Verified.Call
import Verified.Congr

/-! The verified compiler's module of exact cover by dancing links.  The recursive `search` takes
the call depth, so `count`'s code does too, and its generated `trapFree` theorem assumes the frames
condition `fits 1000 x`.  `search_fits` shows that the condition holds for every array once the
depth bound is below the number of frames, by induction on the bound, so `count_fits` derives it
from `N ≤ 998`.  `count_call` composes `trapFree` with `count_eq` for valid inputs, and
`valid_callSpec` composes the generated theorem of `valid` with `valid_eq` for every input.  An
array in memory has fewer than `2^29` words, which the proofs' bound of `2^50` covers. -/

namespace Library.Combinatorics.DancingLinks

open Wasm LeanExe.Pipeline

verified_compile compiled := [hide, unhide, hideColumn, unhideColumn, unlinkItem, relinkItem,
  coverItem, uncoverItem, coverOthers, uncoverOthers, choose, next, search, nodeCount, build, count,
  valid]

theorem count_export :
    ({ name := "count", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem valid_export :
    ({ name := "valid", funcIdx := 18 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The search has enough frames whenever its depth bound is below their number. -/
theorem search_fits : ∀ (k : Nat) (d b : UInt64) (t : Array UInt64), d.toNat < k →
    compiled.search.fits k (d, b, { val := t }) = true
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, d, b, t, h => by
    rw [compiled.search.fits_eq]
    split
    · rfl
    · rename_i hc
      have hd : d ≠ 0 := fun e => hc (by simp [e])
      have hpos : 0 < d.toNat := Nat.pos_of_ne_zero fun e => hd (UInt64.toNat_inj.mp (by rw [e]; rfl))
      have hle : 1 ≤ d := by rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; exact hpos
      have hd1 : (d - 1).toNat < k := by
        rw [UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_one]
        omega
      exact Verified.loopFits_true (fun _ => rfl) (fun _ _ => search_fits k _ _ _ hd1) _ _ _

/-- A valid input finds the frames of its search. -/
theorem count_fits (x : Array UInt64) (hv : Valid x) : compiled.count.fits 1000 x = true := by
  rw [show (1000 : Nat) = 999 + 1 from rfl, compiled.count.fits_eq]
  refine search_fits 999 _ _ _ ?_
  have := first_word x
  have := hv.1
  simp only [UInt64.toNat_ofNat, Nat.zero_mod] at *
  omega

/-- From a ready store with room for `compiled.count.bound 1000 x` bytes, function 20, the export
`count`, returns `countSpec x` for a valid input `x`, without a trap, and leaves a ready store. -/
theorem count_call :
    Verified.Call compiled.module compiled.tables 20 countSpec
      (fun x heap store => Valid x ∧
        heap.Within store compiled.module (compiled.count.bound 1000 x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.count.bound 1000 x) :=
  Verified.call_on (fun x => Valid x)
    (Verified.ImplementsTables.call (.ofA compiled.count.trapFree) compiled.tables nofun)
    (fun x _ _ h => ⟨h.1, count_fits x h.1, h.2⟩)
    fun _ _ _ x ⟨_, _, hxs⟩ hv => count_eq x hv (by have := hxs.values.size_lt_memory32; omega)

/-- From a ready store with room for `compiled.valid.bound x` bytes, function 18, the export
`valid`, returns `validSpec x` without a trap and leaves a ready store. -/
theorem valid_callSpec :
    Verified.CallSpec compiled.module compiled.tables 18 validSpec compiled.valid.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.valid.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ => valid_eq x (by have := hxs.values.size_lt_memory32; omega)

#print axioms count_call
#print axioms valid_callSpec

end Library.Combinatorics.DancingLinks
