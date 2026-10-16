import CodeLib.IEEE64.Roundoff
import Mathlib.Data.Finset.Max

namespace LeanExe.ProofKit.F64NearestNonnegative
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def limit : Nat := 0x7FF0000000000000

def Nearest (y : ℝ) (w : UInt64) : Prop :=
  w.toNat < limit ∧
    ∀ v : UInt64, v.toNat < limit → |value w - y| ≤ |value v - y|

def NearestEven (y : ℝ) (w : UInt64) : Prop :=
  Nearest y w ∧ ∀ v : UInt64, Nearest y v → w.toNat % 2 ≤ v.toNat % 2

theorem word_toNat (n : Nat) (hn : n < limit) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (hn.trans (by decide : limit < 2 ^ 64))

theorem nearest_finite (y : ℝ) (w : UInt64) (hw : Nearest y w) :
    Finite w ∧ Wasm.IEEE64.sign w = false := by
  have hb : w.toNat < 2047 * 2 ^ 52 := hw.1
  have hs : w.toNat < 2 ^ 63 := hb.trans (by norm_num)
  constructor
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne]
    omega
  · simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    omega

theorem exists_nearest (y : ℝ) : ∃ w : UInt64, Nearest y w := by
  classical
  let s := Finset.range limit
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (by decide : 0 < limit)⟩
  obtain ⟨n, hn, hm⟩ := Finset.exists_min_image s
    (fun n : Nat => |value (UInt64.ofNat n) - y|) hs
  have hnl : n < limit := Finset.mem_range.mp hn
  refine ⟨UInt64.ofNat n, by rw [word_toNat n hnl]; exact hnl, ?_⟩
  intro v hv
  have h := hm v.toNat (Finset.mem_range.mpr hv)
  simpa only [UInt64.ofNat_toNat] using h

theorem exists_nearest_even (y : ℝ) : ∃ w : UInt64, NearestEven y w := by
  classical
  obtain ⟨v, hv⟩ := exists_nearest y
  let s := (Finset.range limit).filter (fun n : Nat => Nearest y (UInt64.ofNat n))
  have hsv : v.toNat ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hv.1, by simpa only [UInt64.ofNat_toNat] using hv⟩
  obtain ⟨n, hn, hm⟩ := Finset.exists_min_image s (fun n : Nat => n % 2) ⟨v.toNat, hsv⟩
  have hn' := Finset.mem_filter.mp hn
  have hnl : n < limit := Finset.mem_range.mp hn'.1
  refine ⟨UInt64.ofNat n, hn'.2, ?_⟩
  intro w hw
  have hsw : w.toNat ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hw.1, by simpa only [UInt64.ofNat_toNat] using hw⟩
  simpa only [word_toNat n hnl] using hm w.toNat hsw

#print axioms nearest_finite
#print axioms exists_nearest
#print axioms exists_nearest_even

end LeanExe.ProofKit.F64NearestNonnegative
