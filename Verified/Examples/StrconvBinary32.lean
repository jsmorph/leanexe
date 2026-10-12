import CodeLib.IEEE32.Roundoff
import Mathlib.Data.Finset.Max

/-!
The nearest-even binary32 reference, defined as ProofKit defines the binary64 one in
`F64NearestNonnegative` and `F64PositiveRounding`.  `Nearest y w` states that the finite
nonnegative word `w` lies at least as close to the real `y` as every other finite nonnegative word,
by the value `CodeLib.IEEE32.value` of Talos's binary32 model, and `NearestEven` adds that `w` has
the smaller last bit, which for a positive word is the last bit of the significand.  From the
overflow threshold `2 ^ 128 - 2 ^ 103` on, halfway between the largest finite value
`2 ^ 128 - 2 ^ 104` and `2 ^ 128`, the reference is positive infinity, as roundTiesToEven gives,
since the largest finite value has an odd significand.  `StrconvGrid` proves that the nearest-even
word is unique.
-/

namespace Verified.Examples.StrconvBinary32
open CodeLib.IEEE32

set_option exponentiation.threshold 4096

/-- The encoding of positive infinity, the first word past the finite nonnegative ones. -/
def limit : Nat := 0x7F800000

def positiveInfinity : UInt32 := 0x7F800000

noncomputable def overflowThreshold : ℝ := (2 : ℝ) ^ 128 - (2 : ℝ) ^ 103

/-- `w` is finite and nonnegative, and no finite nonnegative word lies closer to `y`. -/
def Nearest (y : ℝ) (w : UInt32) : Prop :=
  w.toNat < limit ∧ ∀ v : UInt32, v.toNat < limit → |value w - y| ≤ |value v - y|

def NearestEven (y : ℝ) (w : UInt32) : Prop :=
  Nearest y w ∧ ∀ v : UInt32, Nearest y v → w.toNat % 2 ≤ v.toNat % 2

private theorem word_of_nat (n : Nat) (hn : n < limit) : (UInt32.ofNat n).toNat = n :=
  UInt32.toNat_ofNat_of_lt' (hn.trans (by decide : limit < 2 ^ 32))

theorem exists_nearest (y : ℝ) : ∃ w : UInt32, Nearest y w := by
  classical
  let s := Finset.range limit
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (by decide : 0 < limit)⟩
  obtain ⟨n, hn, hm⟩ := Finset.exists_min_image s
    (fun n : Nat => |value (UInt32.ofNat n) - y|) hs
  have hnl : n < limit := Finset.mem_range.mp hn
  refine ⟨UInt32.ofNat n, by rw [word_of_nat n hnl]; exact hnl, ?_⟩
  intro v hv
  have h := hm v.toNat (Finset.mem_range.mpr hv)
  simpa only [UInt32.ofNat_toNat] using h

theorem exists_nearest_even (y : ℝ) : ∃ w : UInt32, NearestEven y w := by
  classical
  obtain ⟨v, hv⟩ := exists_nearest y
  let s := (Finset.range limit).filter (fun n : Nat => Nearest y (UInt32.ofNat n))
  have hsv : v.toNat ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hv.1, by simpa only [UInt32.ofNat_toNat] using hv⟩
  obtain ⟨n, hn, hm⟩ := Finset.exists_min_image s (fun n : Nat => n % 2) ⟨v.toNat, hsv⟩
  have hn' := Finset.mem_filter.mp hn
  have hnl : n < limit := Finset.mem_range.mp hn'.1
  refine ⟨UInt32.ofNat n, hn'.2, ?_⟩
  intro w hw
  have hsw : w.toNat ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hw.1, by simpa only [UInt32.ofNat_toNat] using hw⟩
  simpa only [word_of_nat n hnl] using hm w.toNat hsw

/-- A nearest-even finite word of `y`. -/
noncomputable def nearestEven (y : ℝ) : UInt32 := Classical.choose (exists_nearest_even y)

theorem nearestEven_spec (y : ℝ) : NearestEven y (nearestEven y) :=
  Classical.choose_spec (exists_nearest_even y)

/-- The nearest-even binary32 word of a nonnegative `y`, positive infinity from the overflow
threshold on. -/
noncomputable def roundNearestEven (y : ℝ) : UInt32 :=
  if overflowThreshold ≤ y then positiveInfinity else nearestEven y

#print axioms exists_nearest
#print axioms exists_nearest_even
#print axioms nearestEven_spec

end Verified.Examples.StrconvBinary32
