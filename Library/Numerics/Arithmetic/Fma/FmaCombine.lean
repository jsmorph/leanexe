import Library.Numerics.Arithmetic.Fma.FmaParts
import Library.Numerics.Arithmetic.Fma.FmaRoundPack
import Library.Numerics.Arithmetic.Fma.FmaNearestEven
import Library.Numerics.Arithmetic.Fma.FmaAlign

/-!
The rounded sum of `FmaParts.combine`.  For normalized addends `X` at scale `wX` and `Y` at scale
`wY`, with `X · 2 ^ wX ≥ Y · 2 ^ wY`, `tail_spec` proves that `FmaParts.tail` returns `+0` for an
exact zero sum and otherwise the signed nearest-even reference of the exact sum
`±X · 2 ^ wX ± Y · 2 ^ wY`, in units of `2 ^ -2400`.  The aligned sum is exact when the sticky
shift loses no set bit, and otherwise it is odd, at least `2 ^ 124`, and within one unit of the
exact sum at its scale, so that `FmaGrid.roundsTo_transfer` carries the rounding over
(`round_sum`).  `combine_spec` orders the product and the addend as `combine` does.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaCombine
open Verified.Examples FmaWords FmaGrid FmaRound FmaRoundPack FmaNearestEven FmaAlign FmaParts
open CodeLib.IEEE64 LeanExe.ProofKit

/-- The sign `±1` of a sign bit. -/
noncomputable def sgn (s : UInt64) : ℝ := if s = 1 then -1 else 1

theorem sgn_ne_zero (s : UInt64) : sgn s ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

theorem sign_cases (s : UInt64) (hs : s.toNat ≤ 1) : s = 0 ∨ s = 1 := by
  rcases (show s.toNat = 0 ∨ s.toNat = 1 by omega) with h | h
  · left; exact UInt64.toNat_inj.mp (by rw [h]; rfl)
  · right; exact UInt64.toNat_inj.mp (by rw [h]; rfl)

theorem pair_zero (h l : UInt64) : (h == 0 && l == 0) = decide (pair h l = 0) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_iff,
    ← UInt64.toNat_inj, ← UInt64.toNat_inj, UInt64.toNat_zero]
  unfold pair
  simp only [Nat.reducePow]
  omega

/-- The rounding of a nonzero aligned sum `Z` at scale `wX = d + WY`, exact or within one unit of
the exact sum `T` at scale `WY`. -/
theorem round_sum (sX zh zl wX : UInt64) (hsX : sX.toNat ≤ 1) (hwX : wX.toNat < 2 ^ 32)
    (T WY d : ℕ) (hWX : wX.toNat = d + WY) (hZ0 : pair zh zl ≠ 0) (hZ : pair zh zl < 2 ^ 127)
    (hT : 0 < T)
    (hcase : pair zh zl * 2 ^ d = T ∨ (pair zh zl % 2 = 1 ∧ 2 ^ 124 ≤ pair zh zl ∧
      pair zh zl * 2 ^ d < T + 2 ^ d ∧ T < pair zh zl * 2 ^ d + 2 ^ d)) :
    Fma.roundPack sX wX zh zl =
      F64SignedRounding.roundNearestEven (sgn sX * ((T * 2 ^ WY : ℕ) : ℝ) / 2 ^ 2400) := by
  obtain ⟨E, Q, hpack, hR, hb⟩ := roundPack_spec sX wX zh zl hZ0 hZ hwX
  rw [hpack]
  have hsplit : ∀ n : ℕ, n * 2 ^ wX.toNat = n * 2 ^ d * 2 ^ WY := by
    intro n; rw [hWX, pow_add, mul_assoc]
  have hRT : RoundsTo (T * 2 ^ WY) E Q := by
    rcases hcase with h | ⟨hodd, hbig, h1, h2⟩
    · rwa [hsplit, h] at hR
    · obtain ⟨_, m1, m2⟩ := msb128_spec zh zl hZ0
      have hm : 124 ≤ (Fma.msb128 zh zl).toNat := by
        by_contra hc
        have : 2 ^ ((Fma.msb128 zh zl).toNat + 1) ≤ 2 ^ 124 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hP : 0 < 2 ^ WY := by positivity
      have hdW : 2 ^ d * 2 ^ WY = 2 ^ wX.toNat := by rw [hWX, pow_add]
      apply roundsTo_transfer (pair zh zl * 2 ^ wX.toNat) (T * 2 ^ WY) E Q (pair zh zl)
        wX.toNat hR rfl hodd (by omega)
      · have h3 := Nat.mul_lt_mul_of_pos_right h1 hP
        rw [hsplit, ← hdW]
        rw [Nat.add_mul] at h3
        exact h3
      · have h3 := Nat.mul_lt_mul_of_pos_right h2 hP
        rw [hsplit, ← hdW]
        rw [Nat.add_mul] at h3
        exact h3
  have hpos : 0 < T * 2 ^ WY := by positivity
  have e : sgn sX * ((T * 2 ^ WY : ℕ) : ℝ) =
      if sX = 1 then -((T * 2 ^ WY : ℕ) : ℝ) else ((T * 2 ^ WY : ℕ) : ℝ) := by
    unfold sgn; split_ifs <;> ring
  rw [e, signed_reference (T * 2 ^ WY) E Q sX (sign_cases sX hsX) hpos hRT]

/-- The sum of the aligned addends, as `FmaParts.tail` forms it. -/
def sumZ (sX sY xh xl : UInt64) (y : UInt64 × UInt64) : UInt64 × UInt64 :=
  if sX == sY then Fma.add128 xh xl y.1 y.2 else Fma.sub128 xh xl y.1 y.2

/-- The last step of `FmaParts.tail`. -/
def finishZ (sX wX : UInt64) (z : UInt64 × UInt64) : UInt64 :=
  if z.1 == 0 && z.2 == 0 then 0 else Fma.roundPack sX wX z.1 z.2

theorem tail_eq (sX sY xh xl wX yh yl wY : UInt64) :
    tail sX sY xh xl wX yh yl wY = finishZ sX wX (sumZ sX sY xh xl (Fma.sticky128 yh yl (wX - wY))) := by
  unfold tail finishZ sumZ
  dsimp only

/-- The tail of `combine`: an exact zero sum gives `+0`, and any other sum its signed
nearest-even reference. -/
theorem tail_spec (sX sY xh xl wX yh yl wY : UInt64) (hsX : sX.toNat ≤ 1) (hsY : sY.toNat ≤ 1)
    (hX1 : 2 ^ 125 ≤ pair xh xl) (hX2 : pair xh xl < 2 ^ 126) (hX20 : pair xh xl % 2 ^ 20 = 0)
    (hY2 : pair yh yl < 2 ^ 126) (hY20 : pair yh yl % 2 ^ 20 = 0)
    (hw : wY.toNat ≤ wX.toNat) (hwX : wX.toNat < 2 ^ 32)
    (hord : pair yh yl * 2 ^ wY.toNat ≤ pair xh xl * 2 ^ wX.toNat) :
    tail sX sY xh xl wX yh yl wY =
      if sgn sX * ((pair xh xl * 2 ^ wX.toNat : ℕ) : ℝ) +
          sgn sY * ((pair yh yl * 2 ^ wY.toNat : ℕ) : ℝ) = 0 then 0
      else F64SignedRounding.roundNearestEven
        ((sgn sX * ((pair xh xl * 2 ^ wX.toNat : ℕ) : ℝ) +
          sgn sY * ((pair yh yl * 2 ^ wY.toNat : ℕ) : ℝ)) / 2 ^ 2400) := by
  obtain ⟨d, hWX⟩ : ∃ d, wX.toNat = d + wY.toNat := ⟨wX.toNat - wY.toNat, by omega⟩
  have hd : (wX - wY).toNat = d := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hw)]
    omega
  have hsplit : ∀ n : ℕ, n * 2 ^ wX.toNat = n * 2 ^ d * 2 ^ wY.toNat := by
    intro n; rw [hWX, pow_add, mul_assoc]
  have hst := sticky128_spec yh yl (wX - wY)
  rw [hd] at hst
  rw [tail_eq]
  generalize Fma.sticky128 yh yl (wX - wY) = y at hst ⊢
  generalize hXd : pair xh xl = X at hX1 hX2 hX20 hord ⊢
  generalize pair yh yl = Y at hY2 hY20 hord hst ⊢
  have hst' : pair y.1 y.2 = stickyShift Y d := hst
  have hord' : Y ≤ X * 2 ^ d := by
    apply Nat.le_of_mul_le_mul_right _ (by positivity : 0 < 2 ^ wY.toNat)
    rw [← hsplit]
    exact hord
  have h128 : (2 : ℕ) ^ 127 < 2 ^ 128 := by norm_num
  have h125 : 0 < (2 : ℕ) ^ 125 := by positivity
  by_cases hs : sX = sY
  · subst hs
    have hsum : sumZ sX sX xh xl y = Fma.add128 xh xl y.1 y.2 := by
      unfold sumZ; rw [ite_eq_left (by simp)]
    rw [hsum]
    obtain ⟨g1, g2, g3⟩ := sum_same X Y d hX2 hX1 hY2 hX20 hY20 hord'
    have hadd := add128_spec xh xl y.1 y.2 (by rw [hst', hXd]; omega)
    rw [hst', hXd] at hadd
    generalize Fma.add128 xh xl y.1 y.2 = z at hadd ⊢
    have hZ0 : pair z.1 z.2 ≠ 0 := by rw [hadd]; omega
    have hfin : finishZ sX wX z = Fma.roundPack sX wX z.1 z.2 := by
      unfold finishZ; rw [ite_eq_right (by rw [pair_zero]; simpa using hZ0)]
    rw [hfin]
    have hS : sgn sX * ((X * 2 ^ wX.toNat : ℕ) : ℝ) + sgn sX * ((Y * 2 ^ wY.toNat : ℕ) : ℝ) =
        sgn sX * (((X * 2 ^ d + Y) * 2 ^ wY.toNat : ℕ) : ℝ) := by
      rw [← mul_add, hsplit X]
      push_cast
      ring
    have hTpos : 0 < X * 2 ^ d + Y := by
      have : 0 < X * 2 ^ d := Nat.mul_pos (by omega) (by positivity)
      omega
    have hS0 : sgn sX * (((X * 2 ^ d + Y) * 2 ^ wY.toNat : ℕ) : ℝ) ≠ 0 :=
      mul_ne_zero (sgn_ne_zero sX) (by positivity)
    rw [hS, ite_eq_right hS0]
    apply round_sum sX z.1 z.2 wX hsX hwX (X * 2 ^ d + Y) wY.toNat d hWX hZ0
      (by rw [hadd]; exact g1) hTpos
    by_cases hex : Y % 2 ^ d = 0
    · left; rw [hadd]; exact g2 hex
    · right; rw [hadd]; exact g3 hex
  · have hsum : sumZ sX sY xh xl y = Fma.sub128 xh xl y.1 y.2 := by
      unfold sumZ; rw [ite_eq_right (by simpa using hs)]
    rw [hsum]
    obtain ⟨f1, g1, g2, g3⟩ := sum_diff X Y d hX2 hX1 hY2 hX20 hY20 hord'
    have hsub := sub128_spec xh xl y.1 y.2 (by rw [hst', hXd]; exact f1)
    rw [hst', hXd] at hsub
    generalize Fma.sub128 xh xl y.1 y.2 = z at hsub ⊢
    have hsgn : sgn sY = -sgn sX := by
      unfold sgn
      rcases sign_cases sX hsX with h | h <;> rcases sign_cases sY hsY with h' | h' <;>
        subst h h' <;> simp_all
    have hle : Y * 2 ^ wY.toNat ≤ X * 2 ^ d * 2 ^ wY.toNat := by rw [← hsplit]; exact hord
    have hS : sgn sX * ((X * 2 ^ wX.toNat : ℕ) : ℝ) + sgn sY * ((Y * 2 ^ wY.toNat : ℕ) : ℝ) =
        sgn sX * (((X * 2 ^ d - Y) * 2 ^ wY.toNat : ℕ) : ℝ) := by
      rw [hsgn, hsplit X, Nat.sub_mul, Nat.cast_sub hle]
      ring
    rw [hS]
    by_cases hZ : pair z.1 z.2 = 0
    · have hT : X * 2 ^ d - Y = 0 := by
        by_cases hex : Y % 2 ^ d = 0
        · rw [← g2 hex, ← hsub, hZ, zero_mul]
        · have := (g3 hex).2.1
          rw [← hsub] at this
          omega
      have hfin : finishZ sX wX z = 0 := by
        unfold finishZ; rw [ite_eq_left (by rw [pair_zero]; simpa using hZ)]
      rw [hfin, hT]
      simp
    · have hTpos : 0 < X * 2 ^ d - Y := by
        by_cases hex : Y % 2 ^ d = 0
        · rw [← g2 hex, ← hsub]
          exact Nat.mul_pos (Nat.pos_of_ne_zero hZ) (by positivity)
        · obtain ⟨_, k2, k3, _⟩ := g3 hex
          have : 2 ^ d ≤ (X - stickyShift Y d) * 2 ^ d :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
      have hS0 : sgn sX * (((X * 2 ^ d - Y) * 2 ^ wY.toNat : ℕ) : ℝ) ≠ 0 :=
        mul_ne_zero (sgn_ne_zero sX) (by positivity)
      have hfin : finishZ sX wX z = Fma.roundPack sX wX z.1 z.2 := by
        unfold finishZ; rw [ite_eq_right (by rw [pair_zero]; simpa using hZ)]
      rw [hfin, ite_eq_right hS0]
      apply round_sum sX z.1 z.2 wX hsX hwX (X * 2 ^ d - Y) wY.toNat d hWX hZ
        (by rw [hsub]; exact g1) hTpos
      by_cases hex : Y % 2 ^ d = 0
      · left; rw [hsub]; exact g2 hex
      · right; rw [hsub]; exact g3 hex

/-- Of two normalized numbers, the one at the larger scale is the larger. -/
theorem scale_order (X Y wX wY : ℕ) (hX1 : 2 ^ 125 ≤ X) (hY2 : Y < 2 ^ 126) (hw : wY < wX) :
    Y * 2 ^ wY < X * 2 ^ wX := by
  calc Y * 2 ^ wY < 2 ^ 126 * 2 ^ wY := Nat.mul_lt_mul_of_pos_right hY2 (by positivity)
    _ = 2 ^ 125 * 2 ^ (wY + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ 125 * 2 ^ wX := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hw)
    _ ≤ X * 2 ^ wX := Nat.mul_le_mul_right _ hX1

/-- `combine` returns `+0` for an exact zero sum and otherwise the signed nearest-even reference of
the exact sum. -/
theorem combine_spec (sp sc ph pl wP ch cl wC : UInt64) (hsp : sp.toNat ≤ 1) (hsc : sc.toNat ≤ 1)
    (hP1 : 2 ^ 125 ≤ pair ph pl) (hP2 : pair ph pl < 2 ^ 126) (hP20 : pair ph pl % 2 ^ 20 = 0)
    (hC1 : 2 ^ 125 ≤ pair ch cl) (hC2 : pair ch cl < 2 ^ 126) (hC20 : pair ch cl % 2 ^ 20 = 0)
    (hwP : wP.toNat < 2 ^ 32) (hwC : wC.toNat < 2 ^ 32) :
    combine sp sc ph pl wP ch cl wC =
      if sgn sp * ((pair ph pl * 2 ^ wP.toNat : ℕ) : ℝ) +
          sgn sc * ((pair ch cl * 2 ^ wC.toNat : ℕ) : ℝ) = 0 then 0
      else F64SignedRounding.roundNearestEven
        ((sgn sp * ((pair ph pl * 2 ^ wP.toNat : ℕ) : ℝ) +
          sgn sc * ((pair ch cl * 2 ^ wC.toNat : ℕ) : ℝ)) / 2 ^ 2400) := by
  rw [combine_eq]
  have hcond : (wP > wC || (wP == wC && !Fma.lt128 ph pl ch cl)) = true ↔
      (wC.toNat < wP.toNat ∨ (wP.toNat = wC.toNat ∧ ¬ pair ph pl < pair ch cl)) := by
    rw [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', lt128_spec, decide_eq_true_iff,
      beq_iff_eq, ← UInt64.toNat_inj, decide_eq_false_iff_not, gt_iff_lt, UInt64.lt_iff_toNat_lt]
  by_cases hf : (wP > wC || (wP == wC && !Fma.lt128 ph pl ch cl)) = true
  · rw [ite_eq_left hf]
    have h := hcond.mp hf
    have hw : wC.toNat ≤ wP.toNat := by omega
    have hord : pair ch cl * 2 ^ wC.toNat ≤ pair ph pl * 2 ^ wP.toNat := by
      rcases h with h | ⟨h1, h2⟩
      · exact (scale_order _ _ _ _ hP1 hC2 h).le
      · rw [h1]; exact Nat.mul_le_mul_right _ (by omega)
    exact tail_spec sp sc ph pl wP ch cl wC hsp hsc hP1 hP2 hP20 hC2 hC20 hw hwP hord
  · rw [ite_eq_right hf]
    have h : ¬ (wC.toNat < wP.toNat ∨ (wP.toNat = wC.toNat ∧ ¬ pair ph pl < pair ch cl)) :=
      fun h' => hf (hcond.mpr h')
    have hw : wP.toNat ≤ wC.toNat := by omega
    have hord : pair ph pl * 2 ^ wP.toNat ≤ pair ch cl * 2 ^ wC.toNat := by
      rcases lt_or_eq_of_le hw with h1 | h1
      · exact (scale_order _ _ _ _ hC1 hP2 h1).le
      · rw [h1]; exact Nat.mul_le_mul_right _ (by omega)
    rw [tail_spec sc sp ch cl wC ph pl wP hsc hsp hC1 hC2 hC20 hP2 hP20 hw hwC hord, add_comm]

#print axioms round_sum
#print axioms tail_spec
#print axioms combine_spec

end Library.Numerics.Arithmetic.Fma.FmaCombine
