import Verified.Examples.TrigLargeFloat
import Verified.Examples.TrigDistance
import LeanExe.ProofKit.F64Magnitude
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The accuracy of `Trig.remLarge`.  For a positive finite double `x` with exponent field from 1043
on, the remainder `y0 + y1` lies within `2 ^ -72` relative of `x - N π/2` for an integer `N` with
`N mod 4` the returned count, and that remainder is at least `2 ^ -62` and at most
`π/4 + 2 ^ -130` in magnitude.
-/

namespace Verified.Examples.TrigLarge

open CodeLib.IEEE64 LeanExe.ProofKit TrigLargeInt TrigLargeFloat TrigPi

/-- The truncated normalization and the truncated product with `π/2` lose at most 3 units. -/
theorem product_error (B : Nat) (hB : B < 2 ^ 192) :
    |(((B / 2 ^ 64) * halfNum / 2 ^ 128 : Nat) : ℝ) - Real.pi * B / 2 ^ 66| ≤ 3 := by
  obtain ⟨hh1, hh2⟩ := half_bounds
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  generalize hT : B / 2 ^ 64 = T
  have hT1 : (T : ℝ) ≤ B / 2 ^ 64 := by
    have h := Nat.cast_div_le (α := ℝ) (m := B) (n := 2 ^ 64)
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    rw [← hT]
    exact h
  have hT2 : (B : ℝ) / 2 ^ 64 < T + 1 := by
    have h := Nat.lt_div_mul_add (a := B) (show 0 < 2 ^ 64 by positivity)
    rw [hT] at h
    have h' : (B : ℝ) < T * 2 ^ 64 + 2 ^ 64 := by exact_mod_cast h
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hU1 : (((T * halfNum) / 2 ^ 128 : Nat) : ℝ) ≤ (T : ℝ) * halfNum / 2 ^ 128 := by
    have h := Nat.cast_div_le (α := ℝ) (m := T * halfNum) (n := 2 ^ 128)
    rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] at h
    exact h
  have hU2 : (T : ℝ) * halfNum / 2 ^ 128 < (((T * halfNum) / 2 ^ 128 : Nat) : ℝ) + 1 := by
    have h := Nat.lt_div_mul_add (a := T * halfNum) (show 0 < 2 ^ 128 by positivity)
    have h' : ((T * halfNum : Nat) : ℝ) <
        (((T * halfNum) / 2 ^ 128 : Nat) : ℝ) * 2 ^ 128 + 2 ^ 128 := by exact_mod_cast h
    rw [Nat.cast_mul] at h'
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hB' : (B : ℝ) < 2 ^ 192 := by exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hHnn : (0 : ℝ) ≤ Real.pi * 2 ^ 126 - 1 := by nlinarith [Real.pi_gt_three]
  have hlow : ((B : ℝ) / 2 ^ 64 - 1) * (Real.pi * 2 ^ 126 - 1) ≤ (T : ℝ) * halfNum := by
    calc ((B : ℝ) / 2 ^ 64 - 1) * (Real.pi * 2 ^ 126 - 1)
        ≤ (T : ℝ) * (Real.pi * 2 ^ 126 - 1) := mul_le_mul_of_nonneg_right (by linarith) hHnn
      _ ≤ (T : ℝ) * halfNum := mul_le_mul_of_nonneg_left (by linarith) hT0
  have hhigh : (T : ℝ) * halfNum ≤ (B : ℝ) / 2 ^ 64 * (Real.pi * 2 ^ 126) :=
    mul_le_mul hT1 hh1 (Nat.cast_nonneg _) (by positivity)
  have hBB : (B : ℝ) / 2 ^ 64 < 2 ^ 128 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  rw [abs_le]
  constructor
  · have hexp : ((B : ℝ) / 2 ^ 64 - 1) * (Real.pi * 2 ^ 126 - 1) =
        Real.pi * B * 2 ^ 62 - (B : ℝ) / 2 ^ 64 - Real.pi * 2 ^ 126 + 1 := by ring
    have h1 : Real.pi * 2 ^ 126 < 2 ^ 128 := by nlinarith
    have h2 : Real.pi * B * 2 ^ 62 - 2 ^ 129 < (T : ℝ) * halfNum := by nlinarith
    have h3 : Real.pi * B / 2 ^ 66 - 2 < (T : ℝ) * halfNum / 2 ^ 128 := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    linarith
  · have h1 : (T : ℝ) * halfNum / 2 ^ 128 ≤ Real.pi * B / 2 ^ 66 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- The words `hi` and `lo` hold all but the low `k - 41` bits of `U`. -/
theorem cut_value (U k hi lo : Nat) (hk : k = 62 ∨ k = 63) (hhi : hi = U / 2 ^ (k + 12))
    (hlo : lo = U / 2 ^ (k - 41) % 2 ^ 53) (hU : U < 2 ^ 128) :
    (hi * 2 ^ 53 + lo) * 2 ^ (k - 41) ≤ U ∧ U < (hi * 2 ^ 53 + lo) * 2 ^ (k - 41) + 2 ^ (k - 41) := by
  rcases hk with hk | hk <;> subst hk <;> subst hhi <;> subst hlo <;>
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reducePow] at hU ⊢ <;> omega

/-- The window of `2/π` from bit `g` on gives `M · X` as the low 192 bits `V` of the product,
plus multiples of `2 ^ 1280`, plus the part below the window. -/
theorem quadrant_split (M X : Nat) : ∃ K : Nat,
    M * X = (M * (X / 2 ^ 1088 % 2 ^ 192) % 2 ^ 192 + 2 ^ 192 * K) * 2 ^ 1088 +
      M * (X % 2 ^ 1088) := by
  refine ⟨M * (X / 2 ^ 1088 % 2 ^ 192) / 2 ^ 192 + M * (X / 2 ^ 1088 / 2 ^ 192), ?_⟩
  generalize hZf : X / 2 ^ 1088 = Zf
  have hX : X = Zf * 2 ^ 1088 + X % 2 ^ 1088 := by
    rw [← hZf]
    exact (Nat.div_add_mod' X _).symm
  have hZ : Zf = Zf / 2 ^ 192 * 2 ^ 192 + Zf % 2 ^ 192 := (Nat.div_add_mod' Zf _).symm
  have hMZ : M * (Zf % 2 ^ 192) = M * (Zf % 2 ^ 192) / 2 ^ 192 * 2 ^ 192 +
      M * (Zf % 2 ^ 192) % 2 ^ 192 := (Nat.div_add_mod' _ _).symm
  generalize Zf / 2 ^ 192 = Q at hZ ⊢
  generalize Zf % 2 ^ 192 = Z at hZ hMZ ⊢
  generalize M * Z / 2 ^ 192 = C1 at hMZ ⊢
  generalize M * Z % 2 ^ 192 = V at hMZ ⊢
  generalize X % 2 ^ 1088 = Xr at hX ⊢
  subst hX
  rw [hZ]
  have e : M * ((Q * 2 ^ 192 + Z) * 2 ^ 1088 + Xr) =
      M * Z * 2 ^ 1088 + M * Q * 2 ^ 192 * 2 ^ 1088 + M * Xr := by ring
  rw [e, hMZ]
  ring

theorem halfNum_lt : halfNum < 2 ^ 128 := by decide

/-- The remainder `S` formed from `hi` and `lo` lies within `2 ^ -103` relative of `(π/2) ρ`,
`ρ = A / 2 ^ 190`. -/
theorem remainder_scale (A lz U k hi lo : Nat) (hlz1 : 2 ^ 191 ≤ A * 2 ^ lz)
    (hlz2 : A * 2 ^ lz < 2 ^ 192) (hU : U = A * 2 ^ lz / 2 ^ 64 * halfNum / 2 ^ 128)
    (hk : k = 62 ∨ k = 63) (hhi : hi = U / 2 ^ (k + 12)) (hlo : lo = U / 2 ^ (k - 41) % 2 ^ 53)
    (hlzk : lz ≤ k + 908) :
    |((hi : ℝ) * 2 ^ 53 + lo) * 2 ^ (k + 908 - lz) / 2 ^ 1074 - Real.pi / 2 * (A / 2 ^ 190)| ≤
      Real.pi / 2 * (A / 2 ^ 190) / 2 ^ 103 := by
  have hpe := product_error (A * 2 ^ lz) hlz2
  rw [← hU] at hpe
  have hUlt : U < 2 ^ 128 := by
    rw [hU]
    have hT : A * 2 ^ lz / 2 ^ 64 < 2 ^ 128 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc A * 2 ^ lz < 2 ^ 192 := hlz2
        _ = 2 ^ 128 * 2 ^ 64 := by norm_num
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc A * 2 ^ lz / 2 ^ 64 * halfNum < 2 ^ 128 * 2 ^ 128 :=
          Nat.mul_lt_mul'' hT halfNum_lt
      _ = 2 ^ 128 * 2 ^ 128 := rfl
  obtain ⟨hc1, hc2⟩ := cut_value U k hi lo hk hhi hlo hUlt
  have hk41 : 41 ≤ k := by omega
  have hk63 : k ≤ 63 := by omega
  generalize hD : hi * 2 ^ 53 + lo = D at hc1 hc2
  have hDr : (hi : ℝ) * 2 ^ 53 + lo = D := by rw [← hD]; push_cast; ring
  rw [hDr]
  have hexp : (k + 908 - lz) + (lz + 125) = (k - 41) + 1074 := by omega
  have hS : (D : ℝ) * 2 ^ (k + 908 - lz) / 2 ^ 1074 * 2 ^ (lz + 125) = D * 2 ^ (k - 41) := by
    rw [div_mul_eq_mul_div, mul_assoc, ← pow_add, hexp, pow_add]
    field_simp
  have hT : Real.pi / 2 * (A / 2 ^ 190) * 2 ^ (lz + 125) = Real.pi * (A * 2 ^ lz : Nat) / 2 ^ 66 := by
    push_cast
    rw [pow_add]
    field_simp
  have hc1' : (D : ℝ) * 2 ^ (k - 41) ≤ U := by exact_mod_cast hc1
  have hc2' : (U : ℝ) < D * 2 ^ (k - 41) + 2 ^ (k - 41) := by exact_mod_cast hc2
  have hpk : (2 : ℝ) ^ (k - 41) ≤ 2 ^ 22 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hB : (2 : ℝ) ^ 191 ≤ ((A * 2 ^ lz : Nat) : ℝ) := by exact_mod_cast hlz1
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hbig : 3 * 2 ^ 125 ≤ Real.pi * (A * 2 ^ lz : Nat) / 2 ^ 66 := by
    rw [le_div_iff₀ (by positivity)]
    have e : (3 : ℝ) * 2 ^ 125 * 2 ^ 66 = 3 * 2 ^ 191 := by rw [mul_assoc, ← pow_add]
    rw [e]
    calc (3 : ℝ) * 2 ^ 191 ≤ Real.pi * 2 ^ 191 :=
          mul_le_mul_of_nonneg_right hpi.le (by positivity)
      _ ≤ Real.pi * ((A * 2 ^ lz : Nat) : ℝ) := mul_le_mul_of_nonneg_left hB Real.pi_pos.le
  have hP : (0 : ℝ) < 2 ^ (lz + 125) := by positivity
  set X := Real.pi * (A * 2 ^ lz : Nat) / 2 ^ 66 with hX
  set Sv := (D : ℝ) * 2 ^ (k + 908 - lz) / 2 ^ 1074 with hSv
  set Tv := Real.pi / 2 * (A / 2 ^ 190) with hTv
  have h22 : (2 : ℝ) ^ 22 + 3 ≤ X / 2 ^ 103 := by
    rw [le_div_iff₀ (by positivity)]
    have : ((2 : ℝ) ^ 22 + 3) * 2 ^ 103 ≤ 3 * 2 ^ 125 := by norm_num
    linarith
  have hmain : |Sv * 2 ^ (lz + 125) - Tv * 2 ^ (lz + 125)| ≤ X / 2 ^ 103 := by
    rw [hS, hT]
    rw [abs_le] at hpe ⊢
    constructor <;> linarith
  have key : |Sv - Tv| * 2 ^ (lz + 125) ≤ Tv / 2 ^ 103 * 2 ^ (lz + 125) := by
    have e1 : |Sv - Tv| * 2 ^ (lz + 125) = |Sv * 2 ^ (lz + 125) - Tv * 2 ^ (lz + 125)| := by
      rw [← sub_mul, abs_mul, abs_of_pos hP]
    have e2 : Tv / 2 ^ 103 * 2 ^ (lz + 125) = X / 2 ^ 103 := by
      rw [← hT]
      ring
    rw [e1, e2]
    exact hmain
  exact le_of_mul_le_mul_right key hP

/-- The quadrant identity: `x · 2/π` is `4 K + V / 2 ^ 190` plus less than `2 ^ -136`. -/
theorem quadrant_value (M E V K Xr : Nat) (hM : M < 2 ^ 53) (hE1 : 1013 ≤ E) (hE2 : E ≤ 2046)
    (hsplit : M * (tableNum * 2 ^ (E - 1013)) = (V + 2 ^ 192 * K) * 2 ^ 1088 + M * Xr)
    (hXr : Xr < 2 ^ 1088) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 / 2 ^ 136 ∧
      (M : ℝ) * 2 ^ E / 2 ^ 1075 * (2 / Real.pi) = 4 * K + (V : ℝ) / 2 ^ 190 + t := by
  obtain ⟨hlo, hhi⟩ := table_bounds
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsr : (M : ℝ) * (tableNum * 2 ^ (E - 1013)) = ((V : ℝ) + 2 ^ 192 * K) * 2 ^ 1088 + M * Xr := by
    exact_mod_cast hsplit
  have hE : (2 : ℝ) ^ E = 2 ^ (E - 1013) * 2 ^ 1013 := by
    rw [← pow_add, Nat.sub_add_cancel hE1]
  set d := (M : ℝ) * 2 ^ E / 2 ^ 1075 * (2 / Real.pi - tableNum / 2 ^ 1216) with hd
  have hd0 : 0 ≤ 2 / Real.pi - (tableNum : ℝ) / 2 ^ 1216 := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    linarith
  refine ⟨(M : ℝ) * Xr / 2 ^ 1278 + d, ?_, ?_, ?_⟩
  · exact add_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (by positivity)) (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (by positivity)) hd0)
  · have hM' : (M : ℝ) < 2 ^ 53 := by exact_mod_cast hM
    have hX' : (Xr : ℝ) < 2 ^ 1088 := by exact_mod_cast hXr
    have h1 : (M : ℝ) * Xr / 2 ^ 1278 < 1 / 2 ^ 137 := by
      have hlt : (M : ℝ) * Xr < 2 ^ 53 * 2 ^ 1088 :=
        mul_lt_mul'' hM' hX' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hq : (2 : ℝ) ^ 53 * 2 ^ 1088 / 2 ^ 1278 = 1 / 2 ^ 137 := by
        rw [← pow_add, div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
      rw [← hq]
      exact div_lt_div_of_pos_right hlt (by positivity)
    have h2 : d < 1 / 2 ^ 137 := by
      have hf : 2 / Real.pi - (tableNum : ℝ) / 2 ^ 1216 < 1 / 2 ^ 1216 := by
        have : 2 / Real.pi * 2 ^ 1216 - tableNum < 1 := by linarith
        rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ (by positivity)]
        linarith
      have hEx : (2 : ℝ) ^ E ≤ 2 ^ 2046 := pow_le_pow_right₀ (by norm_num) hE2
      have hMx : (M : ℝ) * 2 ^ E / 2 ^ 1075 ≤ 2 ^ 53 * 2 ^ 2046 / 2 ^ 1075 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul hM'.le hEx (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
      have hq : (2 : ℝ) ^ 53 * 2 ^ 2046 / 2 ^ 1075 * (1 / 2 ^ 1216) = 1 / 2 ^ 192 := by
        rw [← pow_add, div_mul_div_comm, mul_one, ← pow_add, div_eq_div_iff (by positivity)
          (by positivity), one_mul, ← pow_add]
      calc d ≤ (2 : ℝ) ^ 53 * 2 ^ 2046 / 2 ^ 1075 * (1 / 2 ^ 1216) := by
            rw [hd]
            exact mul_le_mul hMx hf.le hd0 (by positivity)
        _ = 1 / 2 ^ 192 := hq
        _ < 1 / 2 ^ 137 := by
            apply one_div_lt_one_div_of_lt (by positivity)
            exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    have h3 : (1 : ℝ) / 2 ^ 137 + 1 / 2 ^ 137 = 1 / 2 ^ 136 := by norm_num
    linarith
  · have hT : (M : ℝ) * 2 ^ E / 2 ^ 1075 * ((tableNum : ℝ) / 2 ^ 1216) =
        (M * (tableNum * 2 ^ (E - 1013)) : ℝ) / 2 ^ 1278 := by
      rw [hE]
      field_simp
    have h2 : (M : ℝ) * 2 ^ E / 2 ^ 1075 * (2 / Real.pi) =
        (M : ℝ) * 2 ^ E / 2 ^ 1075 * ((tableNum : ℝ) / 2 ^ 1216) + d := by
      rw [hd]
      ring
    rw [h2, hT, hsr]
    field_simp
    ring

/-- The bounds of the reduction from the quadrant fraction: with `u = ±ρ + t` the distance of
`x · 2/π` from the chosen multiple, `S` within `2 ^ -103` relative of `(π/2) ρ` lies within
`2 ^ -72` relative of `(π/2) u`. -/
theorem core_bounds (u ρ t S : ℝ) (up : Bool) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) (ht0 : 0 ≤ t)
    (ht1 : t < 1 / 2 ^ 136) (hu : u = (if up then -ρ else ρ) + t) (hdist : 1 / 2 ^ 63 < |u|)
    (hS : |S - Real.pi / 2 * ρ| ≤ Real.pi / 2 * ρ / 2 ^ 103) :
    |(if up then -S else S) - Real.pi / 2 * u| ≤ |Real.pi / 2 * u| / 2 ^ 72 ∧
      1 / 2 ^ 63 ≤ |Real.pi / 2 * u| ∧ |Real.pi / 2 * u| ≤ Real.pi / 4 + 1 / 2 ^ 134 := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hp2 : 0 < Real.pi / 2 := by linarith
  have h136 : (1 : ℝ) / 2 ^ 136 = 1 / 2 ^ 63 * (1 / 2 ^ 73) := by norm_num
  have hpos73 : (0 : ℝ) < 1 / 2 ^ 73 := by norm_num
  rw [abs_le] at hS
  cases up with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hu ⊢
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    rw [abs_of_nonneg hu0] at hdist
    have hpu : 0 ≤ Real.pi / 2 * u := by positivity
    rw [abs_of_nonneg hpu]
    have htu : t ≤ u * (1 / 2 ^ 73) := by nlinarith
    have hρu : ρ ≤ u := by rw [hu]; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> nlinarith
    · nlinarith
    · have h1 : Real.pi / 2 * t ≤ 1 / 2 ^ 134 := by
        have h2 : Real.pi / 2 * t ≤ 2 * (1 / 2 ^ 136) :=
          mul_le_mul (by linarith) ht1.le ht0 (by norm_num)
        have h3 : (2 : ℝ) * (1 / 2 ^ 136) ≤ 1 / 2 ^ 134 := by norm_num
        linarith
      have h2 : Real.pi / 2 * ρ ≤ Real.pi / 4 := by nlinarith
      rw [hu, mul_add]
      linarith
  | true =>
    simp only [ite_true] at hu ⊢
    have hun : u < 0 := by
      by_contra h
      have hu0 : 0 ≤ u := le_of_not_gt h
      rw [abs_of_nonneg hu0] at hdist
      have : u ≤ t := by rw [hu]; linarith
      have : (1 : ℝ) / 2 ^ 136 < 1 / 2 ^ 63 := by norm_num
      linarith
    rw [abs_of_neg hun] at hdist
    have hpu : Real.pi / 2 * u < 0 := mul_neg_of_pos_of_neg hp2 hun
    rw [abs_of_neg hpu]
    have htu : t ≤ -u * (1 / 2 ^ 73) := by nlinarith
    have hρu : ρ ≤ -u + t := by rw [hu]; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> nlinarith
    · nlinarith
    · have h1 : -u ≤ ρ := by rw [hu]; linarith
      have h2 : Real.pi / 2 * ρ ≤ Real.pi / 4 := by nlinarith
      have h3 : -(Real.pi / 2 * u) ≤ Real.pi / 2 * ρ := by nlinarith
      have h4 : (0 : ℝ) < 1 / 2 ^ 134 := by norm_num
      linarith

#print axioms core_bounds
#print axioms remainder_scale
#print axioms quadrant_value
#print axioms product_error
#print axioms cut_value
#print axioms quadrant_split

end Verified.Examples.TrigLarge
