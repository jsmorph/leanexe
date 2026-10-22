import Library.Numerics.Float64.Tgamma.TgammaLarge
import LeanExe.ProofKit.F64Sterbenz
import LeanExe.ProofKit.GammaBasic

/-!
The first steps of the path of `tgammaWith` from `-184` to `-3`.  `fastTwoSum (-x) 1` is the exact
pair `1 - x`, whose high part lies from `4` to `186` and whose low part is below `2 ^ -44`
(`refl_front`), the range of `TgammaAsym6.asLgammaAsym_spec`.  `x - floorF x` is the fractional
part of `x`, exactly, by Sterbenz's lemma (`refl_dx`).  The parity of `-floorF x` that the code
tests gives the sign of `Γ x` (`refl_odd`), and `Γ x` is `± π/(sin (π d) Γ (1 - x))` for the
fractional part `d` (`refl_gamma`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaRefl1
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaFloor

set_option exponentiation.threshold 4096

/-- **`1 - x`** as `fastTwoSum (-x) 1`. -/
theorem refl_front (x : Float) (hx : Finite x.toBits) (h1 : -184 < value x.toBits)
    (h2 : value x.toBits < -3) :
    Finite (fastTwoSum (-x) 1.0).1.toBits ∧ Finite (fastTwoSum (-x) 1.0).2.toBits ∧
      value (fastTwoSum (-x) 1.0).1.toBits + value (fastTwoSum (-x) 1.0).2.toBits =
        1 - value x.toBits ∧
      |value (fastTwoSum (-x) 1.0).2.toBits| ≤ 1 / 2 ^ 44 ∧
      4 ≤ value (fastTwoSum (-x) 1.0).1.toBits ∧ value (fastTwoSum (-x) 1.0).1.toBits ≤ 186 := by
  obtain ⟨hnf, hnv⟩ := neg_float x hx
  have hone := TgammaRecip.one_value
  have honef := TgammaRecip.one_finite
  have hxa : |value (-x).toBits| = -value x.toBits := by
    rw [hnv, abs_neg, abs_of_neg (by linarith)]
  obtain ⟨hsf, hlf, hsum, hlb1, hlb2⟩ := fastTwoSum_spec (-x) 1.0 hnf honef
    (by rw [hone, abs_one, hxa]; linarith) (by rw [hxa]; linarith)
  rw [hnv, hone] at hsum
  rw [hone, abs_one] at hlb1
  have hs1 : (fastTwoSum (-x) 1.0).1.toBits =
      Wasm.IEEE64.add (-x).toBits (1.0 : Float).toBits := by
    simp only [fastTwoSum, F64Bits.toBits_add]
  have hr := F64RoundNearest.add_rounded (-x).toBits (1.0 : Float).toBits hnf honef
    (by rw [hnv, hone]; intro h; linarith)
    (by rw [hnv, hone, abs_of_pos (show (0 : ℝ) < -value x.toBits + 1 by linarith)]; linarith)
  rw [← hs1, hnv, hone] at hr
  obtain ⟨-, -, hsg, hnear⟩ := hr
  have hpos := F64TwoSum.value_nonneg_of_sign _ (hsg (by linarith))
  have h4w : value (0x4010000000000000 : UInt64) = 4 := by
    rw [TgammaSpecial.lit_value _ 4 (by decide +kernel)]
    norm_num
  have h4 := hnear 0x4010000000000000
  rw [h4w, abs_of_nonneg hpos, abs_of_pos (by linarith : (0 : ℝ) < -value x.toBits + 1),
    abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_neg (by linarith : 4 - (-value x.toBits + 1) < 0)] at h4
  have h4' := (abs_le.mp h4).1
  have hhi : value (fastTwoSum (-x) 1.0).1.toBits ≤ 186 := by
    linarith [(abs_le.mp hlb1).1]
  refine ⟨hsf, hlf, by linarith, ?_, by linarith, hhi⟩
  have : |value (fastTwoSum (-x) 1.0).1.toBits| ≤ 186 := abs_le.mpr ⟨by linarith, hhi⟩
  linarith [(by norm_num : (186 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 44)]

/-- **The fractional part** `x - floorF x`. -/
theorem refl_dx (x : Float) (hx : Finite x.toBits) (h1 : -184 < value x.toBits)
    (h2 : value x.toBits < -3) (hint : ∀ n : ℤ, value x.toBits ≠ n) :
    Finite (floorF x).toBits ∧ value (floorF x).toBits = ⌊value x.toBits⌋ ∧
      Finite (x - floorF x).toBits ∧ value (x - floorF x).toBits = Int.fract (value x.toBits) ∧
      0 < Int.fract (value x.toBits) ∧ Int.fract (value x.toBits) < 1 := by
  obtain ⟨hff, hfv⟩ := floorF_spec x hx
    (by rw [abs_of_neg (show value x.toBits < 0 by linarith)]; linarith)
  have hfl1 : (⌊value x.toBits⌋ : ℝ) ≤ value x.toBits := Int.floor_le _
  have hfl2 : value x.toBits < ⌊value x.toBits⌋ + 1 := Int.lt_floor_add_one _
  have hfr : 0 < Int.fract (value x.toBits) :=
    Int.fract_pos.mpr (hint ⌊value x.toBits⌋)
  have hfr1 : Int.fract (value x.toBits) < 1 := Int.fract_lt_one _
  have hfd : Int.fract (value x.toBits) = value x.toBits - ⌊value x.toBits⌋ :=
    (Int.self_sub_floor _).symm
  have hb : |value (floorF x).toBits| = -(⌊value x.toBits⌋ : ℝ) := by
    rw [hfv, abs_of_neg (show (⌊value x.toBits⌋ : ℝ) < 0 by linarith)]
  have hd : |value x.toBits - value (floorF x).toBits| = Int.fract (value x.toBits) := by
    rw [hfv, ← hfd, abs_of_pos hfr]
  obtain ⟨hsf, hsv⟩ := F64Sterbenz.sub_exact x.toBits (floorF x).toBits hx hff
    (by rw [hd, abs_of_neg (show value x.toBits < 0 by linarith)]; linarith)
    (by rw [hd, hb]; linarith)
    (by rw [hb]; linarith [(by norm_num : (185 : ℝ) < 2 ^ 1021)])
  rw [← F64Bits.toBits_sub] at hsf hsv
  refine ⟨hff, hfv, hsf, ?_, hfr, hfr1⟩
  rw [hsv, hfv, hfd]

/-- The parity test of the code is the parity of `⌊x⌋`. -/
theorem refl_odd (x : Float) (hx : Finite x.toBits) (h1 : -184 < value x.toBits)
    (h2 : value x.toBits < -3) :
    ((-floorF x).toUInt64 &&& 1 == 1) = decide (Odd ⌊value x.toBits⌋) := by
  obtain ⟨hff, hfv⟩ := floorF_spec x hx
    (by rw [abs_of_neg (show value x.toBits < 0 by linarith)]; linarith)
  obtain ⟨hnf, hnv⟩ := neg_float _ hff
  have hfl1 : (⌊value x.toBits⌋ : ℝ) ≤ value x.toBits := Int.floor_le _
  have hfl2 : value x.toBits < ⌊value x.toBits⌋ + 1 := Int.lt_floor_add_one _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = -⌊value x.toBits⌋ :=
    ⟨(-⌊value x.toBits⌋).toNat, Int.toNat_of_nonneg (by
      have : (⌊value x.toBits⌋ : ℝ) < 0 := by linarith
      have : ⌊value x.toBits⌋ < 0 := by exact_mod_cast this
      omega)⟩
  have hN184 : N < 185 := by
    have h3 : (-185 : ℝ) < ⌊value x.toBits⌋ := by linarith
    have : (-185 : ℤ) < ⌊value x.toBits⌋ := by exact_mod_cast h3
    omega
  have hNv : value (-floorF x).toBits = N := by
    rw [hnv, hfv]
    have : ((N : ℤ) : ℝ) = -(⌊value x.toBits⌋ : ℝ) := by rw [hN]; push_cast; ring
    push_cast at this
    linarith
  rw [TgammaMainRed.toUInt64_nat _ N hnf hNv (by omega)]
  have hodd : Odd ⌊value x.toBits⌋ ↔ N % 2 = 1 := by
    rw [show ⌊value x.toBits⌋ = -(N : ℤ) by omega, odd_neg, Int.odd_coe_nat, Nat.odd_iff]
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hand : (UInt64.ofNat N &&& 1).toNat = N % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_ofNat_of_lt' (by omega)]
    exact Nat.and_one_is_mod N
  by_cases h : N % 2 = 1
  · have : (UInt64.ofNat N &&& 1) = 1 := UInt64.toNat_inj.mp (by rw [hand, h]; rfl)
    rw [this, decide_eq_true (hodd.mpr h)]
    rfl
  · have h0 : N % 2 = 0 := by omega
    have : (UInt64.ofNat N &&& 1) = 0 := UInt64.toNat_inj.mp (by rw [hand, h0]; rfl)
    rw [this, decide_eq_false (fun ho => h (hodd.mp ho))]
    rfl

/-- **The reflection** with the sign of `Γ x` from the parity of `⌊x⌋`. -/
theorem refl_gamma (x : ℝ) (hint : ∀ n : ℤ, x ≠ n) :
    Real.Gamma x = (if Odd ⌊x⌋ then -1 else 1) *
      (Real.pi / (Real.sin (Real.pi * Int.fract x) * Real.Gamma (1 - x))) := by
  rw [GammaBasic.gamma_reflect hint, GammaBasic.sin_pi_eq x]
  split_ifs with ho
  · rw [ho.neg_one_zpow, neg_one_mul, neg_mul, div_neg]
    ring
  · rw [(Int.not_odd_iff_even.mp ho).neg_one_zpow]
    ring

#print axioms refl_front
#print axioms refl_dx
#print axioms refl_odd
#print axioms refl_gamma

end Library.Numerics.Float64.Tgamma.TgammaRefl1
