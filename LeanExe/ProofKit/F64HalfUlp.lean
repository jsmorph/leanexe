import LeanExe.ProofKit.F64Approx
import LeanExe.ProofKit.F64RoundingScale

/-!
The rounding error of a sum or difference is at most half the spacing of the binade below the
bound of the exact result: when `|a + b| < 2 ^ (53 + g)` scaled units, the rounded sum lies within
`2 ^ g / 2` scaled units.  The relative bound of `F64AddBounds` charges up to a whole spacing at the
top of a binade.  `fapprox_add_half` and `fapprox_sub_half` carry the bound through `FApprox`.
-/

namespace LeanExe.ProofKit.F64HalfUlp
open CodeLib.IEEE64 F64Approx

set_option exponentiation.threshold 4096

theorem add_half (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : ℕ) (hg : g ≤ 1023)
    (hS : |value a + value b| < 2 ^ (53 + g) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ 2 ^ g / 2 / 2 ^ 1074 := by
  set S := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b with hSdef
  have hSv : value a + value b = (S : ℝ) / 2 ^ 1074 := by
    simp only [value, hSdef]
    push_cast
    ring
  have hcast : |(S : ℝ)| = (S.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hSabs : S.natAbs < 2 ^ (53 + g) := by
    rw [hSv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      div_lt_div_iff_of_pos_right (by positivity), hcast] at hS
    exact_mod_cast hS
  by_cases hS0 : S = 0
  · have hz : value a + value b = 0 := by rw [hSv, hS0]; simp
    have hr := F64AddBounds.add_real_relative a b ha hb (by rw [hz]; norm_num)
    rw [hz, abs_zero, mul_zero] at hr
    refine ⟨hr.1, ?_⟩
    rw [hz]
    exact hr.2.trans (by positivity)
  · set n := S.natAbs with hn
    have hmax : n < 2 ^ 1076 :=
      lt_of_lt_of_le hSabs (Nat.pow_le_pow_right (by norm_num) (by omega))
    have heq : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) n := by
      have hne : (S == 0) = false := by simpa using hS0
      simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
        ite_false, ← hSdef, hne]
      rfl
    have hspec := roundScaledMagnitude_spec (decide (S < 0)) n hmax
    have hsign := sign_roundScaledMagnitude (decide (S < 0)) n hmax
    have herr := F64Packing.roundedMagnitude_error n
    have hn0 : n ≠ 0 := by simpa [hn] using hS0
    have hlog : Nat.log2 n - 52 ≤ g := by
      have := (Nat.log2_lt hn0).mpr hSabs
      omega
    have hpow : (2 : ℝ) ^ (Nat.log2 n - 52) ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) hlog
    rw [heq]
    refine ⟨hspec.1, ?_⟩
    have hsv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) n) =
        if S < 0 then -(roundedMagnitude n : Int) else (roundedMagnitude n : Int) := by
      simp only [Wasm.IEEE64.scaledValue, hspec.2.1, hsign, decide_eq_true_eq]
    have hdiff : |value (Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) n) -
        (S : ℝ) / 2 ^ 1074| = |(roundedMagnitude n : ℝ) - n| / 2 ^ 1074 := by
      rw [value, hsv]
      rcases lt_or_ge S 0 with hneg | hpos
      · have hSn : (S : ℝ) = -(n : ℝ) := by
          rw [hn]
          have : (S.natAbs : Int) = -S := Int.ofNat_natAbs_of_nonpos hneg.le
          have h2 : ((S.natAbs : Int) : ℝ) = ((-S : Int) : ℝ) := by rw [this]
          push_cast at h2
          linarith
        rw [if_pos hneg, hSn]
        push_cast
        rw [show -(roundedMagnitude n : ℝ) / 2 ^ 1074 - -(n : ℝ) / 2 ^ 1074 =
          -(((roundedMagnitude n : ℝ) - n) / 2 ^ 1074) by ring, abs_neg, abs_div,
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
      · have hSn : (S : ℝ) = (n : ℝ) := by
          rw [hn]
          have : (S.natAbs : Int) = S := Int.natAbs_of_nonneg hpos
          have h2 : ((S.natAbs : Int) : ℝ) = ((S : Int) : ℝ) := by rw [this]
          push_cast at h2
          linarith
        rw [if_neg (not_lt.mpr hpos), hSn]
        push_cast
        rw [show (roundedMagnitude n : ℝ) / 2 ^ 1074 - (n : ℝ) / 2 ^ 1074 =
          ((roundedMagnitude n : ℝ) - n) / 2 ^ 1074 by ring, abs_div,
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    rw [hSv, hdiff]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact herr.trans (by linarith)

theorem sub_half (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : ℕ) (hg : g ≤ 1023)
    (hS : |value a - value b| < 2 ^ (53 + g) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.sub a b) ∧
      |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ 2 ^ g / 2 / 2 ^ 1074 := by
  have hn := F64Magnitude.negate_value b hb
  have h := add_half a (Wasm.IEEE64.negate b) ha hn.1 g hg (by rw [hn.2, ← sub_eq_add_neg]; exact hS)
  rw [hn.2, ← sub_eq_add_neg] at h
  exact h

theorem fapprox_add_half {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (g : ℕ) (hg : g ≤ 1023)
    (hS : |va + vb| + (ea + eb) < 2 ^ (53 + g) / 2 ^ 1074) :
    FApprox (a + b) (va + vb) (ea + eb + 2 ^ g / 2 / 2 ^ 1074) := by
  unfold FApprox at *
  rw [F64Bits.toBits_add]
  have hsum : |(value a.toBits + value b.toBits) - (va + vb)| ≤ ea + eb := by
    rw [show (value a.toBits + value b.toBits) - (va + vb) =
      (value a.toBits - va) + (value b.toBits - vb) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.2 hb.2)
  have hm : |value a.toBits + value b.toBits| < 2 ^ (53 + g) / 2 ^ 1074 := by
    have := abs_sub_abs_le_abs_sub (value a.toBits + value b.toBits) (va + vb)
    linarith
  have hr := add_half a.toBits b.toBits ha.1 hb.1 g hg hm
  refine ⟨hr.1, ?_⟩
  have := abs_sub_le (value (Wasm.IEEE64.add a.toBits b.toBits))
    (value a.toBits + value b.toBits) (va + vb)
  linarith

theorem fapprox_sub_half {a b : Float} {va vb ea eb : ℝ} (ha : FApprox a va ea)
    (hb : FApprox b vb eb) (g : ℕ) (hg : g ≤ 1023)
    (hS : |va - vb| + (ea + eb) < 2 ^ (53 + g) / 2 ^ 1074) :
    FApprox (a - b) (va - vb) (ea + eb + 2 ^ g / 2 / 2 ^ 1074) := by
  unfold FApprox at *
  rw [F64Bits.toBits_sub]
  have hdiff : |(value a.toBits - value b.toBits) - (va - vb)| ≤ ea + eb := by
    rw [show (value a.toBits - value b.toBits) - (va - vb) =
      (value a.toBits - va) + -(value b.toBits - vb) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.2 (by rw [abs_neg]; exact hb.2))
  have hm : |value a.toBits - value b.toBits| < 2 ^ (53 + g) / 2 ^ 1074 := by
    have := abs_sub_abs_le_abs_sub (value a.toBits - value b.toBits) (va - vb)
    linarith
  have hr := sub_half a.toBits b.toBits ha.1 hb.1 g hg hm
  refine ⟨hr.1, ?_⟩
  have := abs_sub_le (value (Wasm.IEEE64.sub a.toBits b.toBits))
    (value a.toBits - value b.toBits) (va - vb)
  linarith

#print axioms add_half
#print axioms sub_half
#print axioms fapprox_add_half
#print axioms fapprox_sub_half

end LeanExe.ProofKit.F64HalfUlp
