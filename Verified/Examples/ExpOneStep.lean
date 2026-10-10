import Verified.Examples.ExpCoreRange
import LeanExe.ProofKit.F64FullStep
import LeanExe.ProofKit.F64Magnitude

/-!
One representable step for a reconstruction of `exp`.  Let `E` lie in the range that table
entry `j` gives in the binade of `2 ^ q`, and let `P` be within `(7/5) u 2 ^ q H j` of `E`, where
`H j` is the table head.  A word that is either finite with value `P`, or positive infinity with
`2 ^ 1024 ≤ P`, lies within one step of the nonnegative nearest-even reference of `E`.
-/

namespace Verified.Examples.ExpOneStep
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64NearestBinade F64PositiveOrder F64FullStep
  F64Magnitude

set_option exponentiation.threshold 4096

/-- The range of `exp x` from the reduction `k = 128 q + j`, for `abs x ≤ 768`. -/
theorem target_bounds (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) (k q : Int)
    (j : Fin 128) (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) :
    (j.val ≠ 0 → (2 : ℝ) ^ q * (1 + 1 / 4096) ≤ Real.exp (value x) ∧
        Real.exp (value x) ≤ (2 : ℝ) ^ q * (2 - 1 / 65536)) ∧
      (j.val = 0 → (2 : ℝ) ^ q * (319 / 320) ≤ Real.exp (value x) ∧
        Real.exp (value x) ≤ (2 : ℝ) ^ q * (257 / 256)) := by
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  refine ⟨fun hj0 => ExpCoreRange.target_binade x k q j hxf hx hkv hk hj0, ?_⟩
  intro hj0
  have hf := ExpCoreRange.target_factor x k q j hkv hk
  rw [hj0] at hf
  simp only [Nat.cast_zero, zero_mul, zero_div, Real.exp_zero, mul_one] at hf
  have ha := ExpCoreRange.ideal_exponential_range x hxf hx
  rw [hf]
  exact ⟨mul_le_mul_of_nonneg_left ha.1 hQ.le, mul_le_mul_of_nonneg_left ha.2 hQ.le⟩

theorem one_step_of_error (E P : ℝ) (c : UInt64) (q : Int) (j : Fin 128)
    (hq : -1022 ≤ q)
    (hEn : j.val ≠ 0 →
      (2 : ℝ) ^ q * (1 + 1 / 4096) ≤ E ∧ E ≤ (2 : ℝ) ^ q * (2 - 1 / 65536))
    (hEz : j.val = 0 → (2 : ℝ) ^ q * (319 / 320) ≤ E ∧ E ≤ (2 : ℝ) ^ q * (257 / 256))
    (herr : |P - E| ≤
      (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)))
    (hc : (c.toNat < limit ∧ value c = P) ∨
      (c = F64PositiveRounding.positiveInfinity ∧ (2 : ℝ) ^ 1024 ≤ P)) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven E).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven E).toNat ≤ c.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hH := ExpCoreRange.head_bounds j
  have hthr : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
  have h970 : (0 : ℝ) < 2 ^ 970 := by positivity
  by_cases hov : c = F64PositiveRounding.positiveInfinity ∧
      F64PositiveRounding.overflowThreshold ≤ E
  · rw [F64PositiveRounding.reference_overflow E hov.2, hov.1]
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  have hcfin : F64PositiveRounding.overflowThreshold ≤ E → c.toNat < limit := by
    intro hE
    rcases hc with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd ⟨h, hE⟩ hov
  have hdist : |value c - E| ≤ |P - E| := by
    rcases hc with ⟨_, hv⟩ | ⟨hci, hPi⟩
    · rw [hv]
    · have hEt : E < F64PositiveRounding.overflowThreshold := by
        by_contra h
        exact hov ⟨hci, le_of_not_gt h⟩
      have hvi : value c = (2 : ℝ) ^ 1024 := by
        rw [hci]
        exact infinity_value
      rw [hvi, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hc63 : c.toNat < 2 ^ 63 := by
    rcases hc with ⟨h, _⟩ | ⟨h, _⟩
    · exact h.trans hlim
    · rw [h]
      decide
  have hcv := abs_le.mp (hdist.trans herr)
  obtain ⟨e, hei⟩ : ∃ e : Nat, (e : Int) = q + 1023 :=
    ⟨(q + 1023).toNat, Int.toNat_of_nonneg (by omega)⟩
  by_cases hj : j.val = 0
  · obtain ⟨hEl, hEu⟩ := hEz hj
    have hH1 : value (ExpTableBounds.headBits j.val) = 1 := by
      rw [hj]
      exact ExpCoreRange.zero_entry.1
    rw [hH1, mul_one, hu] at hcv
    have hq' : q ≤ 1024 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (1025 : Int) ≤ (2 : ℝ) ^ q :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hp' : (2 : ℝ) ^ (1025 : Int) = 2 * (2 : ℝ) ^ 1024 := by norm_num
      have hcf := hcfin (by rw [hthr]; nlinarith)
      have hlt := finite_below_overflow c hcf
      nlinarith
    have hva : value (UInt64.ofNat ((e - 1) * 2 ^ 52)) ≤ (2 : ℝ) ^ q / 2 := by
      by_cases he1 : e = 1
      · have hz : (e - 1) * 2 ^ 52 = 0 := by rw [he1]; norm_num
        have h0 : Wasm.IEEE64.scaledValue (UInt64.ofNat 0) = 0 := by decide
        rw [hz, value, h0]
        simp only [Int.cast_zero, zero_div]
        positivity
      · exact le_of_eq (by
          rw [boundary_power (e - 1) (q - 1) (by omega) (by omega) (by omega),
            zpow_sub₀ (by norm_num), zpow_one])
    have hgap : (2 : ℝ) ^ q / (2 : ℝ) ^ 53 ≤ (2 : ℝ) ^ (e - 1 - 1) / (2 : ℝ) ^ 1074 := by
      by_cases he1 : e = 1
      · have hq1 : q = -1022 := by omega
        rw [he1, hq1]
        norm_num
      · exact le_of_eq (power_quotient_split (e - 1 - 1) 53 q (by omega)).symm
    have he : |value c - E| < 3 * ((2 : ℝ) ^ (e - 1 - 1) / (2 : ℝ) ^ 1074) / 2 := by
      have hd := hdist.trans herr
      rw [hH1, mul_one, hu] at hd
      have hs : (7 / 5 : ℝ) * (1 / 2 ^ 53) * 2 ^ q < 3 * (2 ^ q / 2 ^ 53) / 2 := by
        have : (0 : ℝ) < 2 ^ q / 2 ^ 53 := by positivity
        nlinarith
      linarith
    rcases (show q ≤ 1023 ∨ q = 1024 by omega) with hq3 | hq3
    · have hvb : value (UInt64.ofNat ((e + 1) * 2 ^ 52)) = 2 * (2 : ℝ) ^ q := by
        rw [boundary_power (e + 1) (q + 1) (by omega) (by omega) (by push_cast; omega),
          zpow_add₀ (by norm_num), zpow_one]
        ring
      refine one_step_binades E c (e - 1) (e + 1) (by omega) (by omega)
        (hva.trans (by linarith)) (fun _ => by rw [hvb]; linarith) hc63
        (hva.trans (by linarith)) (by rw [hvb]; linarith) he
    · have he2047 : e = 2047 := by omega
      have hvb : value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ 1024 := by
        rw [he2047]
        exact infinity_value
      have hcb : value c ≤ (2 : ℝ) ^ 1024 := by
        rcases hc with ⟨h, _⟩ | ⟨h, _⟩
        · exact (finite_below_overflow c h).le
        · rw [h]
          exact infinity_value.le
      refine one_step_binades E c (e - 1) e (by omega) (by omega)
        (hva.trans (by linarith)) (fun h => absurd h (by omega)) hc63
        (hva.trans (by linarith)) (by rw [hvb]; exact hcb) he
  · obtain ⟨hEl, hEu⟩ := hEn hj
    have hHb : (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) ≤ (2 : ℝ) ^ q * (255 / 128) :=
      mul_le_mul_of_nonneg_left hH.1 hQ.le
    have hd := hdist.trans herr
    rw [hu] at hd
    have hd' : |value c - E| ≤ (7 / 5) * (1 / (2 : ℝ) ^ 53) * ((2 : ℝ) ^ q * (255 / 128)) :=
      hd.trans (mul_le_mul_of_nonneg_left hHb (by positivity))
    have hcv' := abs_le.mp hd'
    have hq' : q ≤ 1023 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (1024 : Int) ≤ (2 : ℝ) ^ q :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hp' : (2 : ℝ) ^ (1024 : Int) = (2 : ℝ) ^ 1024 := by norm_num
      have hcf := hcfin (by rw [hthr]; nlinarith)
      have hlt := finite_below_overflow c hcf
      nlinarith
    have hva : value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ q :=
      boundary_power e q (by omega) (by omega) hei
    have hvb : value (UInt64.ofNat ((e + 1) * 2 ^ 52)) = 2 * (2 : ℝ) ^ q := by
      rw [boundary_power (e + 1) (q + 1) (by omega) (by omega) (by push_cast; omega),
        zpow_add₀ (by norm_num), zpow_one]
      ring
    have hgap : (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 = (2 : ℝ) ^ q / (2 : ℝ) ^ 52 :=
      power_quotient_split (e - 1) 52 q (by omega)
    have he : |value c - E| < 3 * ((2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074) / 2 := by
      rw [hgap]
      have hs : (7 / 5 : ℝ) * (1 / 2 ^ 53) * (2 ^ q * (255 / 128)) < 3 * (2 ^ q / 2 ^ 52) / 2 := by
        have : (0 : ℝ) < 2 ^ q / 2 ^ 53 := by positivity
        nlinarith
      linarith
    refine one_step_binades E c e (e + 1) (by omega) (by omega) (by rw [hva]; linarith)
      (fun _ => by rw [hvb]; linarith) hc63 (by rw [hva]; linarith) (by rw [hvb]; linarith) he

#print axioms target_bounds
#print axioms one_step_of_error

end Verified.Examples.ExpOneStep
