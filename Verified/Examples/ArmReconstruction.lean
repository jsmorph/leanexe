import Verified.Examples.ExpOneStep
import Verified.Examples.ExpTableBounds
import LeanExe.ProofKit.F64SignedRounding

/-!
The reconstruction `s + s · w` shared by Arm's `exp2` and `exp10`, for any polynomial word `w`.
Let `s` hold `2 ^ (q + d) H j`, `t` the table tail `T j`, and `ρ` the real factor that `w`
approximates as `T + ρ - 1`, within `2 ^ -56`.  Then `s + s · w` lies within `(6/5) u s` of
`s (1 + T) ρ`, which lies within `s / 2 ^ 98` of `2 ^ d E` for `E = 2 ^ q exp (j log 2 / 128) ρ`.
For `319/320 ≤ ρ ≤ 257/256`, `E` lies in the range that `ExpOneStep.one_step_of_error` needs,
so the ordinary reconstruction (`d = 0`) lies within one step of the reference of `E`.
-/

namespace Verified.Examples.ArmReconstruction
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative

set_option exponentiation.threshold 4096

/-- The scaled sum before its final rounding. -/
theorem presum_general (s w : UInt64) (T ρ : ℝ) (hsf : Finite s) (hwf : Finite w)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1023)
    (hW : |value w| ≤ 1 / 64) (hWe : |value w - (T + ρ - 1)| ≤ 1 / 2 ^ 56)
    (hρ : |ρ - 1| ≤ 1 / 128) (hT : |T| ≤ 1 / 2 ^ 53) :
    Finite (Wasm.IEEE64.mul s w) ∧
    |value (Wasm.IEEE64.mul s w)| ≤ value s / 32 ∧
    |value s + value (Wasm.IEEE64.mul s w) - value s * (1 + T) * ρ| ≤
      (21 / 128) * unitRoundoff64 * value s := by
  set S := value s
  set W := value w
  set p := Wasm.IEEE64.mul s w
  set P := value p
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ unitRoundoff64 := by rw [hu]; positivity
  have hprod : |S * W| ≤ S / 64 := by
    rw [abs_mul, abs_of_pos hS]
    calc
      _ ≤ S * (1 / 64) := mul_le_mul_of_nonneg_left hW hS.le
      _ = S / 64 := by ring
  have hprodMax : |S * W| < (2 : ℝ) ^ 1022 := by
    calc
      _ ≤ S / 64 := hprod
      _ ≤ (2 : ℝ) ^ 1023 / 64 := div_le_div_of_nonneg_right hshi (by norm_num)
      _ < (2 : ℝ) ^ 1022 := by norm_num
  have hm := F64MulBounds.mul_real_mixed s w hsf hwf hprodMax
  have hbeta : multiplicationUnderflowEpsilon ≤ unitRoundoff64 * S / 64 := by
    calc
      _ ≤ unitRoundoff64 * (1 / (2 : ℝ) ^ 1000) / 64 := by
        norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
      _ ≤ unitRoundoff64 * S / 64 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hslo hu0) (by norm_num)
  have hme : |P - S * W| ≤ unitRoundoff64 * S / 32 := by
    calc
      _ ≤ unitRoundoff64 * |S * W| + multiplicationUnderflowEpsilon := hm.2
      _ ≤ unitRoundoff64 * (S / 64) + unitRoundoff64 * S / 64 :=
        add_le_add (mul_le_mul_of_nonneg_left hprod hu0) hbeta
      _ = unitRoundoff64 * S / 32 := by ring
  have hPm : |P| ≤ S / 32 := by
    have := abs_sub_abs_le_abs_sub P (S * W)
    have hus : unitRoundoff64 * S / 32 ≤ S / 64 := by
      rw [hu]
      nlinarith only [hS]
    linarith
  have hinner : |S + P - (S + S * (T + ρ - 1))| ≤
      unitRoundoff64 * S / 32 + S * (1 / 2 ^ 56) := by
    calc
      _ = |(P - S * W) + S * (W - (T + ρ - 1))| := by congr 1; ring
      _ ≤ |P - S * W| + |S * (W - (T + ρ - 1))| := abs_add_le _ _
      _ = |P - S * W| + S * |W - (T + ρ - 1)| := by rw [abs_mul, abs_of_pos hS]
      _ ≤ _ := add_le_add hme (mul_le_mul_of_nonneg_left hWe hS.le)
  have hcross : |(S + S * (T + ρ - 1)) - S * (1 + T) * ρ| ≤
      S * (unitRoundoff64 / 128) := by
    calc
      _ = |S * T * (ρ - 1)| := by
        rw [show (S + S * (T + ρ - 1)) - S * (1 + T) * ρ = -(S * T * (ρ - 1)) by ring, abs_neg]
      _ = S * |T| * |ρ - 1| := by rw [abs_mul, abs_mul, abs_of_pos hS]
      _ ≤ S * unitRoundoff64 * (1 / 128) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by rw [hu]; exact hT) hS.le) hρ (abs_nonneg _)
          (mul_nonneg hS.le hu0)
      _ = S * (unitRoundoff64 / 128) := by ring
  refine ⟨hm.1, hPm, ?_⟩
  calc
    _ ≤ |S + P - (S + S * (T + ρ - 1))| + |(S + S * (T + ρ - 1)) - S * (1 + T) * ρ| :=
      abs_sub_le _ _ _
    _ ≤ (unitRoundoff64 * S / 32 + S * (1 / 2 ^ 56)) + S * (unitRoundoff64 / 128) :=
      add_le_add hinner hcross
    _ = (21 / 128) * unitRoundoff64 * S := by rw [hu]; ring

/-- The rounded scaled sum, when it stays below `2 ^ 1023`. -/
theorem reconstruction_general (s w : UInt64) (T ρ : ℝ) (hsf : Finite s) (hwf : Finite w)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1023)
    (hW : |value w| ≤ 1 / 64) (hWe : |value w - (T + ρ - 1)| ≤ 1 / 2 ^ 56)
    (hρ : |ρ - 1| ≤ 1 / 128) (hT : |T| ≤ 1 / 2 ^ 53)
    (hfit : value s * (1 + T) * ρ + value s / 2 ^ 50 < (2 : ℝ) ^ 1023) :
    Finite (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) ∧
      |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) - value s * (1 + T) * ρ| ≤
        (6 / 5) * unitRoundoff64 * value s := by
  obtain ⟨hpf, hPm, hpre⟩ := presum_general s w T ρ hsf hwf hslo hshi hW hWe hρ hT
  set S := value s
  set p := Wasm.IEEE64.mul s w
  set P := value p
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ unitRoundoff64 := by rw [hu]; positivity
  have hsum : |S + P| ≤ (33 / 32) * S := by
    calc
      _ ≤ |S| + |P| := abs_add_le S P
      _ ≤ S + S / 32 := by rw [abs_of_pos hS]; exact add_le_add le_rfl hPm
      _ = (33 / 32) * S := by ring
  have hsumMax : |S + P| < (2 : ℝ) ^ 1023 := by
    have hpos : 0 ≤ S + P := by
      have := (abs_le.mp hPm).1
      linarith
    rw [abs_of_nonneg hpos]
    have h1 := (abs_le.mp hpre).2
    have h2 : (21 / 128) * unitRoundoff64 * S ≤ S / 2 ^ 50 := by
      rw [hu]
      nlinarith only [hS]
    linarith
  have ha := F64AddBounds.add_real_relative s p hsf hpf hsumMax
  refine ⟨ha.1, ?_⟩
  calc
    _ ≤ |value (Wasm.IEEE64.add s p) - (S + P)| + |S + P - S * (1 + T) * ρ| := abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * ((33 / 32) * S) + (21 / 128) * unitRoundoff64 * S :=
      add_le_add (ha.2.trans (mul_le_mul_of_nonneg_left hsum hu0)) hpre
    _ ≤ (6 / 5) * unitRoundoff64 * S := by
      have : 0 ≤ unitRoundoff64 * S := mul_nonneg hu0 hS.le
      nlinarith only [this]

/-- The table factor: `2 ^ (q + d) H j (1 + T j) ρ` against `2 ^ (q + d) exp (j log 2 / 128) ρ`. -/
theorem table_general (s : UInt64) (q d : Int) (j : Fin 128) (ρ : ℝ)
    (hs : value s = (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val))
    (hρ0 : 0 < ρ) (hρ : ρ ≤ 257 / 256) :
    |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ -
        (2 : ℝ) ^ d * ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)| ≤
      value s / 2 ^ 98 := by
  have hb := ExpTableBounds.entry_bounds j
  have he := ExpTableBounds.scale_error j
  have hQ : (0 : ℝ) < (2 : ℝ) ^ (q + d) := zpow_pos (by norm_num) _
  have hH : 1 ≤ value (ExpTableBounds.headBits j.val) := hb.2.2.1
  have hT := hb.2.2.2.2
  have hsc : ExpTableBounds.scale j.val ≤ value (ExpTableBounds.headBits j.val) * (2 : ℝ) := by
    rw [ExpTableBounds.scale]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have := (abs_le.mp hT).2
    linarith [show (1 : ℝ) / 2 ^ 53 ≤ 1 by norm_num]
  have hzq : (2 : ℝ) ^ d * (2 : ℝ) ^ q = (2 : ℝ) ^ (q + d) := by
    rw [← zpow_add₀ (by norm_num), add_comm]
  have hid : value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ -
      (2 : ℝ) ^ d * ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ) =
      (2 : ℝ) ^ (q + d) * ρ *
        (ExpTableBounds.scale j.val - Real.exp ((j.val : ℝ) * Real.log 2 / 128)) := by
    rw [hs, ExpTableBounds.scale, ← hzq]
    ring
  have hsc0 : 0 ≤ ExpTableBounds.scale j.val := by
    rw [ExpTableBounds.scale]
    apply mul_nonneg (by linarith)
    have := (abs_le.mp hT).1
    linarith [show (1 : ℝ) / 2 ^ 53 ≤ 1 by norm_num]
  rw [hid, abs_mul, abs_of_pos (mul_pos hQ hρ0)]
  calc
    _ ≤ (2 : ℝ) ^ (q + d) * ρ * (ExpTableBounds.scale j.val / 2 ^ 100) :=
      mul_le_mul_of_nonneg_left he (mul_pos hQ hρ0).le
    _ ≤ (2 : ℝ) ^ (q + d) * (257 / 256) *
          (value (ExpTableBounds.headBits j.val) * 2 / 2 ^ 100) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hρ hQ.le)
        (div_le_div_of_nonneg_right hsc (by norm_num)) (div_nonneg hsc0 (by norm_num))
        (by positivity)
    _ ≤ value s / 2 ^ 98 := by
      rw [hs]
      have : 0 ≤ (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val) :=
        mul_nonneg hQ.le (by linarith)
      nlinarith only [this]

/-- The target `E = 2 ^ q exp (j log 2 / 128) ρ` lies in the range of table entry `j` in the
binade of `2 ^ q`. -/
theorem target_range (q : Int) (j : Fin 128) (ρ : ℝ) (hρl : 319 / 320 ≤ ρ)
    (hρu : ρ ≤ 257 / 256) :
    (j.val ≠ 0 →
      (2 : ℝ) ^ q * (1 + 1 / 4096) ≤
          (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ ∧
        (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ ≤
          (2 : ℝ) ^ q * (2 - 1 / 65536)) ∧
    (j.val = 0 →
      (2 : ℝ) ^ q * (319 / 320) ≤ (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ ∧
        (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ ≤ (2 : ℝ) ^ q * (257 / 256)) := by
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hX := Real.exp_pos ((j.val : ℝ) * Real.log 2 / 128)
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · obtain ⟨h1, h2⟩ := ExpCoreRange.table_exponential_range j hj
    rw [mul_assoc]
    constructor
    · apply mul_le_mul_of_nonneg_left _ hQ.le
      calc
        _ ≤ Real.exp ((j.val : ℝ) * Real.log 2 / 128) * (319 / 320) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left hρl hX.le
    · apply mul_le_mul_of_nonneg_left _ hQ.le
      calc
        _ ≤ Real.exp ((j.val : ℝ) * Real.log 2 / 128) * (257 / 256) :=
          mul_le_mul_of_nonneg_left hρu hX.le
        _ ≤ _ := h2
  · rw [hj]
    simp only [Nat.cast_zero, zero_mul, zero_div, Real.exp_zero, mul_one]
    exact ⟨mul_le_mul_of_nonneg_left hρl hQ.le, mul_le_mul_of_nonneg_left hρu hQ.le⟩

/-- The ordinary reconstruction `s + s · w` with `s = 2 ^ q H j` lies within one step of the
reference of `E`. -/
theorem ordinary_within (s w : UInt64) (q : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val))
    (hqlo : -1000 ≤ q) (hqhi : q ≤ 1020)
    (hW : |value w| ≤ 1 / 64)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ 1 / 2 ^ 56)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256) :
    F64SignedRounding.WithinSteps 1
      ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)
      (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) := by
  obtain ⟨hEn, hEz⟩ := target_range q j ρ hρl hρu
  set E := (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ with hEdef
  have hb := ExpTableBounds.entry_bounds j
  have hH1 : 1 ≤ value (ExpTableBounds.headBits j.val) := hb.2.2.1
  have hH2 : value (ExpTableBounds.headBits j.val) ≤ 2 := hb.2.2.2.1
  have hT := hb.2.2.2.2
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hρ : |ρ - 1| ≤ 1 / 128 := by
    rw [abs_le]
    constructor <;> linarith
  have hQlo : 1 / (2 : ℝ) ^ 1000 ≤ (2 : ℝ) ^ q := by
    have h : (2 : ℝ) ^ (-((1000 : Nat) : Int)) ≤ (2 : ℝ) ^ q :=
      zpow_le_zpow_right₀ (by norm_num) hqlo
    simpa only [zpow_neg, zpow_natCast, inv_eq_one_div] using h
  have hQhi : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ 1020 := by
    have h : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ ((1020 : Nat) : Int) :=
      zpow_le_zpow_right₀ (by norm_num) hqhi
    simpa only [zpow_natCast] using h
  have hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s := by
    rw [hs]
    nlinarith only [hQlo, hH1, hQ]
  have hshi : value s ≤ (2 : ℝ) ^ 1021 := by
    rw [hs]
    calc
      _ ≤ (2 : ℝ) ^ 1020 * 2 := mul_le_mul hQhi hH2 (by linarith) (by positivity)
      _ = _ := by norm_num
  have hTb : |value (ExpTableBounds.tailBits j.val)| ≤ 1 / 2 ^ 53 := hT
  have hfit : value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ + value s / 2 ^ 50 <
      (2 : ℝ) ^ 1023 := by
    have hs0 : 0 ≤ value s := by linarith [show (0 : ℝ) < 1 / 2 ^ 1000 by positivity]
    have h1 : 1 + value (ExpTableBounds.tailBits j.val) ≤ 2 := by
      have := (abs_le.mp hTb).2
      linarith [show (1 : ℝ) / 2 ^ 53 ≤ 1 by norm_num]
    have hm : value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ ≤
        value s * 2 * (257 / 256) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hs0) hρu (by linarith) (mul_nonneg hs0 (by norm_num))
    have hd : value s / 2 ^ 50 ≤ value s := div_le_self hs0 (by norm_num)
    calc
      _ ≤ value s * 2 * (257 / 256) + value s := add_le_add hm hd
      _ ≤ (2 : ℝ) ^ 1021 * 2 * (257 / 256) + 2 ^ 1021 := by gcongr
      _ < (2 : ℝ) ^ 1023 := by norm_num
  obtain ⟨hcf, hce⟩ := reconstruction_general s w _ ρ hsf hwf hslo (hshi.trans (by norm_num))
    hW hWe hρ hTb hfit
  have htab := table_general s q 0 j ρ (by rw [add_zero]; exact hs)
    (by linarith) hρu
  rw [zpow_zero, one_mul] at htab
  have herr : |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) - E| ≤
      (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
    rw [← hs]
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have hs0 : 0 ≤ value s := by linarith [show (0 : ℝ) < 1 / 2 ^ 1000 by positivity]
    calc
      _ ≤ |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) -
            value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ| +
          |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ - E| := abs_sub_le _ _ _
      _ ≤ (6 / 5) * unitRoundoff64 * value s + value s / 2 ^ 98 := add_le_add hce htab
      _ ≤ _ := by rw [hu]; nlinarith only [hs0]
  have hq : -1022 ≤ q := by omega
  have hc : (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)).toNat < limit ∧
      value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) =
        value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) := by
    refine ⟨?_, rfl⟩
    have hpos : 0 < value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) := by
      have h1 := (abs_le.mp herr).1
      have hE : 0 < E := mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)
      have hH : (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) <
          E := by
        by_cases hj0 : j.val = 0
        · have hz := (hEz hj0).1
          have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
          rw [hu]
          nlinarith only [hz, hQ, hH2]
        · have hn := (hEn hj0).1
          have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
          rw [hu]
          nlinarith only [hn, hQ, hH2]
      linarith
    exact F64PositiveOrder.positive_finite_encoding _ hcf hpos
  have hstep := ExpOneStep.one_step_of_error E _ _ q j hq hEn hEz herr (Or.inl hc)
  have hE0 : 0 ≤ E := (mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)).le
  exact F64SignedRounding.within_of_nonneg 1 E hE0 _ hc.1.le hstep.1 hstep.2

#print axioms presum_general
#print axioms reconstruction_general
#print axioms table_general
#print axioms target_range
#print axioms ordinary_within

end Verified.Examples.ArmReconstruction
