import Library.Numerics.Float64.Exp.ArmSpecial
import Library.Numerics.Float64.Exp.ExpSpecialPositive

/-!
The reconstruction `s + s · w` of Arm's exponential family with a larger allowance for the
polynomial word: `|w| ≤ 1/256` and `|w - (T + ρ - 1)| ≤ (37/100) u`, as `pow` needs, whose
argument carries the error of its logarithm.  The final rounding is then at most
`(1 + 1/128) u s`, and with the table the reconstruction stays within `(7/5) u 2 ^ q H j` of
`2 ^ d E`.  This gives one step for the ordinary reconstruction, for the reconstruction scaled
up by `2 ^ 1009` (with overflow to infinity), and for the scaled-down reconstruction with the
compensated rounding below 1.
-/

namespace Library.Numerics.Float64.Exp.ArmTight
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64Magnitude ExpSpecialNegative

set_option exponentiation.threshold 4096

/-- The allowance for the polynomial word. -/
noncomputable def allowance : ℝ := 37 / 100 / 2 ^ 53

theorem presum_tight (s w : UInt64) (T ρ : ℝ) (hsf : Finite s) (hwf : Finite w)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1023)
    (hW : |value w| ≤ 1 / 256) (hWe : |value w - (T + ρ - 1)| ≤ allowance)
    (hρ : |ρ - 1| ≤ 1 / 256) (hT : |T| ≤ 1 / 2 ^ 53) :
    Finite (Wasm.IEEE64.mul s w) ∧
    |value (Wasm.IEEE64.mul s w)| ≤ value s / 128 ∧
    |value s + value (Wasm.IEEE64.mul s w) - value s * (1 + T) * ρ| ≤
      (3 / 256 / 2 ^ 53 + allowance) * value s := by
  set S := value s
  set W := value w
  set p := Wasm.IEEE64.mul s w
  set P := value p
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ unitRoundoff64 := by rw [hu]; positivity
  have hprod : |S * W| ≤ S / 256 := by
    rw [abs_mul, abs_of_pos hS]
    calc
      _ ≤ S * (1 / 256) := mul_le_mul_of_nonneg_left hW hS.le
      _ = S / 256 := by ring
  have hprodMax : |S * W| < (2 : ℝ) ^ 1022 := by
    calc
      _ ≤ S / 256 := hprod
      _ ≤ (2 : ℝ) ^ 1023 / 256 := div_le_div_of_nonneg_right hshi (by norm_num)
      _ < (2 : ℝ) ^ 1022 := by norm_num
  have hm := F64MulBounds.mul_real_mixed s w hsf hwf hprodMax
  have hbeta : multiplicationUnderflowEpsilon ≤ unitRoundoff64 * S / 256 := by
    calc
      _ ≤ unitRoundoff64 * (1 / (2 : ℝ) ^ 1000) / 256 := by
        norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
      _ ≤ unitRoundoff64 * S / 256 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hslo hu0) (by norm_num)
  have hme : |P - S * W| ≤ unitRoundoff64 * S / 128 := by
    calc
      _ ≤ unitRoundoff64 * |S * W| + multiplicationUnderflowEpsilon := hm.2
      _ ≤ unitRoundoff64 * (S / 256) + unitRoundoff64 * S / 256 :=
        add_le_add (mul_le_mul_of_nonneg_left hprod hu0) hbeta
      _ = unitRoundoff64 * S / 128 := by ring
  have hPm : |P| ≤ S / 128 := by
    have := abs_sub_abs_le_abs_sub P (S * W)
    have hus : unitRoundoff64 * S / 128 ≤ S / 256 := by
      rw [hu]
      nlinarith only [hS]
    linarith
  have hinner : |S + P - (S + S * (T + ρ - 1))| ≤ unitRoundoff64 * S / 128 + S * allowance := by
    calc
      _ = |(P - S * W) + S * (W - (T + ρ - 1))| := by congr 1; ring
      _ ≤ |P - S * W| + |S * (W - (T + ρ - 1))| := abs_add_le _ _
      _ = |P - S * W| + S * |W - (T + ρ - 1)| := by rw [abs_mul, abs_of_pos hS]
      _ ≤ _ := add_le_add hme (mul_le_mul_of_nonneg_left hWe hS.le)
  have hcross : |(S + S * (T + ρ - 1)) - S * (1 + T) * ρ| ≤ S * (unitRoundoff64 / 256) := by
    calc
      _ = |S * T * (ρ - 1)| := by
        rw [show (S + S * (T + ρ - 1)) - S * (1 + T) * ρ = -(S * T * (ρ - 1)) by ring, abs_neg]
      _ = S * |T| * |ρ - 1| := by rw [abs_mul, abs_mul, abs_of_pos hS]
      _ ≤ S * unitRoundoff64 * (1 / 256) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by rw [hu]; exact hT) hS.le) hρ (abs_nonneg _)
          (mul_nonneg hS.le hu0)
      _ = S * (unitRoundoff64 / 256) := by ring
  refine ⟨hm.1, hPm, ?_⟩
  calc
    _ ≤ |S + P - (S + S * (T + ρ - 1))| + |(S + S * (T + ρ - 1)) - S * (1 + T) * ρ| :=
      abs_sub_le _ _ _
    _ ≤ (unitRoundoff64 * S / 128 + S * allowance) + S * (unitRoundoff64 / 256) :=
      add_le_add hinner hcross
    _ = (3 / 256 / 2 ^ 53 + allowance) * S := by rw [hu]; ring

theorem reconstruction_tight (s w : UInt64) (T ρ : ℝ) (hsf : Finite s) (hwf : Finite w)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000)
    (hW : |value w| ≤ 1 / 256) (hWe : |value w - (T + ρ - 1)| ≤ allowance)
    (hρ : |ρ - 1| ≤ 1 / 256) (hT : |T| ≤ 1 / 2 ^ 53) :
    Finite (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) ∧
      |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) - value s * (1 + T) * ρ| ≤
        (1 + 5 / 256) / 2 ^ 53 * value s + allowance * value s := by
  obtain ⟨hpf, hPm, hpre⟩ := presum_tight s w T ρ hsf hwf hslo (hshi.trans (by norm_num)) hW
    hWe hρ hT
  set S := value s
  set p := Wasm.IEEE64.mul s w
  set P := value p
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ unitRoundoff64 := by rw [hu]; positivity
  have hsum : |S + P| ≤ (1 + 1 / 128) * S := by
    calc
      _ ≤ |S| + |P| := abs_add_le S P
      _ ≤ S + S / 128 := by rw [abs_of_pos hS]; exact add_le_add le_rfl hPm
      _ = (1 + 1 / 128) * S := by ring
  have hsumMax : |S + P| < (2 : ℝ) ^ 1023 := by
    calc
      _ ≤ (1 + 1 / 128) * S := hsum
      _ ≤ (1 + 1 / 128) * (2 : ℝ) ^ 1000 := mul_le_mul_of_nonneg_left hshi (by norm_num)
      _ < (2 : ℝ) ^ 1023 := by norm_num
  have ha := F64AddBounds.add_real_relative s p hsf hpf hsumMax
  refine ⟨ha.1, ?_⟩
  calc
    _ ≤ |value (Wasm.IEEE64.add s p) - (S + P)| + |S + P - S * (1 + T) * ρ| := abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * ((1 + 1 / 128) * S) + (3 / 256 / 2 ^ 53 + allowance) * S :=
      add_le_add (ha.2.trans (mul_le_mul_of_nonneg_left hsum hu0)) hpre
    _ = (1 + 5 / 256) / 2 ^ 53 * S + allowance * S := by rw [hu]; ring

/-- The reconstruction against `2 ^ d E`, with the table. -/
theorem reconstruction_target (s w : UInt64) (q d : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val))
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000)
    (hW : |value w| ≤ 1 / 256)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ allowance)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256) :
    Finite (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) ∧
      |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) -
        (2 : ℝ) ^ d * ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)| ≤
        (7 / 5) * unitRoundoff64 * value s := by
  have hb := ExpTableBounds.entry_bounds j
  have hTb : |value (ExpTableBounds.tailBits j.val)| ≤ 1 / 2 ^ 53 := hb.2.2.2.2
  have hρ : |ρ - 1| ≤ 1 / 256 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hcf, hce⟩ := reconstruction_tight s w _ ρ hsf hwf hslo hshi hW hWe hρ hTb
  have htab := ArmReconstruction.table_general s q d j ρ hs (by linarith) hρu
  have hS : 0 ≤ value s := le_trans (by positivity) hslo
  refine ⟨hcf, ?_⟩
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  calc
    _ ≤ |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) -
          value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ| +
        |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ -
          (2 : ℝ) ^ d * ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)| :=
      abs_sub_le _ _ _
    _ ≤ ((1 + 5 / 256) / 2 ^ 53 * value s + allowance * value s) + value s / 2 ^ 98 :=
      add_le_add hce htab
    _ ≤ _ := by
      rw [hu, allowance]
      nlinarith only [hS]

theorem scale_bounds (s : UInt64) (q : Int) (j : Fin 128) (lo : Int)
    (hs : value s = (2 : ℝ) ^ (q + lo) * value (ExpTableBounds.headBits j.val))
    (hqlo : -1000 ≤ q + lo) (hqhi : q + lo ≤ 999) :
    1 / (2 : ℝ) ^ 1000 ≤ value s ∧ value s ≤ (2 : ℝ) ^ 1000 := by
  have hb := ExpTableBounds.entry_bounds j
  have hH1 : 1 ≤ value (ExpTableBounds.headBits j.val) := hb.2.2.1
  have hH2 : value (ExpTableBounds.headBits j.val) ≤ 2 := hb.2.2.2.1
  have hQlo : 1 / (2 : ℝ) ^ 1000 ≤ (2 : ℝ) ^ (q + lo) := by
    have h : (2 : ℝ) ^ (-((1000 : Nat) : Int)) ≤ (2 : ℝ) ^ (q + lo) :=
      zpow_le_zpow_right₀ (by norm_num) hqlo
    simpa only [zpow_neg, zpow_natCast, inv_eq_one_div] using h
  have hQhi : (2 : ℝ) ^ (q + lo) ≤ (2 : ℝ) ^ 999 := by
    have h : (2 : ℝ) ^ (q + lo) ≤ (2 : ℝ) ^ ((999 : Nat) : Int) :=
      zpow_le_zpow_right₀ (by norm_num) hqhi
    simpa only [zpow_natCast] using h
  have hQ : (0 : ℝ) < (2 : ℝ) ^ (q + lo) := zpow_pos (by norm_num) _
  rw [hs]
  constructor
  · nlinarith
  · calc
      _ ≤ (2 : ℝ) ^ 999 * 2 := mul_le_mul hQhi hH2 (by linarith) (by positivity)
      _ = (2 : ℝ) ^ 1000 := by norm_num

/-- The ordinary reconstruction within one step of `E`. -/
theorem ordinary_tight (s w : UInt64) (q : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val))
    (hqlo : -1000 ≤ q) (hqhi : q ≤ 999)
    (hW : |value w| ≤ 1 / 256)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ allowance)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256) :
    F64SignedRounding.WithinSteps 1
      ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)
      (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) := by
  obtain ⟨hEn, hEz⟩ := ArmReconstruction.target_range q j ρ hρl hρu
  have hs0 : value s = (2 : ℝ) ^ (q + 0) * value (ExpTableBounds.headBits j.val) := by
    rw [add_zero]
    exact hs
  obtain ⟨hslo, hshi⟩ := scale_bounds s q j 0 hs0 (by omega) (by omega)
  obtain ⟨hcf, hce⟩ := reconstruction_target s w q 0 j ρ hsf hwf hs0 hslo hshi hW hWe hρl hρu
  rw [zpow_zero, one_mul, hs] at hce
  set E := (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ with hEdef
  have hb := ExpTableBounds.entry_bounds j
  have hH2 : value (ExpTableBounds.headBits j.val) ≤ 2 := hb.2.2.2.1
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hE : 0 < E := mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)
  have hElo : (2 : ℝ) ^ q * (319 / 320) ≤ E := by
    by_cases hj0 : j.val = 0
    · exact (hEz hj0).1
    · have := (hEn hj0).1
      nlinarith
  have hpos : 0 < value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) := by
    have h1 := (abs_le.mp hce).1
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have h2 : (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) ≤ (2 : ℝ) ^ q * 2 :=
      mul_le_mul_of_nonneg_left hH2 hQ.le
    rw [hu] at h1
    linarith
  have hclim := F64PositiveOrder.positive_finite_encoding _ hcf hpos
  have hstep := ExpOneStep.one_step_of_error E _ _ q j (by omega) hEn hEz hce
    (Or.inl ⟨hclim, rfl⟩)
  exact F64SignedRounding.within_of_nonneg 1 E hE.le _ hclim.le hstep.1 hstep.2

/-- Multiplication of finite words is commutative. -/
theorem mul_comm_finite (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.mul b a := by
  have hfin : ∀ x : UInt64, Finite x →
      Wasm.IEEE64.isNaN x = false ∧ Wasm.IEEE64.isInfinite x = false := by
    intro x hx
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hx
    simp [Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite, hx]
  obtain ⟨hna, hia⟩ := hfin a ha
  obtain ⟨hnb, hib⟩ := hfin b hb
  have hs : (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) =
      (Wasm.IEEE64.sign b != Wasm.IEEE64.sign a) := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
  simp only [Wasm.IEEE64.mul, hna, hnb, hia, hib, hs, Bool.or_false, Bool.false_eq_true,
    ite_false, Bool.or_comm (Wasm.IEEE64.scaledMagnitude a == 0),
    Nat.mul_comm (Wasm.IEEE64.scaledMagnitude a)]

/-- The reconstruction scaled up by `2 ^ 1009`, with overflow to infinity. -/
theorem positive1009_tight (s w : UInt64) (q : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val))
    (hqlo : 9 ≤ q) (hqhi : q ≤ 2008)
    (hW : |value w| ≤ 1 / 256)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ allowance)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256) :
    F64SignedRounding.WithinSteps 1
      ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)
      (Wasm.IEEE64.mul (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) 0x7F00000000000000) := by
  obtain ⟨hEn, hEz⟩ := ArmReconstruction.target_range q j ρ hρl hρu
  have hs' : value s = (2 : ℝ) ^ (q + -1009) * value (ExpTableBounds.headBits j.val) := by
    rw [← sub_eq_add_neg]
    exact hs
  obtain ⟨hslo, hshi⟩ := scale_bounds s q j (-1009) hs' (by omega) (by omega)
  obtain ⟨hYf, hYe⟩ := reconstruction_target s w q (-1009) j ρ hsf hwf hs' hslo hshi hW hWe
    hρl hρu
  set E := (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ with hEdef
  set Y := Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)
  rw [mul_comm_finite Y 0x7F00000000000000 hYf (by unfold CodeLib.IEEE64.Finite; decide)]
  rw [hs] at hYe
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hH := ExpCoreRange.head_bounds j
  have hE : 0 < E := mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)
  have hElo : (2 : ℝ) ^ q * (319 / 320) ≤ E := by
    by_cases hj0 : j.val = 0
    · exact (hEz hj0).1
    · have := (hEn hj0).1
      nlinarith
  set P := (2 : ℝ) ^ (1009 : Int) * value Y with hPdef
  have h1009 : (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (-1009 : Int) = 1 := by
    rw [← zpow_add₀ (by norm_num), show (1009 : Int) + -1009 = 0 by norm_num, zpow_zero]
  have hq1009 : (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (q - 1009) = (2 : ℝ) ^ q := by
    rw [← zpow_add₀ (by norm_num), show (1009 : Int) + (q - 1009) = q by ring]
  have herr : |P - E| ≤
      (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
    have hPE : P - E = (2 : ℝ) ^ (1009 : Int) * (value Y - (2 : ℝ) ^ (-1009 : Int) * E) := by
      rw [hPdef, mul_sub, ← mul_assoc, h1009, one_mul]
    rw [hPE, abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
    calc
      _ ≤ (2 : ℝ) ^ (1009 : Int) * ((7 / 5) * unitRoundoff64 *
          ((2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val))) :=
        mul_le_mul_of_nonneg_left hYe (by positivity)
      _ = _ := by
        rw [← hq1009]
        ring
  have hYv : 1 / (2 : ℝ) ^ 1022 < value Y := by
    have hR : (2 : ℝ) ^ (-1009 : Int) * (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1009) := by
      rw [← zpow_add₀ (by norm_num), show (-1009 : Int) + q = q - 1009 by ring]
    have hRlo : (2 : ℝ) ^ (-1000 : Int) ≤ (2 : ℝ) ^ (q - 1009) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hp1000 : (2 : ℝ) ^ (-1000 : Int) = 1 / (2 : ℝ) ^ 1000 := by norm_num
    have hm : (2 : ℝ) ^ (q - 1009) * (319 / 320) ≤ (2 : ℝ) ^ (-1009 : Int) * E := by
      rw [← hR, mul_assoc]
      exact mul_le_mul_of_nonneg_left hElo (by positivity)
    have hHb : (2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val) ≤
        (2 : ℝ) ^ (q - 1009) * (255 / 128) :=
      mul_le_mul_of_nonneg_left hH.1 (by positivity)
    have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
    have hYe' := (abs_le.mp hYe).1
    rw [hu] at hYe'
    have h1022 : (1 : ℝ) / 2 ^ 1022 < 1 / 2 ^ 1000 / 2 := by norm_num
    nlinarith
  obtain ⟨hYe1, hYs⟩ := normal_of_value Y hYv
  have hsum : 1024 ≤ Wasm.IEEE64.exponent Y + 2032 := by omega
  have hc : ((Wasm.IEEE64.mul 0x7F00000000000000 Y).toNat < limit ∧
        value (Wasm.IEEE64.mul 0x7F00000000000000 Y) = P) ∨
      (Wasm.IEEE64.mul 0x7F00000000000000 Y = F64PositiveRounding.positiveInfinity ∧
        (2 : ℝ) ^ 1024 ≤ P) := by
    rw [ExpSpecialPositive.scale_up_word]
    by_cases hov : 0x7FF ≤ Wasm.IEEE64.exponent Y + 2032 - 1023
    · right
      rw [F64PowerScale.mul_power_overflow 2032 Y (by norm_num) (by norm_num) hYf hYe1
        hsum hov, hYs, ExpSpecialPositive.infinity_word]
      refine ⟨rfl, ?_⟩
      have hv := value_ge_of_exponent Y 1038 15 (by norm_num) (by norm_num) (by norm_num)
        hYs (by omega)
      have hp : (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (15 : Int) = (2 : ℝ) ^ 1024 := by
        rw [← zpow_add₀ (by norm_num), show (1009 : Int) + 15 = ((1024 : Nat) : Int) by norm_num,
          zpow_natCast]
      calc
        (2 : ℝ) ^ 1024 = (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (15 : Int) := hp.symm
        _ ≤ P := by rw [hPdef]; exact mul_le_mul_of_nonneg_left hv (by positivity)
    · left
      obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 2032 Y (by norm_num)
        (by norm_num) hYf hYe1 hsum (by omega)
      have hcv' : value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 2032 0) Y) = P := by
        rw [hPdef, hcv, show ((2032 : Nat) : Int) - 1023 = 1009 by norm_num]
      refine ⟨F64PositiveOrder.positive_finite_encoding _ hcf ?_, hcv'⟩
      rw [hcv', hPdef]
      exact mul_pos (zpow_pos (by norm_num) _) (by linarith)
  have hstep := ExpOneStep.one_step_of_error E P _ q j (by omega) hEn hEz herr hc
  have hclim : (Wasm.IEEE64.mul 0x7F00000000000000 Y).toNat ≤ 0x7FF0000000000000 := by
    rcases hc with ⟨h, _⟩ | ⟨h, _⟩
    · exact h.le
    · rw [h]
      decide
  exact F64SignedRounding.within_of_nonneg 1 E hE.le _ hclim hstep.1 hstep.2

/-- The scaled-down reconstruction, with the compensated rounding below 1. -/
theorem negative_tight (s w : UInt64) (q : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ (q + 1022) * value (ExpTableBounds.headBits j.val))
    (hqlo : -2022 ≤ q) (hqhi : q ≤ -23)
    (hW : |value w| ≤ 1 / 256)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ allowance)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256) :
    F64SignedRounding.WithinSteps 1
      ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)
      (Wasm.IEEE64.mul 0x0010000000000000
        (if Wasm.IEEE64.lt (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) one then
          compRounded (compSum s (Wasm.IEEE64.mul s w))
        else Wasm.IEEE64.add s (Wasm.IEEE64.mul s w))) := by
  obtain ⟨hEn, hEz⟩ := ArmReconstruction.target_range q j ρ hρl hρu
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 < unitRoundoff64 := by rw [hu]; positivity
  have hb := ExpTableBounds.entry_bounds j
  have hH1 : 1 ≤ value (ExpTableBounds.headBits j.val) := hb.2.2.1
  have hH : value (ExpTableBounds.headBits j.val) ≤ 255 / 128 := (ExpCoreRange.head_bounds j).1
  have hTb : |value (ExpTableBounds.tailBits j.val)| ≤ 1 / 2 ^ 53 := hb.2.2.2.2
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hρ : |ρ - 1| ≤ 1 / 256 := by
    rw [abs_le]
    constructor <;> linarith
  have hR : (0 : ℝ) < (2 : ℝ) ^ (q + 1022) := zpow_pos (by norm_num) _
  have hS : 0 < value s := by rw [hs]; exact mul_pos hR (by linarith)
  obtain ⟨hslo, hshi⟩ := scale_bounds s q j 1022 hs (by omega) (by omega)
  obtain ⟨hpf, hPm, hpre0⟩ := presum_tight s w _ ρ hsf hwf hslo (hshi.trans (by norm_num)) hW
    hWe hρ hTb
  have htab := ArmReconstruction.table_general s q 1022 j ρ hs (by linarith) hρu
  set E := (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ with hEdef
  obtain ⟨hyf, hye⟩ := reconstruction_target s w q 1022 j ρ hsf hwf hs hslo hshi hW hWe hρl hρu
  generalize hp : Wasm.IEEE64.mul s w = p at *
  have hE : 0 < E := mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)
  have hlt := lt_one_iff _ hyf
  by_cases hy1 : value (Wasm.IEEE64.add s p) < 1
  · rw [hlt, decide_eq_true hy1, ite_eq_left rfl]
    -- `s < 9/8`, since the rounded sum is below 1
    have hsumMax : |value s + value p| < (2 : ℝ) ^ 1023 := by
      have := abs_add_le (value s) (value p)
      rw [abs_of_pos hS] at this
      have : value s ≤ (2 : ℝ) ^ 1000 := hshi
      linarith [show (2 : ℝ) ^ 1000 + 2 ^ 1000 / 128 < 2 ^ 1023 by norm_num]
    have ha := F64AddBounds.add_real_relative s p hsf hpf hsumMax
    have hS98 : value s ≤ 9 / 8 := by
      have h1 := (abs_le.mp ha.2).1
      have h2 := (abs_le.mp hPm).1
      have hpos : 0 ≤ value s + value p := by linarith
      rw [abs_of_nonneg hpos, hu] at h1
      nlinarith
    have hpre' : |value s + value p - (2 : ℝ) ^ (1022 : Int) * E| ≤ 11 / 16 * unitRoundoff64 := by
      rw [allowance] at hpre0
      calc
        _ ≤ |value s + value p - value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ| +
            |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ -
              (2 : ℝ) ^ (1022 : Int) * E| := abs_sub_le _ _ _
        _ ≤ (3 / 256 / 2 ^ 53 + 37 / 100 / 2 ^ 53) * value s + value s / 2 ^ 98 :=
          add_le_add hpre0 htab
        _ ≤ (3 / 256 / 2 ^ 53 + 37 / 100 / 2 ^ 53) * (9 / 8) + 9 / 8 / 2 ^ 98 :=
          add_le_add (mul_le_mul_of_nonneg_left hS98 (by positivity))
            (div_le_div_of_nonneg_right hS98 (by positivity))
        _ ≤ 11 / 16 * unitRoundoff64 := by rw [hu]; norm_num
    have hPm32 : |value p| ≤ value s / 32 := by linarith
    obtain ⟨hclim, hc1, hc2⟩ := compensated_one_step s p _ hsf hpf hS hshi hPm32 hy1 hE hpre'
    exact F64SignedRounding.within_of_nonneg 1 E hE.le _ hclim.le hc1 hc2
  · rw [hlt, decide_eq_false hy1]
    simp only [Bool.false_eq_true, ite_false]
    have hy1' : 1 ≤ value (Wasm.IEEE64.add s p) := le_of_not_gt hy1
    have hey := exponent_ge_of_one_le _ hy1'
    have hefin : Wasm.IEEE64.exponent (Wasm.IEEE64.add s p) ≤ 2046 := by
      have h := hyf
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
      have : Wasm.IEEE64.exponent (Wasm.IEEE64.add s p) < 2048 := Nat.mod_lt _ (by norm_num)
      omega
    obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 1 (Wasm.IEEE64.add s p) (by norm_num)
      (by norm_num) hyf (by omega) (by omega) (by omega)
    rw [← scale_down_word] at hcf hcv
    set c := Wasm.IEEE64.mul 0x0010000000000000 (Wasm.IEEE64.add s p)
    have hcv' : value c = (2 : ℝ) ^ (-1022 : Int) * value (Wasm.IEEE64.add s p) := by
      rw [hcv, show ((1 : Nat) : Int) - 1023 = -1022 by norm_num]
    have hEu : E ≤ (2 : ℝ) ^ q * (2 - 1 / 65536) := by
      by_cases hj0 : j.val = 0
      · have := (hEz hj0).2
        nlinarith
      · exact (hEn hj0).2
    have hzq : (2 : ℝ) ^ (1022 : Int) * (2 : ℝ) ^ q = (2 : ℝ) ^ (q + 1022) := by
      rw [← zpow_add₀ (by norm_num), add_comm]
    have hm1022 : (2 : ℝ) ^ (-1022 : Int) * (2 : ℝ) ^ (q + 1022) = (2 : ℝ) ^ q := by
      rw [← zpow_add₀ (by norm_num), show (-1022 : Int) + (q + 1022) = q by ring]
    have hinv : (2 : ℝ) ^ (-1022 : Int) * (2 : ℝ) ^ (1022 : Int) = 1 := by
      rw [← zpow_add₀ (by norm_num), show (-1022 : Int) + 1022 = 0 by norm_num, zpow_zero]
    have hq : -1022 ≤ q := by
      by_contra hn
      push Not at hn
      have hR' : (2 : ℝ) ^ (q + 1022) ≤ (2 : ℝ) ^ (-1 : Int) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hhalf : (2 : ℝ) ^ (-1 : Int) = 1 / 2 := by norm_num
      have h1 : (2 : ℝ) ^ (1022 : Int) * E ≤ (2 : ℝ) ^ (q + 1022) * (2 - 1 / 65536) := by
        rw [← hzq, mul_assoc]
        exact mul_le_mul_of_nonneg_left hEu (by positivity)
      have h2 : value s ≤ (2 : ℝ) ^ (q + 1022) * (255 / 128) := by
        rw [hs]
        exact mul_le_mul_of_nonneg_left hH hR.le
      have h3 := abs_le.mp hye
      rw [hu] at h3
      rw [hhalf] at hR'
      linarith
    have herr : |value c - E| ≤
        (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
      have hid : value c - E = (2 : ℝ) ^ (-1022 : Int) *
          (value (Wasm.IEEE64.add s p) - (2 : ℝ) ^ (1022 : Int) * E) := by
        rw [hcv', mul_sub, ← mul_assoc, hinv, one_mul]
      rw [hid, abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
      calc
        _ ≤ (2 : ℝ) ^ (-1022 : Int) * ((7 / 5) * unitRoundoff64 * value s) :=
          mul_le_mul_of_nonneg_left hye (by positivity)
        _ = _ := by
          rw [hs, ← hm1022]
          ring
    have hcpos : 0 < value c := by
      rw [hcv']
      exact mul_pos (zpow_pos (by norm_num) _) (by linarith)
    have hclim := F64PositiveOrder.positive_finite_encoding _ hcf hcpos
    have hstep := ExpOneStep.one_step_of_error E _ c q j hq hEn hEz herr (Or.inl ⟨hclim, rfl⟩)
    exact F64SignedRounding.within_of_nonneg 1 E hE.le c hclim.le hstep.1 hstep.2

#print axioms presum_tight
#print axioms reconstruction_tight
#print axioms reconstruction_target
#print axioms ordinary_tight
#print axioms mul_comm_finite
#print axioms positive1009_tight
#print axioms negative_tight

end Library.Numerics.Float64.Exp.ArmTight
