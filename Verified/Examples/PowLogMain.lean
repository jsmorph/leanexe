import Verified.Examples.PowLogError

/-!
`Pow.powLog` against `log x`.  For the word `iz` of `z` and table entry `i`, the computed pair
approximates `M` (`PowLogError.after_error`), and `M` approximates `L = k log 2 + log z` within
`|k| 2 ^ -91` (the split of `log 2`), `2 ^ -97` (the table), and `6 · 2 ^ -70 |r|` (the
polynomial).  With `|L| ≥ 0.34 |k|` for `k ≠ 0`, `|L| ≥ max (|r|, 1/460)` for `k = 0` and
`logc ≠ 0`, and `|L| ≥ 0.99 |r|` with `|r| ≥ 2 ^ -53` for `k = 0`, `logc = 0`, and `z ≠ 1`, the
error is at most `(7/8) 2 ^ -65 |L|`.
-/

namespace Verified.Examples.PowLogMain
open CodeLib.IEEE64 LeanExe.ProofKit ExpSpecialNegative PowLogTable

set_option exponentiation.threshold 4096

theorem ln2_error :
    |value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730 - Real.log 2| ≤ 1 / 2 ^ 91 ∧
      6931 / 10000 ≤ Real.log 2 := by
  have hq : PolyBound.qabs (ExpReductionBounds.splitLogTwo -
      (PolyBound.ratOfWord 0x3FE62E42FEFA3800 + PolyBound.ratOfWord 0x3D2EF35793C76730)) ≤
      1 / 2 ^ 92 ∧ (6931 / 10000 : ℚ) ≤ ExpReductionBounds.lowerLogTwo := by decide +kernel
  obtain ⟨hq, hl⟩ := hq
  have hq' := rat_le hq
  rw [PolyBound.qabs_cast] at hq'
  push_cast at hq'
  rw [PolyBound.ratOfWord_cast, PolyBound.ratOfWord_cast] at hq'
  obtain ⟨he1, he2⟩ := ExpReductionBounds.log_two_enclosure
  have hlo : (ExpReductionBounds.lowerLogTwo : ℝ) =
      (ExpReductionBounds.splitLogTwo : ℝ) - 1 / 2 ^ 92 := by
    rw [ExpReductionBounds.lowerLogTwo]
    push_cast
    ring
  have hup : (ExpReductionBounds.upperLogTwo : ℝ) =
      (ExpReductionBounds.splitLogTwo : ℝ) + 1 / 2 ^ 92 := by
    rw [ExpReductionBounds.upperLogTwo]
    push_cast
    ring
  have hl' := rat_le hl
  push_cast at hl'
  refine ⟨?_, hl'.trans he1⟩
  have h1 := abs_le.mp hq'
  rw [abs_le]
  constructor <;> linarith

theorem log1p_linear (R : ℝ) (hR : |R| ≤ 23 / 4000) :
    |Real.log (1 + R) - R| ≤ 1006 / 1000 * R ^ 2 := by
  have h := TaylorRemainder.log1p_remainder R (hR.trans_lt (by norm_num)) 1
  have he : PolyBound.eval (TaylorRemainder.log1pCoeffs 1) R = R := by
    simp [TaylorRemainder.log1pCoeffs, TaylorRemainder.log1pQuotCoeffs]
  rw [he] at h
  have h1 : 0 < 1 - |R| := by linarith [show (23 : ℝ) / 4000 < 1 by norm_num]
  have h2 : |R| ^ (1 + 1) / (1 - |R|) ≤ 1006 / 1000 * R ^ 2 := by
    rw [div_le_iff₀ h1, show 1 + 1 = 2 from rfl, sq_abs]
    have := sq_nonneg R
    nlinarith
  exact h.trans h2

theorem bound_mono (K : Int) (lt R T Q H Q' H' : ℝ) (hQ : Q ≤ Q') (hH : H ≤ H') :
    PowLogError.bound K lt R T Q H ≤ PowLogError.bound K lt R T Q' H' := by
  simp only [PowLogError.bound]
  have : 12 / 2 ^ 53 * Q ≤ 12 / 2 ^ 53 * Q' := mul_le_mul_of_nonneg_left hQ (by positivity)
  have : 24 / 2 ^ 106 * H ≤ 24 / 2 ^ 106 * H' := mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith

theorem word_value (w : UInt64) : value w = ((PolyBound.ratOfWord w : ℚ) : ℝ) :=
  (PolyBound.ratOfWord_cast w).symm

/-- The computed pair of an entry against `L = k log 2 + log z`, before the case analysis. -/
theorem core_bound (iz kd : UInt64) (e f : Nat) (he : e = 1022 ∨ e = 1023) (hf : f < 2 ^ 52)
    (hf1023 : e = 1023 → f + 2 ^ 31 < 2 ^ 52) (hiz : iz.toNat = e * 2 ^ 52 + f)
    (i : Fin 128) (hie : e = 1022 → i.val ≤ 75) (hie' : e = 1023 → 75 ≤ i.val)
    (hzl : e = 1022 → (lowU i.val : ℝ) ≤ value iz ∧ value iz ≤ (highU i.val : ℝ))
    (hzl' : e = 1023 → (lowL i.val : ℝ) ≤ value iz ∧ value iz ≤ (highL i.val : ℝ))
    (K : Int) (hkf : Finite kd) (hkv : value kd = K) (hK : |K| ≤ 1100) :
    let invc := Pow.powLogTable[4 * i.val]!
    let lc := Pow.powLogTable[4 * i.val + 2]!
    let lt := Pow.powLogTable[4 * i.val + 3]!
    let W := PowLogEval.logWords iz kd invc lc lt
    let R := value iz * value invc - 1
    let T := K * value 0x3FE62E42FEFA3800 + value lc
    Finite W.1 ∧ Finite W.2 ∧ 0 < value iz ∧ |R| ≤ 23 / 4000 ∧ |value lc| ≤ 3466 / 10000 ∧
      |value lt| ≤ 1 / 2 ^ 43 ∧
      |Real.log (value iz) - (Real.log (1 + R) + value lc + value lt)| ≤ 1 / 2 ^ 97 ∧
      (logcQ i.val = 0 → value invc = 1 ∧ value lc = 0 ∧ value lt = 0 ∧
        |Real.log (value iz) - Real.log (1 + R)| = 0) ∧
      (0 < value lc → 1 / 10000 ≤ value lc + 2 * R ∧ 1 / 450 ≤ value lc + R) ∧
      (value lc < 0 → value lc + 2 * R ≤ -(1 / 10000) ∧ value lc + R ≤ -(1 / 450)) ∧
      (value lc = 0 → logcQ i.val = 0) ∧
      |value W.1 + value W.2 - (K * Real.log 2 + Real.log (value iz))| ≤
        |(K : ℝ)| / 2 ^ 91 + 1 / 2 ^ 97 + |R| * (6 / 2 ^ 70) +
          PowLogError.bound K (value lt) R T (3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22))
            ((|R| + 3 / 2 ^ 22) ^ 2) ∧
      (logcQ i.val = 0 → |value W.1 + value W.2 - (K * Real.log 2 + Real.log (value iz))| ≤
        |(K : ℝ)| / 2 ^ 91 + |R| * (6 / 2 ^ 70) +
          PowLogError.bound K (value lt) R T (9 / 2 ^ 22 * |R|) (4 * R ^ 2)) ∧
      (logcQ i.val = 0 → |value W.2| ≤ 2 / 2 ^ 53 * |value W.1| +
          PowLogError.bound K (value lt) R T (9 / 2 ^ 22 * |R|) (4 * R ^ 2)) ∧
      |value W.2| ≤ 2 / 2 ^ 53 * |value W.1| +
        PowLogError.bound K (value lt) R T (3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22))
          ((|R| + 3 / 2 ^ 22) ^ 2) := by
  intro invc lc lt W R T
  obtain ⟨hif, hlcf, hltf, hil, hiu, hg1022, hg1023, hlcg, hlcb, hltb, hrU, hrL, hpos, hneg,
    hzero⟩ := checked_entries i
  have hinv : value invc = (invcQ i.val : ℝ) := word_value _
  have hlcv : value lc = (logcQ i.val : ℝ) := word_value _
  have hltv : value lt = (tailQ i.val : ℝ) := word_value _
  have hil' : 1 / 2 ≤ value invc := by rw [hinv]; have := rat_le hil; push_cast at this; exact this
  have hiu' : value invc ≤ 3 / 2 := by rw [hinv]; have := rat_le hiu; push_cast at this; exact this
  have hip : 0 < value invc := by linarith
  have hlcb' : |value lc| ≤ 3466 / 10000 := by
    rw [hlcv]
    have := rat_le hlcb
    rw [PolyBound.qabs_cast] at this
    exact this.trans (by norm_num)
  have hltb' : |value lt| ≤ 1 / 2 ^ 43 := by
    rw [hltv]
    have := rat_le hltb
    rw [PolyBound.qabs_cast] at this
    exact this.trans (by norm_num)
  -- `z` and `r`
  have hzpos : 0 < value iz := by
    rcases he with he | he
    · have h := (hzl he).1
      have : (0 : ℝ) < (lowU i.val : ℝ) := by
        have h1 : 0 < 2 ^ 52 + 1853042165022720 + i.val * 2 ^ 45 :=
          Nat.lt_of_lt_of_le (Nat.two_pow_pos 52)
            (Nat.le_trans (Nat.le_add_right _ 1853042165022720) (Nat.le_add_right _ _))
        have h2 : (0 : ℚ) < lowU i.val := by
          unfold lowU
          exact div_pos (Nat.cast_pos.mpr h1) (by norm_num)
        exact Rat.cast_pos.mpr h2
      linarith
    · have h := (hzl' he).1
      have : (0 : ℝ) < (lowL i.val : ℝ) := by
        rw [lowL]
        push_cast
        have : (0 : ℝ) < ((max (2 ^ 52) (1853042165022720 + i.val * 2 ^ 45) : Nat) : ℝ) := by
          have : 0 < max (2 ^ 52) (1853042165022720 + i.val * 2 ^ 45) :=
            lt_of_lt_of_le (by norm_num) (le_max_left _ _)
          exact_mod_cast this
        positivity
      linarith
  have hR : |R| ≤ 23 / 4000 := by
    rcases he with he | he
    · obtain ⟨h1, h2⟩ := hzl he
      obtain ⟨h3, h4⟩ := hrU (hie he)
      have h3' := rat_le h3
      have h4' := rat_le h4
      push_cast at h3' h4'
      rw [← hinv] at h3' h4'
      have h5 := mul_le_mul_of_nonneg_right h1 hip.le
      have h6 := mul_le_mul_of_nonneg_right h2 hip.le
      rw [abs_le]
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hzl' he
      obtain ⟨h3, h4⟩ := hrL (hie' he)
      have h3' := rat_le h3
      have h4' := rat_le h4
      push_cast at h3' h4'
      rw [← hinv] at h3' h4'
      have h5 := mul_le_mul_of_nonneg_right h1 hip.le
      have h6 := mul_le_mul_of_nonneg_right h2 hip.le
      rw [abs_le]
      constructor <;> linarith
  have hg66 : Wasm.IEEE64.scaledValue invc % 2 ^ 1066 = 0 := by
    rcases he with he | he
    · have h := hg1022 (hie he)
      rw [← Int.emod_emod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 1066 ≤ 1067)), h]
      rfl
    · exact hg1023 (hie' he)
  obtain ⟨hzf, hhf, hzlof, hrhif, hrlof, hrf, hrv, hsum, hrhg, hrg, hrlb, hrl1⟩ :=
    PowLogReduce.reduce_state iz invc e f he hf hf1023 hiz hif hil' hiu'
      (fun h => hg1022 (hie h)) hg66 hR
  set zhi := PowLogBits.zhiOf iz
  set rhi := Wasm.IEEE64.sub (Wasm.IEEE64.mul zhi invc) one
  set rlo := Wasm.IEEE64.mul (Wasm.IEEE64.sub iz zhi) invc
  have hrv' : value (Wasm.IEEE64.add rhi rlo) = value rhi + value rlo := hrv.trans hsum.symm
  obtain ⟨hW1f, hW2f, hWM, hW2b⟩ := PowLogError.after_error rhi rlo kd lc lt K hrhif hrlof hrf
    hrv' hrhg hrg (by rw [hsum]; exact hR) hrlb hkf hkv hK hlcf hlcg hlcb' hltf hltb'
  rw [hsum] at hWM hW2b
  have hW : W = PowLogError.afterWords rhi rlo kd lc lt := PowLogError.logWords_eq iz kd invc lc lt
  -- `M` against `L`
  have hLz : Real.log (value iz) = Real.log (1 + R) - Real.log (value invc) := by
    have h1 : value iz = (1 + R) / value invc := by
      simp only [R]
      field_simp
      ring
    rw [h1, Real.log_div (by linarith [abs_le.mp hR]) hip.ne']
  have htab := (log_table i).2
  rw [← hinv, ← hlcv, ← hltv] at htab
  have hker := kernel_error R hR
  rw [kernel_eval] at hker
  obtain ⟨hln2, -⟩ := ln2_error
  have hK' : |(K : ℝ)| ≤ 1100 := by exact_mod_cast hK
  have hMK : |(K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) -
      K * Real.log 2| ≤ |(K : ℝ)| / 2 ^ 91 := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ |(K : ℝ)| * (1 / 2 ^ 91) := mul_le_mul_of_nonneg_left hln2 (abs_nonneg _)
      _ = _ := by ring
  have hML : |(K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc +
      value lt + (R - R ^ 2 / 2 + poly R) - (K * Real.log 2 + Real.log (value iz))| ≤
      |(K : ℝ)| / 2 ^ 91 + 1 / 2 ^ 97 + |R| * (6 / 2 ^ 70) := by
    rw [hLz]
    have h1 := abs_le.mp hMK
    have h2 := abs_le.mp htab
    have h3 := abs_le.mp hker
    rw [abs_le]
    constructor <;> linarith
  -- `Q` and `H`
  set Rh := value rhi
  set Rl := value rlo
  have hRs : Rh + Rl = R := hsum
  have hRRl := abs_le.mp hrlb
  have hQg : |Rl| * |R + Rh| ≤ 3 / 2 ^ 22 * (2 * |R| + 3 / 2 ^ 22) := by
    have h1 : |R + Rh| ≤ 2 * |R| + 3 / 2 ^ 22 := by
      rw [show R + Rh = 2 * R - Rl by linear_combination hRs]
      have := abs_sub (2 * R) Rl
      rw [abs_mul, abs_two] at this
      linarith
    exact mul_le_mul hrlb h1 (abs_nonneg _) (by norm_num)
  have hHg : Rh ^ 2 ≤ (|R| + 3 / 2 ^ 22) ^ 2 := by
    rw [← sq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [show Rh = R - Rl by linear_combination hRs]
    have := abs_sub R Rl
    linarith
  have hb := bound_mono K (value lt) R T _ _ _ _ hQg hHg
  have hzeroc : logcQ i.val = 0 → value invc = 1 ∧ value lc = 0 ∧ value lt = 0 := by
    intro h0
    obtain ⟨h1, h2, h3⟩ := hzero h0
    refine ⟨?_, ?_, ?_⟩
    · show value Pow.powLogTable[4 * i.val]! = 1
      rw [h1]
      exact ExpTinyError.one_value
    · show value Pow.powLogTable[4 * i.val + 2]! = 0
      rw [h2]
      exact F64Magnitude.value_zero
    · show value Pow.powLogTable[4 * i.val + 3]! = 0
      rw [h3]
      exact F64Magnitude.value_zero
  have hone : logcQ i.val = 0 → |Rl| * |R + Rh| ≤ 9 / 2 ^ 22 * |R| ∧ Rh ^ 2 ≤ 4 * R ^ 2 := by
    intro h0
    obtain ⟨h1, -, -⟩ := hzeroc h0
    have hRl2 : |Rl| ≤ |R| := hrl1 h1
    constructor
    · have h4 : |R + Rh| ≤ 3 * |R| := by
        rw [show R + Rh = 2 * R - Rl by linear_combination hRs]
        have := abs_sub (2 * R) Rl
        rw [abs_mul, abs_two] at this
        linarith
      calc
        _ ≤ 3 / 2 ^ 22 * (3 * |R|) := mul_le_mul hrlb h4 (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    · rw [← sq_abs, show (4 : ℝ) * R ^ 2 = (2 * |R|) ^ 2 by rw [mul_pow, sq_abs]; norm_num]
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [show Rh = R - Rl by linear_combination hRs]
      have := abs_sub R Rl
      linarith
  refine ⟨by rw [hW]; exact hW1f, by rw [hW]; exact hW2f, hzpos, hR, hlcb', hltb', ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLz]
    have h2 := abs_le.mp htab
    rw [abs_le]
    constructor <;> linarith
  · intro h0
    obtain ⟨h1, h2, h3⟩ := hzeroc h0
    refine ⟨h1, h2, h3, ?_⟩
    rw [hLz, h1, Real.log_one, sub_zero, sub_self, abs_zero]
  · intro hp
    have hp' : 0 < logcQ i.val := by rw [hlcv] at hp; exact_mod_cast hp
    obtain ⟨h1, h2⟩ := hpos hp'
    have h1' := rat_le h1
    have h2' := rat_le h2
    rw [rminQ] at h1' h2'
    rcases he with he | he
    · rw [ite_eq_left (hie he)] at h1' h2'
      push_cast at h1' h2'
      rw [← hlcv, ← hinv] at h1' h2'
      have h5 := mul_le_mul_of_nonneg_right (hzl he).1 hip.le
      constructor <;> linarith
    · by_cases h75 : i.val ≤ 75
      · have hi75 : i.val = 75 := le_antisymm h75 (hie' he)
        exfalso
        have : logcQ i.val = 0 := by rw [hi75]; decide +kernel
        linarith
      · rw [ite_eq_right h75] at h1' h2'
        push_cast at h1' h2'
        rw [← hlcv, ← hinv] at h1' h2'
        have h5 := mul_le_mul_of_nonneg_right (hzl' he).1 hip.le
        constructor <;> linarith
  · intro hn
    have hn' : logcQ i.val < 0 := by rw [hlcv] at hn; exact_mod_cast hn
    obtain ⟨h1, h2⟩ := hneg hn'
    have h1' := rat_le h1
    have h2' := rat_le h2
    rw [rmaxQ] at h1' h2'
    rcases he with he | he
    · rw [ite_eq_left (hie he)] at h1' h2'
      push_cast at h1' h2'
      rw [← hlcv, ← hinv] at h1' h2'
      have h5 := mul_le_mul_of_nonneg_right (hzl he).2 hip.le
      constructor <;> linarith
    · by_cases h75 : i.val ≤ 75
      · have hi75 : i.val = 75 := le_antisymm h75 (hie' he)
        exfalso
        have : logcQ i.val = 0 := by rw [hi75]; decide +kernel
        linarith
      · rw [ite_eq_right h75] at h1' h2'
        push_cast at h1' h2'
        rw [← hlcv, ← hinv] at h1' h2'
        have h5 := mul_le_mul_of_nonneg_right (hzl' he).2 hip.le
        constructor <;> linarith
  · intro h0
    rw [hlcv] at h0
    exact_mod_cast h0
  · rw [hW]
    calc
      _ ≤ |value (PowLogError.afterWords rhi rlo kd lc lt).1 +
            value (PowLogError.afterWords rhi rlo kd lc lt).2 -
            ((K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc +
              value lt + (R - R ^ 2 / 2 + poly R))| +
          |(K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc +
              value lt + (R - R ^ 2 / 2 + poly R) - (K * Real.log 2 + Real.log (value iz))| :=
        abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · intro h0
    obtain ⟨h1, h2, h3⟩ := hzeroc h0
    obtain ⟨hQ1, hH1⟩ := hone h0
    have hb1 := bound_mono K (value lt) R T _ _ _ _ hQ1 hH1
    have htab0 : |Real.log (value iz) - Real.log (1 + R)| = 0 := by
      rw [hLz, h1, Real.log_one, sub_zero, sub_self, abs_zero]
    have hML0 : |(K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc +
        value lt + (R - R ^ 2 / 2 + poly R) - (K * Real.log 2 + Real.log (value iz))| ≤
        |(K : ℝ)| / 2 ^ 91 + |R| * (6 / 2 ^ 70) := by
      rw [h2, h3]
      have h4 := abs_le.mp hMK
      have h5 := abs_le.mp hker
      have h6 : Real.log (value iz) = Real.log (1 + R) := by
        have := abs_eq_zero.mp htab0
        linarith
      rw [h6, abs_le]
      constructor <;> linarith
    rw [hW]
    calc
      _ ≤ |value (PowLogError.afterWords rhi rlo kd lc lt).1 +
            value (PowLogError.afterWords rhi rlo kd lc lt).2 -
            ((K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc +
              value lt + (R - R ^ 2 / 2 + poly R))| +
          |(K : ℝ) * (value 0x3FE62E42FEFA3800 + value 0x3D2EF35793C76730) + value lc +
              value lt + (R - R ^ 2 / 2 + poly R) - (K * Real.log 2 + Real.log (value iz))| :=
        abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · intro h0
    obtain ⟨hQ1, hH1⟩ := hone h0
    have hb1 := bound_mono K (value lt) R T _ _ _ _ hQ1 hH1
    rw [hW]
    linarith
  · rw [hW]
    linarith

#print axioms ln2_error
#print axioms log1p_linear
#print axioms bound_mono
#print axioms core_bound

end Verified.Examples.PowLogMain
