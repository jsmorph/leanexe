import Verified.Examples.AsinhTheoremCompose
import Verified.Examples.AcoshTheoremMid
import LeanExe.ProofKit.F64SqrtHalf
import LeanExe.ProofKit.F64GridExact

/-!
`Asinh.acosh` from 1 to `2 (1 + 2 ^ -20)`: the code returns `log1p (t + √(2t + t²))` with
`t = x - 1`.  `t` is exact and a multiple of `2 ^ -52` (`acosh_t`).  `acosh_s` bounds the computed
root against `S = √(2t + t²)` with half spacings: `t²` has relative error `2 ^ -53`, the sum
`2t + t²` and the root round within half a spacing of the binades `2 ^ g_r` and `2 ^ g_s` below
bounds of their values (`F64HalfUlp.fapprox_add_half`, `F64SqrtHalf.sqrt_half`).  `add_exact`
states that `t + s` is exact when `s` lies in a binade at most `[1, 2)` and the sum stays in it,
since `t` lies on the grid of that binade.
-/

namespace Verified.Examples.AcoshTheoremSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64Near F64HalfUlp Log1pTheoremNear
  AsinhTheoremCompose

set_option exponentiation.threshold 4096

/-- A positive word of value at least `2 ^ (g - 1022)` lies on the grid of `2 ^ g` scaled
units. -/
theorem grid_of_value (x : UInt64) (hs : Wasm.IEEE64.sign x = false) (g : ℕ)
    (hv : (2 : ℝ) ^ (((g + 1 : ℕ) : ℤ) - 1023) ≤ value x) :
    ∃ M : ℕ, Wasm.IEEE64.scaledValue x = (M : ℤ) * 2 ^ g := by
  have he := F64Magnitude.exponent_ge_of_value x (g + 1) (by omega) hv
  obtain ⟨M0, _, hM⟩ := F64Exact.magnitude_grid x
  refine ⟨M0 * 2 ^ (Wasm.IEEE64.exponent x - 1 - g), ?_⟩
  rw [F64Exact.scaledValue_of_sign x hs, hM]
  push_cast
  rw [mul_assoc, ← pow_add, show Wasm.IEEE64.exponent x - 1 - g + g = Wasm.IEEE64.exponent x - 1 by
    omega]

theorem one_scaled : Wasm.IEEE64.scaledValue (1.0 : Float).toBits = (2 ^ 52 : ℕ) * 2 ^ 1022 := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  decide +kernel

/-- `t = x - 1` is exact for `1 ≤ x ≤ 3` and a multiple of `2 ^ -52`. -/
theorem acosh_t (x : Float) (hx : Finite x.toBits) (h1 : 1 ≤ value x.toBits)
    (h3 : value x.toBits ≤ 3) :
    Finite (x - 1.0).toBits ∧ value (x - 1.0).toBits = value x.toBits - 1 ∧
      ∃ N : ℕ, value (x - 1.0).toBits = N / 2 ^ 52 := by
  have hs : Wasm.IEEE64.sign x.toBits = false := F64Exact.sign_of_pos _ (by linarith)
  obtain ⟨M, hM⟩ := grid_of_value x.toBits hs 1022 (by norm_num; linarith)
  have hvx : value x.toBits = (M : ℝ) * 2 ^ 1022 / 2 ^ 1074 := by
    rw [value, hM]
    push_cast
    ring
  have hM1 : (2 : ℝ) ^ 52 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) * 2 ^ 1022 / 2 ^ 1074 := hvx ▸ h1
    rw [le_div_iff₀ (by positivity)] at this
    have h2 : (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 := by norm_num
    nlinarith
  have hM3 : (M : ℝ) ≤ 3 * 2 ^ 52 := by
    have : (M : ℝ) * 2 ^ 1022 / 2 ^ 1074 ≤ 3 := hvx ▸ h3
    rw [div_le_iff₀ (by positivity)] at this
    have h2 : (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 := by norm_num
    nlinarith
  have hM1' : 2 ^ 52 ≤ M := by exact_mod_cast hM1
  have hM3' : M ≤ 3 * 2 ^ 52 := by exact_mod_cast hM3
  have hsub := F64GridExact.sub_grid_exact x.toBits (1.0 : Float).toBits hx
    (by rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
        unfold CodeLib.IEEE64.Finite; decide)
    ((M : ℤ) - 2 ^ 52) 1022 (by rw [hM, one_scaled]; push_cast; ring)
    (by omega) (by norm_num)
  rw [← F64Bits.toBits_sub] at hsub
  have hvt : value (x - 1.0).toBits = ((M : ℝ) - 2 ^ 52) / 2 ^ 52 := by
    rw [value, hsub.2, hM, one_scaled]
    push_cast
    field_simp
    ring
  refine ⟨hsub.1, ?_, ⟨M - 2 ^ 52, ?_⟩⟩
  · rw [hvt, hvx]
    field_simp
  · rw [hvt, Nat.cast_sub hM1']
    push_cast
    ring

/-- The computed root of `2t + t²` within `δs` of `S`, for `t ∈ [TL, TH]`. -/
theorem acosh_s (t : Float) (ht : Finite t.toBits) (TL TH hr hs SLm : ℝ) (gr gs : ℕ)
    (hTL : TL ≤ value t.toBits) (hTH : value t.toBits ≤ TH) (hTL0 : 1 / 2 ^ 52 ≤ TL)
    (hTH2 : TH ≤ 2) (hgr : gr ≤ 1023)
    (hhr : 2 ^ gr / 2 / 2 ^ 1074 ≤ hr) (hhs : 2 ^ gs / 2 / 2 ^ 1074 ≤ hs)
    (hR : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075) < 2 ^ (53 + gr) / 2 ^ 1074)
    (hSLm0 : 0 < SLm)
    (hSLm : SLm ^ 2 ≤ 2 * TL + TL * TL - (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr))
    (hS : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) <
      (2 ^ (53 + gs) / 2 ^ 1074) ^ 2) :
    Finite (2.0 * t + t * t).sqrt.toBits ∧
      |value (2.0 * t + t * t).sqrt.toBits - Real.sqrt (2 * value t.toBits + value t.toBits * value t.toBits)| ≤
        hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) ∧
      SLm - hs ≤ value (2.0 * t + t * t).sqrt.toBits := by
  set T := value t.toBits with hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) (hTL0.trans hTL)
  have hTH0 : 0 ≤ TH := hT0.le.trans hTH
  -- `2 t`
  obtain ⟨hpf, hpv⟩ := AtanTheoremReduce.double_float t ht
    (by rw [abs_of_pos hT0]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 52)])
    (by rw [abs_of_pos hT0]; linarith [(by norm_num : (2 : ℝ) < 2 ^ 900)])
  have hp : FApprox (2.0 * t) (2 * T) 0 := ⟨hpf, by rw [hpv, sub_self, abs_zero]⟩
  -- `t * t`
  have hTT : T * T ≤ TH * TH := mul_le_mul hTH hTH hT0.le hTH0
  have hm0 := approx_mul (approx_self t.toBits ht) (approx_self t.toBits ht) T T
    (le_of_eq (abs_of_pos hT0)) (le_of_eq (abs_of_pos hT0)) (T * T) (le_of_eq (by ring))
    (by nlinarith [(by norm_num : (4 : ℝ) < 2 ^ 1022)])
  rw [← F64Bits.toBits_mul] at hm0
  have hm : FApprox (t * t) (T * T) (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075) := by
    refine hm0.mono ?_
    have : T * T / 2 ^ 53 ≤ TH * TH / 2 ^ 53 := div_le_div_of_nonneg_right hTT (by positivity)
    linarith
  -- `2 t + t * t`
  have hr0 := fapprox_add_half hp hm gr hgr (by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * T + T * T), zero_add]
    linarith)
  set er := TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr with her
  have hrr : |value (2.0 * t + t * t).toBits - (2 * T + T * T)| ≤ er := by
    have := hr0.2
    linarith
  have hrra := abs_le.mp hrr
  -- the root
  set rc := value (2.0 * t + t * t).toBits with hrc
  have hRL : 2 * TL + TL * TL ≤ 2 * T + T * T := by nlinarith
  have hrc0 : SLm ^ 2 ≤ rc := by linarith
  have hrcpos : 0 < rc := lt_of_lt_of_le (by positivity) hrc0
  have hsign : Wasm.IEEE64.sign (2.0 * t + t * t).toBits = false := F64Exact.sign_of_pos _ hrcpos
  have hmag : Wasm.IEEE64.scaledMagnitude (2.0 * t + t * t).toBits ≠ 0 :=
    (F64Magnitude.scaledMagnitude_pos _ hrcpos.ne').ne'
  have hsq : Real.sqrt rc < 2 ^ (53 + gs) / 2 ^ 1074 := by
    rw [Real.sqrt_lt' (by positivity)]
    linarith
  have hroot := F64SqrtHalf.sqrt_half _ hr0.1 hmag hsign gs hsq
  rw [← F64Bits.toBits_sqrt] at hroot
  have hS1 : SLm ≤ Real.sqrt rc := Real.le_sqrt_of_sq_le hrc0
  refine ⟨hroot.1, ?_, ?_⟩
  rotate_left
  · have := (abs_le.mp hroot.2).1
    linarith
  -- `|√rc - S| ≤ er/(2 SLm)`
  have hS2 : SLm ≤ Real.sqrt (2 * T + T * T) := Real.le_sqrt_of_sq_le (by linarith)
  have hden : 2 * SLm ≤ Real.sqrt rc + Real.sqrt (2 * T + T * T) := by linarith
  have hprod : (Real.sqrt rc - Real.sqrt (2 * T + T * T)) *
      (Real.sqrt rc + Real.sqrt (2 * T + T * T)) = rc - (2 * T + T * T) := by
    have h1 := Real.sq_sqrt hrcpos.le
    have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * T + T * T)
    linear_combination h1 - h2
  have hdiff : |Real.sqrt rc - Real.sqrt (2 * T + T * T)| ≤ er / (2 * SLm) := by
    rw [le_div_iff₀ (by positivity)]
    calc |Real.sqrt rc - Real.sqrt (2 * T + T * T)| * (2 * SLm)
        ≤ |Real.sqrt rc - Real.sqrt (2 * T + T * T)| *
          (Real.sqrt rc + Real.sqrt (2 * T + T * T)) :=
          mul_le_mul_of_nonneg_left hden (abs_nonneg _)
      _ = |rc - (2 * T + T * T)| := by
          rw [← hprod, abs_mul, abs_of_nonneg
            (by positivity : (0 : ℝ) ≤ Real.sqrt rc + Real.sqrt (2 * T + T * T))]
      _ ≤ er := hrr
  have htri := abs_sub_le (value (2.0 * t + t * t).sqrt.toBits) (Real.sqrt rc)
    (Real.sqrt (2 * T + T * T))
  linarith [hroot.2]

/-- `t + s` is exact when `t` lies on the grid of `2 ^ -52`, `s` in the binade
`[2 ^ (gs - 1022), 2 ^ (gs - 1021))` with `gs ≤ 1022`, and the sum stays in that binade. -/
theorem add_exact (t s : Float) (ht : Finite t.toBits) (hs : Finite s.toBits) (N : ℕ)
    (hN : value t.toBits = N / 2 ^ 52) (gs : ℕ) (hgs : gs ≤ 1022)
    (hsL : (2 : ℝ) ^ (((gs + 1 : ℕ) : ℤ) - 1023) ≤ value s.toBits)
    (hsum : value t.toBits + value s.toBits < 2 ^ (53 + gs) / 2 ^ 1074) :
    Finite (t + s).toBits ∧ value (t + s).toBits = value t.toBits + value s.toBits := by
  have hs0 : 0 < value s.toBits := lt_of_lt_of_le (by positivity) hsL
  have hsign : Wasm.IEEE64.sign s.toBits = false := F64Exact.sign_of_pos _ hs0
  obtain ⟨M, hM⟩ := grid_of_value s.toBits hsign gs hsL
  have htv : Wasm.IEEE64.scaledValue t.toBits = (N : ℤ) * 2 ^ 1022 := by
    have h : ((Wasm.IEEE64.scaledValue t.toBits : ℤ) : ℝ) = (((N : ℤ) * 2 ^ 1022 : ℤ) : ℝ) := by
      have h1 : ((Wasm.IEEE64.scaledValue t.toBits : ℤ) : ℝ) = value t.toBits * 2 ^ 1074 := by
        simp only [value]
        field_simp
      rw [h1, hN]
      push_cast
      field_simp
      ring
    exact_mod_cast h
  have hz : (N : ℤ) * 2 ^ 1022 + M * 2 ^ gs = ((N : ℤ) * 2 ^ (1022 - gs) + M) * 2 ^ gs := by
    rw [add_mul, mul_assoc, ← pow_add, show 1022 - gs + gs = 1022 by omega]
  have hpg : (2 : ℝ) ^ (1022 - gs) * 2 ^ gs = 2 ^ 1022 := by
    rw [← pow_add, show 1022 - gs + gs = 1022 by omega]
  have hvs : value s.toBits = (M : ℝ) * 2 ^ gs / 2 ^ 1074 := by
    simp only [value, hM]
    push_cast
    ring
  have hzv : value t.toBits + value s.toBits =
      ((N : ℝ) * 2 ^ (1022 - gs) + M) * 2 ^ gs / 2 ^ 1074 := by
    rw [hN, hvs, add_mul, mul_assoc, hpg]
    field_simp
  have hzr : (N : ℝ) * 2 ^ (1022 - gs) + M < 2 ^ 53 := by
    rw [hzv, div_lt_div_iff_of_pos_right (by positivity), pow_add] at hsum
    exact lt_of_mul_lt_mul_right hsum (by positivity)
  have hzn : N * 2 ^ (1022 - gs) + M < 2 ^ 53 := by exact_mod_cast hzr
  have hbound : ((N : ℤ) * 2 ^ (1022 - gs) + M).natAbs ≤ 2 ^ 53 := by
    have : ((N : ℤ) * 2 ^ (1022 - gs) + M) = ((N * 2 ^ (1022 - gs) + M : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_natCast]
    exact hzn.le
  have h := F64GridExact.grid_add_exact t.toBits s.toBits ht hs
    ((N : ℤ) * 2 ^ (1022 - gs) + M) gs (by rw [htv, hM, hz]) hbound (by omega)
  rw [← F64Bits.toBits_add] at h
  refine ⟨h.1, ?_⟩
  simp only [value, h.2]
  push_cast
  ring

theorem arcosh_eq (X : ℝ) :
    Real.arcosh X = Real.log (1 + ((X - 1) + Real.sqrt (2 * (X - 1) + (X - 1) * (X - 1)))) := by
  rw [Real.arcosh]
  congr 1
  rw [show 2 * (X - 1) + (X - 1) * (X - 1) = X ^ 2 - 1 by ring]
  ring

/-- The bound at a computed argument `u` within `δ` of `U = t + S`, for `t ∈ [TL, TH]` and
`S ∈ [SL, SH]`, against two spacings of binade `n`. -/
theorem acosh_core (x u : Float) (hu : Finite u.toBits) (TL TH SL SH δ E K YL : ℝ) (n : ℕ)
    (hTL : TL ≤ value x.toBits - 1) (hTH : value x.toBits - 1 ≤ TH) (hTL0 : 1 / 2 ^ 52 ≤ TL)
    (hTH2 : TH ≤ 2) (hSL0 : 0 ≤ SL) (hSL : SL ^ 2 ≤ 2 * TL + TL * TL)
    (hSH0 : 0 ≤ SH) (hSH : 2 * TH + TH * TH ≤ SH ^ 2)
    (hd : |value u.toBits - ((value x.toBits - 1) + Real.sqrt (2 * (value x.toBits - 1) +
      (value x.toBits - 1) * (value x.toBits - 1)))| ≤ δ)
    (hu29 : 1 / 2 ^ 29 ≤ TL + SL - δ)
    (hE : ∀ v : ℝ, TL + SL - δ ≤ v → v ≤ TH + SH + δ → errBound v ≤ E)
    (hK : δ ≤ K * (1 + TL + SL - δ))
    (hYL : YL ≤ Real.log (1 + (TL + SL)))
    (hn1 : 1 ≤ n) (hn : n < 2047)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + (E + K) ≤ YL)
    (hT : E + K < 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits)) (Log1p.log1p u).toBits := by
  set T := value x.toBits - 1 with hT'
  obtain ⟨S, hSdef⟩ : ∃ S, S = Real.sqrt (2 * T + T * T) := ⟨_, rfl⟩
  rw [← hSdef] at hd
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) (hTL0.trans hTL)
  have hSLS : SL ≤ S := by
    rw [hSdef]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hSSH : S ≤ SH := by
    rw [hSdef, Real.sqrt_le_left hSH0]
    nlinarith
  have hda := abs_le.mp hd
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hd
  have hw29 : 1 / 2 ^ 29 ≤ value u.toBits := by linarith
  have hN := (log1p_near u hu hw29).mono (hE _ (by linarith) (by linarith))
  have hm : 0 < 1 + TL + SL - δ := by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 29)]
  have hN2 := near_compose hN hd (m := 1 + TL + SL - δ) hm (by linarith) (by linarith)
  have hK' : δ / (1 + TL + SL - δ) ≤ K := by
    rw [div_le_iff₀ hm]
    exact hK
  have hY : Real.log (1 + (T + S)) = Real.arcosh (value x.toBits) := by
    rw [arcosh_eq, ← hT', ← hSdef]
  rw [hY] at hN2
  have hN3 := hN2.mono (E' := E + K) (by linarith only [hK'])
  have hYL' : YL ≤ Real.arcosh (value x.toBits) := by
    rw [← hY]
    exact hYL.trans (Real.log_le_log (by linarith only [hTL0, hSL0]) (by linarith only [hTL, hSLS]))
  have hY0 : 0 ≤ Real.arcosh (value x.toBits) := by
    rw [← hY]
    exact Real.log_nonneg (by linarith only [hT0, hSLS, hSL0])
  have hYu : Real.arcosh (value x.toBits) ≤ 5 := by
    rw [← hY]
    have := Real.log_le_sub_one_of_pos (by linarith only [hT0, hSLS, hSL0] : (0 : ℝ) < 1 + (T + S))
    have hS3 : S ≤ 3 := by
      rw [hSdef, Real.sqrt_le_left (by norm_num)]
      nlinarith
    linarith only [this, hS3, hTH, hTH2]
  refine hN3.within_two n hn1 hn ?_ hT ?_
  · rw [abs_of_nonneg hY0]
    generalize value (UInt64.ofNat (n * 2 ^ 52)) = B at hB ⊢
    linarith only [hB, hYL']
  · rw [abs_of_nonneg hY0]
    linarith only [hYu, (by norm_num : (5 : ℝ) < 2 ^ 1023)]

/-- A positive word above the predecessor of the start of binade `n` lies at or above that
start. -/
theorem ge_boundary (w : UInt64) (hw : 0 < value w) (n : ℕ) (hn2 : 2 ≤ n) (hn : n < 2047)
    (h : 2 ^ (n - 1 + 51) / 2 ^ 1074 + (2 ^ 52 - 1 : ℕ) * (2 ^ (n - 1 - 1) / 2 ^ 1074) <
      value w) :
    2 ^ (n + 51) / 2 ^ 1074 ≤ value w := by
  have hs : Wasm.IEEE64.sign w = false := F64Exact.sign_of_pos w hw
  have hw63 : w.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hpred := F64Compose.binade_word (n - 1) (2 ^ 52 - 1) (by omega) (by omega) (by omega)
  have hB := F64PositiveSpacing.boundary_value n (by omega) (by omega)
  rw [← hB]
  by_contra hc
  push Not at hc
  have hlt : w.toNat < n * 2 ^ 52 := by
    by_contra hc2
    push Not at hc2
    have hBt : (UInt64.ofNat (n * 2 ^ 52)).toNat = n * 2 ^ 52 :=
      UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
    have := (F64PositiveOrder.value_le_iff (by rw [hBt]; omega) hw63).mpr (by rw [hBt]; exact hc2)
    linarith
  have hPt : (UInt64.ofNat ((n - 1) * 2 ^ 52 + (2 ^ 52 - 1))).toNat = (n - 1) * 2 ^ 52 + (2 ^ 52 - 1) :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hle := (F64PositiveOrder.value_le_iff hw63 (by rw [hPt]; omega)).mpr (by rw [hPt]; omega)
  rw [hpred] at hle
  linarith

/-- A range of `t` where `t + s` stays in the binade of `s` and is exact. -/
theorem acosh_piece_exact (x : Float) (hx : Finite x.toBits)
    (TL TH hr hs SLm SL SH E K YL : ℝ) (gr gs n : ℕ)
    (hTL : TL ≤ value x.toBits - 1) (hTH : value x.toBits - 1 ≤ TH) (hTL0 : 1 / 2 ^ 52 ≤ TL)
    (hTH2 : TH ≤ 2) (hgr : gr ≤ 1023) (hgs1 : 1 ≤ gs) (hgs : gs ≤ 1022)
    (hhr : 2 ^ gr / 2 / 2 ^ 1074 ≤ hr) (hhs : 2 ^ gs / 2 / 2 ^ 1074 ≤ hs)
    (hR : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075) < 2 ^ (53 + gr) / 2 ^ 1074)
    (hSLm0 : 0 < SLm)
    (hSLm : SLm ^ 2 ≤ 2 * TL + TL * TL - (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr))
    (hS : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) <
      (2 ^ (53 + gs) / 2 ^ 1074) ^ 2)
    (hSL0 : 0 ≤ SL) (hSL : SL ^ 2 ≤ 2 * TL + TL * TL) (hSH0 : 0 ≤ SH)
    (hSH : 2 * TH + TH * TH ≤ SH ^ 2)
    (hbin : 2 ^ (gs + 51) / 2 ^ 1074 + (2 ^ 52 - 1 : ℕ) * (2 ^ (gs - 1) / 2 ^ 1074) + hs < SLm)
    (hsum : TH + SH + (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm)) <
      2 ^ (53 + gs) / 2 ^ 1074)
    (hu29 : 1 / 2 ^ 29 ≤ TL + SL - (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm)))
    (hE : ∀ v : ℝ, TL + SL - (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm)) ≤ v →
      v ≤ TH + SH + (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm)) → errBound v ≤ E)
    (hK : hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) ≤
      K * (1 + TL + SL - (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm))))
    (hYL : YL ≤ Real.log (1 + (TL + SL)))
    (hn1 : 1 ≤ n) (hn : n < 2047)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + (E + K) ≤ YL)
    (hT : E + K < 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits := by
  obtain ⟨htf, htv, N, hN⟩ := acosh_t x hx (by linarith) (by linarith)
  obtain ⟨hsf, hsd, hslow⟩ := acosh_s (x - 1.0) htf TL TH hr hs SLm gr gs (by rw [htv]; exact hTL)
    (by rw [htv]; exact hTH) hTL0 hTH2 hgr hhr hhs hR hSLm0 hSLm hS
  rw [htv] at hsd
  have hsB := ge_boundary _ (by
      linarith only [hslow, hbin, (by positivity : (0 : ℝ) < 2 ^ (gs + 51) / 2 ^ 1074),
        (by positivity : (0 : ℝ) ≤ (2 ^ 52 - 1 : ℕ) * (2 ^ (gs - 1) / 2 ^ 1074))])
    (gs + 1) (by omega) (by omega)
    (by
      rw [show gs + 1 - 1 + 51 = gs + 51 by omega, show gs + 1 - 1 - 1 = gs - 1 by omega]
      linarith only [hslow, hbin])
  set δ := hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) with hδ
  set T := value x.toBits - 1 with hT'
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) (hTL0.trans hTL)
  have hSLS : SL ≤ Real.sqrt (2 * T + T * T) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hSSH : Real.sqrt (2 * T + T * T) ≤ SH := by
    rw [Real.sqrt_le_left hSH0]
    nlinarith
  have hsda := abs_le.mp hsd
  obtain ⟨hadd, haddv⟩ := add_exact (x - 1.0) (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt
    htf hsf N hN gs hgs (by
      rw [show (2 : ℝ) ^ (((gs + 1 : ℕ) : ℤ) - 1023) = 2 ^ (gs + 1 + 51) / 2 ^ 1074 by
        rw [eq_div_iff (by positivity), ← zpow_natCast (2 : ℝ) 1074, ← zpow_add₀ two_ne_zero,
          ← zpow_natCast (2 : ℝ) (gs + 1 + 51)]
        congr 1
        push_cast
        ring]
      exact hsB) (by rw [htv]; linarith)
  refine acosh_core x _ hadd TL TH SL SH δ E K YL n hTL hTH hTL0 hTH2 hSL0 hSL hSH0 hSH ?_ hu29 hE
    hK hYL hn1 hn hB hT
  rw [haddv, htv]
  rw [show T + value (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt.toBits -
      (T + Real.sqrt (2 * T + T * T)) =
    value (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt.toBits - Real.sqrt (2 * T + T * T) by ring]
  exact hsd

/-- A range of `t` where the last sum rounds within half a spacing of binade `2 ^ gu`. -/
theorem acosh_piece_half (x : Float) (hx : Finite x.toBits)
    (TL TH hr hs hu SLm SL SH E K YL : ℝ) (gr gs gu n : ℕ)
    (hTL : TL ≤ value x.toBits - 1) (hTH : value x.toBits - 1 ≤ TH) (hTL0 : 1 / 2 ^ 52 ≤ TL)
    (hTH2 : TH ≤ 2) (hgr : gr ≤ 1023) (hgu : gu ≤ 1023)
    (hhr : 2 ^ gr / 2 / 2 ^ 1074 ≤ hr) (hhs : 2 ^ gs / 2 / 2 ^ 1074 ≤ hs)
    (hhu : 2 ^ gu / 2 / 2 ^ 1074 ≤ hu)
    (hR : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075) < 2 ^ (53 + gr) / 2 ^ 1074)
    (hSLm0 : 0 < SLm)
    (hSLm : SLm ^ 2 ≤ 2 * TL + TL * TL - (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr))
    (hS : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) <
      (2 ^ (53 + gs) / 2 ^ 1074) ^ 2)
    (hSL0 : 0 ≤ SL) (hSL : SL ^ 2 ≤ 2 * TL + TL * TL) (hSH0 : 0 ≤ SH)
    (hSH : 2 * TH + TH * TH ≤ SH ^ 2)
    (hsum : TH + SH + (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm)) <
      2 ^ (53 + gu) / 2 ^ 1074)
    (hu29 : 1 / 2 ^ 29 ≤ TL + SL - (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) + hu))
    (hE : ∀ v : ℝ, TL + SL - (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) + hu) ≤ v →
      v ≤ TH + SH + (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) + hu) →
      errBound v ≤ E)
    (hK : hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) + hu ≤
      K * (1 + TL + SL - (hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) + hu)))
    (hYL : YL ≤ Real.log (1 + (TL + SL)))
    (hn1 : 1 ≤ n) (hn : n < 2047)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + (E + K) ≤ YL)
    (hT : E + K < 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits := by
  obtain ⟨htf, htv, N, hN⟩ := acosh_t x hx (by linarith) (by linarith)
  obtain ⟨hsf, hsd, -⟩ := acosh_s (x - 1.0) htf TL TH hr hs SLm gr gs (by rw [htv]; exact hTL)
    (by rw [htv]; exact hTH) hTL0 hTH2 hgr hhr hhs hR hSLm0 hSLm hS
  rw [htv] at hsd
  set δs := hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) with hδ
  set T := value x.toBits - 1 with hT'
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) (hTL0.trans hTL)
  have hSSH : Real.sqrt (2 * T + T * T) ≤ SH := by
    rw [Real.sqrt_le_left hSH0]
    nlinarith
  have hsda := abs_le.mp hsd
  have hA : FApprox (x - 1.0) T 0 := ⟨htf, by rw [htv, sub_self, abs_zero]⟩
  have hB2 : FApprox (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt (Real.sqrt (2 * T + T * T)) δs :=
    ⟨hsf, hsd⟩
  have hw := fapprox_add_half hA hB2 gu hgu (by
    rw [abs_of_pos (by positivity : (0 : ℝ) < T + Real.sqrt (2 * T + T * T)), zero_add]
    linarith)
  refine acosh_core x _ hw.1 TL TH SL SH (δs + hu) E K YL n hTL hTH hTL0 hTH2 hSL0 hSL hSH0 hSH ?_
    hu29 hE hK hYL hn1 hn hB hT
  have := hw.2
  linarith

theorem errQuad_le2 (v E V : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ V)
    (hE : 174 / 100 / 2 ^ 53 * V ^ 2 + V / 2 ^ 59 ≤ E) :
    174 / 100 / 2 ^ 53 * v ^ 2 + v / 2 ^ 59 ≤ E := by
  have h2 : v ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 174 / 100 / 2 ^ 53 * v ^ 2 ≤ 174 / 100 / 2 ^ 53 * V ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : v / 2 ^ 59 ≤ V / 2 ^ 59 := div_le_div_of_nonneg_right h1 (by norm_num)
  linarith

theorem log_mono (X YL : ℝ) (q Lq : ℚ) (n : ℕ) (hX : ((1 + q : ℚ) : ℝ) ≤ X)
    (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (hL : Lq ≤ Log1pTheoremConst.logLo q n)
    (hY : YL ≤ (Lq : ℝ)) : YL ≤ Real.log X := by
  have h := Log1pTheoremConst.log_ge q Lq n hq hq1 hL
  have hq' : (-1 / 2 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : Real.log (1 + (q : ℝ)) ≤ Real.log X :=
    Real.log_le_log (by linarith) (by push_cast at hX; exact hX)
  linarith

theorem log_mono2 (X YL : ℝ) (q Lq : ℚ) (n : ℕ) (hX : ((2 * (1 + q) : ℚ) : ℝ) ≤ X)
    (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (hL : Lq ≤ Log1pTheoremConst.logLo q n)
    (hY : YL ≤ (Lq : ℝ) + 6931471803 / 10 ^ 10) : YL ≤ Real.log X := by
  have h := Log1pTheoremConst.log_ge q Lq n hq hq1 hL
  have h2 := Log1pTheoremTail.ln2_bounds
  have hq' : (-1 / 2 : ℝ) ≤ q := by exact_mod_cast hq
  have h3 : Real.log (2 * (1 + (q : ℝ))) ≤ Real.log X :=
    Real.log_le_log (by linarith) (by push_cast at hX; exact hX)
  rw [Real.log_mul (by norm_num) (by linarith)] at h3
  linarith [h2.1]

#print axioms grid_of_value
#print axioms acosh_t
#print axioms acosh_s
#print axioms add_exact
#print axioms ge_boundary
#print axioms errQuad_le2
#print axioms log_mono
#print axioms log_mono2
#print axioms acosh_core
#print axioms acosh_piece_exact
#print axioms acosh_piece_half

end Verified.Examples.AcoshTheoremSmall
