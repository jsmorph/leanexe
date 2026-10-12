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
    (hTH2 : TH ≤ 2) (hgr : gr ≤ 1023) (hgs : gs ≤ 1023)
    (hhr : 2 ^ gr / 2 / 2 ^ 1074 ≤ hr) (hhs : 2 ^ gs / 2 / 2 ^ 1074 ≤ hs)
    (hR : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075) < 2 ^ (53 + gr) / 2 ^ 1074)
    (hSLm0 : 0 < SLm)
    (hSLm : SLm ^ 2 ≤ 2 * TL + TL * TL - (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr))
    (hS : 2 * TH + TH * TH + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) <
      (2 ^ (53 + gs) / 2 ^ 1074) ^ 2) :
    Finite (2.0 * t + t * t).sqrt.toBits ∧
      |value (2.0 * t + t * t).sqrt.toBits - Real.sqrt (2 * value t.toBits + value t.toBits * value t.toBits)| ≤
        hs + (TH * TH / 2 ^ 53 + 1 / 2 ^ 1075 + hr) / (2 * SLm) := by
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
    (F64Near.nonzero_of_magnitude _ hrcpos.ne').ne'
  have hsq : Real.sqrt rc < 2 ^ (53 + gs) / 2 ^ 1074 := by
    rw [Real.sqrt_lt' (by positivity)]
    linarith
  have hroot := F64SqrtHalf.sqrt_half _ hr0.1 hmag hsign gs hsq
  rw [← F64Bits.toBits_sqrt] at hroot
  refine ⟨hroot.1, ?_⟩
  -- `|√rc - S| ≤ er/(2 SLm)`
  have hS1 : SLm ≤ Real.sqrt rc := Real.le_sqrt_of_sq_le hrc0
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

#print axioms grid_of_value
#print axioms acosh_t
#print axioms acosh_s
#print axioms add_exact

end Verified.Examples.AcoshTheoremSmall
