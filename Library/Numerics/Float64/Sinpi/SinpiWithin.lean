import Library.Numerics.Float64.Sinpi.SinpiTiny
import Library.Numerics.Float64.Sinpi.SinpiCosFloor
import Library.Numerics.Float64.Sinpi.SinpiTanpi

/-!
The one-step bounds of `Sinpi.sinpi`, `Sinpi.cospi`, and `Sinpi.tanpi` for every finite input,
the last away from an integer plus `1/2`, where `Real.tan` is 0 and `tanpi` gives `±∞`.  From
`2 ^ 52` on, an input is an integer: `cospi` gives `±1` by the parity of its lowest bit below
`2 ^ 53` and 1 above, and `tanpi` gives `±0`.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiWithin

open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Trig.TrigSinCos Library.Numerics.Float64.Tan.TanBigWords Library.Numerics.Float64.Tan.TanWith SinpiBits SinpiFloor
  SinpiPieces SinpiCommon SinpiReflect SinpiSin SinpiKernels SinpiTanKernel SinpiCos
  SinpiCosFloor SinpiTanpi SinpiTiny

set_option exponentiation.threshold 1200

theorem high53 (x : Float) (hxf : Finite x.toBits) :
    (x.toBits >>> 32) &&& 0x7fffffff < 0x43400000 ↔ |value x.toBits| < 2 ^ 53 := by
  obtain ⟨hs, -, hv, -, hix, -⟩ := abs_facts x hxf
  have c : value (0x4340000000000000 : UInt64) = 2 ^ 53 := by
    rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ (2 ^ 53) 0 (by norm_num) (by decide +kernel)]
    norm_num
  rw [← hv, ← c, high_lt _ _ 0x43400000 0x4340000000000000 hix hs (by decide) (by decide)]

/-- From `2 ^ 52` below `2 ^ 53`, `|x|` is an integer whose parity is the lowest bit of `x`. -/
theorem big_parity (x : Float) (hxf : Finite x.toBits) (h1 : 2 ^ 52 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 2 ^ 53) :
    ∃ N : Nat, |value x.toBits| = N ∧
      (x.toBits &&& 0xFFFFFFFF &&& 1 != 0) = decide (N % 2 = 1) := by
  obtain ⟨hs, -, hv, -, -, hlx⟩ := abs_facts x hxf
  have hpos : 0 < value x.abs.toBits := by
    rw [hv]; linarith [show (0 : ℝ) < 2 ^ 52 by positivity]
  have he1 : 1075 ≤ Wasm.IEEE64.exponent x.abs.toBits := by
    by_contra hc
    have h := F64SignedNearestSum.grid_bound x.abs.toBits
    rw [abs_of_pos hpos, hv] at h
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 ≤ 2 ^ 52 := by
      rw [div_le_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have he2 : Wasm.IEEE64.exponent x.abs.toBits ≤ 1075 := by
    by_contra hc
    have h := F64SignedNearestSum.grid_lower x.abs.toBits (by omega)
    rw [abs_of_pos hpos, hv] at h
    have : (2 : ℝ) ^ 53 ≤ 2 ^ (52 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hne : (Wasm.IEEE64.exponent x.abs.toBits == 0) = false := by simp; omega
  have hm : Wasm.IEEE64.scaledMagnitude x.abs.toBits =
      (2 ^ 52 + Wasm.IEEE64.fraction x.abs.toBits) * 2 ^ 1074 := by
    simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ite_false,
      show Wasm.IEEE64.exponent x.abs.toBits - 1 = 1074 by omega]
  have hfr : Wasm.IEEE64.fraction x.abs.toBits = x.abs.toBits.toNat % 2 ^ 52 := rfl
  refine ⟨2 ^ 52 + Wasm.IEEE64.fraction x.abs.toBits, ?_, ?_⟩
  · rw [← hv, ← abs_of_pos hpos, F64RoundNearest.abs_value, hm, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, mul_div_cancel_right₀ _ (by positivity)]
  · have hl : (x.toBits &&& 0xFFFFFFFF &&& 1).toNat = x.abs.toBits.toNat % 2 := by
      rw [UInt64.toNat_and, hlx, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
      omega
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, ← UInt64.toNat_inj, hl,
      show (0 : UInt64).toNat = 0 from rfl, hfr]
    omega

/-- From `2 ^ 53` on, a finite word is an even integer. -/
theorem big_even (w : UInt64) (h : 2 ^ 53 ≤ |value w|) : ∃ n : Nat, |value w| = 2 * n := by
  have hl := F64SignedNearestSum.grid_bound w
  have he : 1076 ≤ Wasm.IEEE64.exponent w := by
    by_contra hc
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent w - 1)) / 2 ^ 1074 ≤ 2 ^ 53 := by
      rw [div_le_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨m, hm, -⟩ := mag_split w
  obtain ⟨k, hk⟩ : ∃ k, Wasm.IEEE64.exponent w - 1 = k + 1075 :=
    ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
  refine ⟨m * 2 ^ k, ?_⟩
  rw [F64RoundNearest.abs_value, hm, hk, pow_add]
  push_cast
  ring

/-- `cospi` from `2 ^ 52` on. -/
theorem cospi_big (x : Float) (hxf : Finite x.toBits) (h : 2 ^ 52 ≤ |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * value x.toBits))
      (Sinpi.cospi x).toBits := by
  obtain ⟨c1, -, c52, cinf⟩ := abs_thresholds x hxf
  obtain ⟨o1, on1, vn1, fn1⟩ := one_negOne
  obtain ⟨-, -, -, -, -, v1, -, -, f1⟩ := quarter_facts
  rw [cos_abs_pi]
  unfold Sinpi.cospi
  dsimp only
  rw [if_neg (fun h' => by linarith [c1.mp h']), if_neg (fun h' => by linarith [c52.mp h']),
    if_neg cinf]
  by_cases h53 : |value x.toBits| < 2 ^ 53
  · rw [if_pos ((high53 x hxf).mpr h53)]
    obtain ⟨N, hN, hp⟩ := big_parity x hxf h h53
    rw [hp, hN, show Real.pi * (N : ℝ) = N * Real.pi by ring, Real.cos_nat_mul_pi]
    by_cases hodd : N % 2 = 1
    · rw [decide_eq_true hodd, if_pos rfl, on1, Odd.neg_one_pow (Nat.odd_iff.mpr hodd)]
      exact pm_one _ _ fn1 vn1 (by norm_num)
    · rw [decide_eq_false hodd, if_neg (show ¬((false : Bool) = true) by decide), o1,
        Even.neg_one_pow (Nat.even_iff.mpr (by omega))]
      exact pm_one _ _ f1 v1 (by norm_num)
  · rw [if_neg (fun h' => h53 ((high53 x hxf).mp h')), o1]
    obtain ⟨n, hn⟩ := big_even x.toBits (not_lt.mp h53)
    rw [hn, show Real.pi * (2 * (n : ℝ)) = n * (2 * Real.pi) by ring, Real.cos_nat_mul_two_pi]
    exact pm_one _ _ f1 v1 (by norm_num)

/-- A word of `±0` is within one step of 0. -/
theorem pm_zero (w : UInt64) (h : w = 0 ∨ w = 0x8000000000000000) :
    F64SignedRounding.WithinSteps 1 0 w := by
  rcases h with h | h <;> rw [h] <;> exact F64SelfStep.zero_step _ (by decide)

/-- `tanpi` from `2 ^ 52` on. -/
theorem tanpi_big (x : Float) (hxf : Finite x.toBits) (h : 2 ^ 52 ≤ |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits))
      (Sinpi.tanpi x).toBits := by
  obtain ⟨c1, -, c52, cinf⟩ := abs_thresholds x hxf
  obtain ⟨n, hn⟩ := big_integer x.toBits h
  unfold Sinpi.tanpi
  dsimp only
  rw [if_neg (fun h' => by linarith [c1.mp h']), if_neg (fun h' => by linarith [c52.mp h']),
    if_neg cinf, hn, tan_int]
  apply pm_zero
  split_ifs <;> simp only [F64Bits.toBits_neg, (zero_bits').1] <;> decide +kernel

/-- `sinpi` for every finite input. -/
theorem sinpi_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits))
      (Sinpi.sinpi x).toBits := by
  rcases lt_or_ge |value x.toBits| (1 / 2 ^ 29) with h1 | h1
  · exact sinpi_tiny x hxf h1
  rcases lt_or_ge |value x.toBits| 1 with h2 | h2
  · exact sinpi_mid x hxf h1 h2
  rcases lt_or_ge |value x.toBits| (2 ^ 52) with h3 | h3
  · exact sinpi_floor x hxf h2 h3
  · exact sinpi_big x hxf h3

/-- `cospi` for every finite input. -/
theorem cospi_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * value x.toBits))
      (Sinpi.cospi x).toBits := by
  rcases lt_or_ge |value x.toBits| 1 with h2 | h2
  · exact cospi_small x hxf h2
  rcases lt_or_ge |value x.toBits| (2 ^ 52) with h3 | h3
  · exact cospi_floor x hxf h2 h3
  · exact cospi_big x hxf h3

/-- `tanpi` for every finite input that is not an integer plus `1/2`. -/
theorem tanpi_within (x : Float) (hxf : Finite x.toBits)
    (hh : ∀ n : Int, value x.toBits ≠ n + 1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits))
      (Sinpi.tanpi x).toBits := by
  have hh' : ∀ N : Nat, |value x.toBits| ≠ N + 1 / 2 := by
    intro N hN
    rcases abs_choice (value x.toBits) with h | h
    · exact hh N (by push_cast; linarith)
    · exact hh (-(N : Int) - 1) (by push_cast; linarith)
  rcases lt_or_ge |value x.toBits| (1 / 2 ^ 29) with h1 | h1
  · exact tanpi_tiny x hxf h1
  rcases lt_or_ge |value x.toBits| 1 with h2 | h2
  · exact tanpi_mid x hxf h1 h2 (by simpa using hh' 0)
  rcases lt_or_ge |value x.toBits| (2 ^ 52) with h3 | h3
  · exact tanpi_floor x hxf h2 h3 hh'
  · exact tanpi_big x hxf h3

#print axioms cospi_big
#print axioms tanpi_big
#print axioms sinpi_within
#print axioms cospi_within
#print axioms tanpi_within

end Library.Numerics.Float64.Sinpi.SinpiWithin
