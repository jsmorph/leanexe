import Verified.Examples.SinpiCommon

/-!
`Sinpi.sinpi` from `2 ^ -29` on in magnitude: within one step of `sin (π x)` for every finite
`x`.  Below 1 the sine chain runs on `|x|`.  From 1 below `2 ^ 52` it runs on the fraction of
`|x|`, with the sign changed for an odd integer part, and an integer gives `±0`.  From `2 ^ 52`
on every input is an integer and the result is `±0`.  The sign of `x` negates the result.
-/

namespace Verified.Examples.SinpiSin

open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos TanBigWords TanTrunc SinpiBits SinpiFloor
  SinpiPieces SinpiCommon SinpiReflect

set_option exponentiation.threshold 1200

theorem sin_shift (F : ℝ) (N : Nat) :
    Real.sin (Real.pi * (N + F)) = if N % 2 = 1 then -Real.sin (Real.pi * F)
      else Real.sin (Real.pi * F) := by
  rw [show Real.pi * (N + F) = Real.pi * F + N * Real.pi by ring, Real.sin_add_nat_mul_pi]
  split_ifs with h
  · rw [Odd.neg_one_pow (Nat.odd_iff.mpr h)]; ring
  · rw [Even.neg_one_pow (Nat.even_iff.mpr (by omega))]; ring

theorem zero_bits' : (0.0 : Float).toBits = 0 ∧ (-0.0 : Float).toBits = 0x8000000000000000 := by
  refine ⟨by decide, ?_⟩
  rw [F64Bits.toBits_neg, show (0.0 : Float).toBits = 0 by decide]
  decide +kernel

/-- The result of a sign choice between `±0` is within one step of 0. -/
theorem zero_choice (c : Bool) :
    F64SignedRounding.WithinSteps 1 0 (if c = true then -(0.0 : Float) else 0.0).toBits := by
  obtain ⟨z1, z2⟩ := zero_bits'
  split
  · rw [z2]; exact F64SelfStep.zero_step _ (by decide)
  · rw [z1]; exact F64SelfStep.zero_step _ (by decide)

/-- The sign of `x` and the value of `|x|`. -/
theorem sign_cases (x : Float) (hxf : Finite x.toBits) (h0 : value x.toBits ≠ 0) :
    (Wasm.IEEE64.sign x.toBits = true ∧ value x.toBits = -|value x.toBits|) ∨
      (Wasm.IEEE64.sign x.toBits = false ∧ value x.toBits = |value x.toBits|) := by
  rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x.toBits) with h | h
  · exact Or.inl ⟨h, sign_true _ h⟩
  · exact Or.inr ⟨h, sign_false _ h⟩

/-- A signed result from a nonnegative one: `sin (π x)` is odd. -/
theorem signed_sin (x : Float) (hxf : Finite x.toBits) (h0 : value x.toBits ≠ 0) (s : Float)
    (hs : F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * |value x.toBits|)) s.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits))
      (if Wasm.IEEE64.sign x.toBits = true then -s else s).toBits := by
  rcases sign_cases x hxf h0 with ⟨hsg, hv⟩ | ⟨hsg, hv⟩
  · rw [if_pos hsg]
    have := neg_within _ _ hs
    rwa [show Real.pi * value x.toBits = -(Real.pi * |value x.toBits|) by
      conv_lhs => rw [hv]
      ring, Real.sin_neg]
  · rw [if_neg (by rw [hsg]; decide)]
    rwa [show Real.pi * value x.toBits = Real.pi * |value x.toBits| by rw [← hv]]

/-- `sinpi` from `2 ^ -29` below 1. -/
theorem sinpi_mid (x : Float) (hxf : Finite x.toBits) (h1 : 1 / 2 ^ 29 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 1) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits))
      (Sinpi.sinpi x).toBits := by
  obtain ⟨hs, hf, hv, -, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, c29, -, -⟩ := abs_thresholds x hxf
  have h0 : value x.toBits ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; linarith [show (0 : ℝ) < 1 / 2 ^ 29 by positivity]
  unfold Sinpi.sinpi
  dsimp only
  rw [ax_abs, neg_flag, if_pos (c1.mpr h2), if_neg (fun h => by linarith [c29.mp h])]
  apply signed_sin x hxf h0
  exact sin_chain x.abs _ |value x.toBits| hix hs hf hv
    (le_trans (by norm_num) h1) h2

/-- `sinpi` from 1 below `2 ^ 52`. -/
theorem sinpi_floor (x : Float) (hxf : Finite x.toBits) (h1 : 1 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 2 ^ 52) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits))
      (Sinpi.sinpi x).toBits := by
  obtain ⟨hs, hf, hv, hn, hix, hlx⟩ := abs_facts x hxf
  obtain ⟨c1, -, c52, -⟩ := abs_thresholds x hxf
  have h0 : value x.toBits ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; linarith
  -- The exponent of `|x|`.
  have hpos : 0 < value x.abs.toBits := by rw [hv]; linarith
  have he1 : 1023 ≤ Wasm.IEEE64.exponent x.abs.toBits := by
    have := F64SignedNearestSum.grid_bound x.abs.toBits
    rw [abs_of_pos hpos, hv] at this
    by_contra hc
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have he2 : Wasm.IEEE64.exponent x.abs.toBits ≤ 1074 := by
    have := F64SignedNearestSum.grid_lower x.abs.toBits (by omega)
    rw [abs_of_pos hpos, hv] at this
    by_contra hc
    have : (2 : ℝ) ^ 52 ≤ 2 ^ (52 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  unfold Sinpi.sinpi
  dsimp only
  rw [ax_abs, neg_flag, if_neg (fun h => by linarith [c1.mp h]), if_pos (c52.mpr h2)]
  obtain ⟨hj0, hflb⟩ := ffloor_bits x.abs.toBits _ _ hs hix hlx he1 he2
  rcases hff : Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) with
    ⟨fl, j0⟩
  rw [hff] at hj0 hflb
  dsimp only at hj0 hflb ⊢
  obtain ⟨hflf, hfl63, N, hNv, hN1, hN52, hNl, hNu, hNcase⟩ :=
    floor_spec x.abs.toBits fl.toBits hs he1 he2 hflb
  rw [hv] at hNl hNu hNcase
  -- `|x| - fl` is exact.
  have hfl0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hdf, hdv⟩ := sterbenz x.abs.toBits fl.toBits hf hflf
    (by rw [hNv, hv]; exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    (by rw [hNv, hv, abs_of_pos hfl0, abs_abs]; linarith)
    (by rw [hNv, hv, abs_of_pos hfl0, abs_abs]
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        linarith)
    (by omega)
  rw [hNv, hv] at hdv
  have hab : (x.abs - fl).toBits = Wasm.IEEE64.sub x.abs.toBits fl.toBits := F64Bits.toBits_sub _ _
  apply signed_sin x hxf h0
  rcases hNcase with heq | hgt
  · -- An integer: the difference is `+0` and the result is `±0`.
    have hz : (x.abs - fl).toBits = 0 := by
      rw [hab]
      refine sub_self_zero _ _ hf hflf (by
        unfold Wasm.IEEE64.sign
        simp only [decide_eq_false_iff_not, not_le]
        exact hs) ?_
      have h1' : (Wasm.IEEE64.scaledValue x.abs.toBits : ℝ) =
          Wasm.IEEE64.scaledValue fl.toBits := by
        have e1 := TrigSmall.value_of_scaled x.abs.toBits
        have e2 := TrigSmall.value_of_scaled fl.toBits
        rw [hv, heq] at e1
        rw [hNv] at e2
        have : (Wasm.IEEE64.scaledValue x.abs.toBits : ℝ) / 2 ^ 1074 =
            (Wasm.IEEE64.scaledValue fl.toBits : ℝ) / 2 ^ 1074 := by rw [← e1, ← e2]
        exact (div_left_inj' (by positivity)).mp this
      exact_mod_cast h1'
    rw [show (x.abs - fl).toBits >>> 32 = 0 by rw [hz]; rfl,
      if_pos (show ((0 : UInt64) == 0) = true by decide), heq,
      show Real.pi * (N : ℝ) = (N : ℝ) * Real.pi by ring, Real.sin_nat_mul_pi]
    obtain ⟨z1, -⟩ := zero_bits'
    rw [z1]
    exact F64SelfStep.zero_step _ (by decide)
  · -- A fraction from `2 ^ -52` on.
    have hF0 : 1 / 2 ^ 52 ≤ |value x.toBits| - N := by linarith
    have hdpos : 0 < value (x.abs - fl).toBits := by
      rw [hab, hdv]; linarith [show (0 : ℝ) < 1 / 2 ^ 52 by positivity]
    have hd63 := pos_toNat _ hdpos
    have hix0 : ¬ ((x.abs - fl).toBits >>> 32 == 0) = true := by
      intro h
      have h' : (x.abs - fl).toBits >>> 32 = 0 := by simpa using h
      have := congrArg UInt64.toNat h'
      rw [TrigWords.shr_toNat, show (32 : UInt64).toNat % 64 = 32 from rfl,
        UInt64.toNat_zero] at this
      have hlt : (x.abs - fl).toBits.toNat < (0x3CB0000000000000 : UInt64).toNat := by
        show _ < 4372995238176751616
        omega
      have hval := F64PositiveOrder.value_strict (by decide) hlt
      have : value (0x3CB0000000000000 : UInt64) = 1 / 2 ^ 52 := by
        rw [TrigReduce.value_word _ 1 52 (by norm_num) (by decide +kernel)]; norm_num
      rw [this, hab, hdv] at hval
      linarith
    rw [if_neg hix0]
    have hchain := sin_chain (x.abs - fl) ((x.abs - fl).toBits >>> 32) (|value x.toBits| - N)
      (by rw [TrigWords.shr_toNat]; rfl) hd63 (by rw [hab]; exact hdf) (by rw [hab, hdv])
      (le_trans (by norm_num) hF0) (by linarith)
    rw [oddPart_spec fl j0 N hflf hNv hN1 hN52 (by
      intro hj
      rw [hj0] at hj
      have := F64SignedNearestSum.grid_lower x.abs.toBits (by omega)
      rw [abs_of_pos hpos, hv] at this
      have h31 : (2 : ℝ) ^ 31 ≤ 2 ^ (52 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 := by
        rw [le_div_iff₀ (by positivity), ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : (2 : ℝ) ^ 31 < N + 1 := by linarith
      have : 2 ^ 31 < N + 1 := by exact_mod_cast this
      omega)]
    rw [show |value x.toBits| = N + (|value x.toBits| - N) by ring, sin_shift]
    by_cases hp : N % 2 = 1
    · rw [if_pos hp, decide_eq_true hp, if_pos rfl]
      exact neg_within _ _ hchain
    · rw [if_neg hp, decide_eq_false hp, if_neg (by decide)]
      exact hchain

/-- `sinpi` from `2 ^ 52` on. -/
theorem sinpi_big (x : Float) (hxf : Finite x.toBits) (h : 2 ^ 52 ≤ |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits))
      (Sinpi.sinpi x).toBits := by
  obtain ⟨c1, -, c52, cinf⟩ := abs_thresholds x hxf
  obtain ⟨n, hn⟩ := big_integer x.toBits h
  unfold Sinpi.sinpi
  dsimp only
  rw [ax_abs, neg_flag, if_neg (fun h' => by linarith [c1.mp h']),
    if_neg (fun h' => by linarith [c52.mp h']), if_neg cinf, hn,
    show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring, Real.sin_int_mul_pi]
  exact zero_choice _

#print axioms sinpi_mid
#print axioms sinpi_floor
#print axioms sinpi_big

end Verified.Examples.SinpiSin
