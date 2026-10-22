import Library.Numerics.Float64.Sinpi.SinpiExact

/-!
The exact results of `Sinpi.tanpi` as bit equalities.  An integer `n` gives `±0`, with the sign
of `x` for even `n` and the other sign for odd `n`.  An integer plus `1/2`, `n + 1/2`, gives `+∞`
for even `n` and `-∞` for odd `n`.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiExactTan

open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Trig.TrigSinCos Library.Numerics.Float64.Tan.TanBigWords Library.Numerics.Float64.Tan.TanWith SinpiBits SinpiFloor
  SinpiPieces SinpiCommon SinpiReflect SinpiSin SinpiKernels SinpiTanKernel SinpiCos
  SinpiCosFloor SinpiTanpi SinpiTiny SinpiWithin SinpiExact

set_option exponentiation.threshold 1200

/-- `±t` by a sign, for `t` of `±0` by a second sign. -/
theorem signed_odd (s c : Bool) (t : Float)
    (ht : t.toBits = if c = true then 0x8000000000000000 else 0) :
    (if s = true then -t else t).toBits =
      if (s != c) = true then 0x8000000000000000 else 0 := by
  cases s
  · rw [if_neg (show ¬((false : Bool) = true) by decide), ht]
    cases c <;> decide
  · rw [if_pos rfl, F64Bits.toBits_neg, ht]
    cases c <;> decide +kernel

/-- `±t` by a sign, for `t` of `±∞` by a second sign. -/
theorem signed_inf (s c : Bool) (t : Float)
    (ht : t.toBits = if c = true then 0xFFF0000000000000 else 0x7FF0000000000000) :
    (if s = true then -t else t).toBits =
      if (s != c) = true then 0xFFF0000000000000 else 0x7FF0000000000000 := by
  cases s
  · rw [if_neg (show ¬((false : Bool) = true) by decide), ht]
    cases c <;> decide
  · rw [if_pos rfl, F64Bits.toBits_neg, ht]
    cases c <;> decide +kernel

theorem float_facts : (-1.0 : Float) < 0.0 ∧ ¬ (1.0 : Float) < 0.0 ∧
    (1.0 / 0.0 : Float).toBits = 0x7FF0000000000000 ∧
    (-1.0 / 0.0 : Float).toBits = 0xFFF0000000000000 := by
  obtain ⟨o1, on1, vn1, fn1⟩ := one_negOne
  obtain ⟨-, -, -, -, -, v1, -, -, f1⟩ := quarter_facts
  obtain ⟨z1, -⟩ := zero_bits'
  obtain ⟨f0, v0⟩ := zero_float
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [flt_iff (-1.0) 0.0 (by rw [on1]; exact fn1) f0, on1, vn1, v0]
    norm_num
  · rw [flt_iff 1.0 0.0 (by rw [o1]; exact f1) f0, o1, v1, v0]
    norm_num
  · rw [F64Bits.toBits_div, o1, z1]
    decide +kernel
  · rw [F64Bits.toBits_div, on1, z1]
    decide +kernel

/-- `odd` of `s_tanpi.c` from the parity of the integer part. -/
theorem odd_float (fl : Float) (N : Nat) (hf : Finite fl.toBits) (hv : value fl.toBits = N)
    (h1 : 1 ≤ N) (h2 : N < 2 ^ 52) :
    (if fl.toUInt64 &&& 1 == 1 then (-1.0 : Float) else 1.0) =
      if decide (N % 2 = 1) = true then -1.0 else 1.0 := by
  rw [toUInt64_int fl N hf hv h1 (by omega), parity N (by omega)]

/-- The sign of a word with a negative value. -/
theorem sign_neg (w : UInt64) (h : value w < 0) : Wasm.IEEE64.sign w = true := by
  rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign w) with hs | hs
  · exact hs
  · have := sign_false w hs
    have := abs_nonneg (value w)
    linarith

/-- The sign of a word with a positive value. -/
theorem sign_pos (w : UInt64) (h : 0 < value w) : Wasm.IEEE64.sign w = false :=
  (F64RelativeStepLow.pos_word w h).1

/-- The parity of `|n|` is that of `n`. -/
theorem parity_abs (n : Int) (N : Nat) (h : (N : ℤ) = |n|) :
    decide (N % 2 = 1) = decide (n % 2 = 1) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  rcases abs_cases n with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at h <;> omega

/-- `tanpi` of an integer `n` is `±0`: the sign of `x` for even `n`, the other sign for odd `n`. -/
theorem tanpi_int (x : Float) (hxf : Finite x.toBits) (n : Int) (hn : value x.toBits = n) :
    (Sinpi.tanpi x).toBits =
      if (Wasm.IEEE64.sign x.toBits != decide (n % 2 = 1)) = true then 0x8000000000000000
      else 0 := by
  obtain ⟨c1, c29, c52, cinf⟩ := abs_thresholds x hxf
  obtain ⟨f0, v0⟩ := zero_float
  obtain ⟨z1, z2⟩ := zero_bits'
  obtain ⟨hneg1, hone, -, -⟩ := float_facts
  have hN : ∀ N : Nat, |value x.toBits| = N → (N : ℤ) = |n| := by
    intro N h
    rw [hn, ← Int.cast_abs] at h
    exact_mod_cast h.symm
  unfold Sinpi.tanpi
  dsimp only
  rw [ax_abs, neg_flag]
  by_cases h0 : value x.toBits = 0
  · have ha : |value x.toBits| = 0 := by rw [h0, abs_zero]
    have hn0 : n = 0 := by
      have : (n : ℝ) = 0 := by rw [← hn, h0]
      exact_mod_cast this
    rw [if_pos (c1.mpr (by rw [ha]; norm_num)), if_pos (c29.mpr (by rw [ha]; positivity)),
      if_pos ((feq_iff x 0.0 hxf f0).mpr (by rw [h0, v0])), hn0,
      show decide ((0 : ℤ) % 2 = 1) = false by decide, Bool.bne_false]
    exact zero_word _ h0
  have h1 := int_one_le _ n hn h0
  rw [if_neg (fun h' => by linarith [c1.mp h'])]
  by_cases h52 : |value x.toBits| < 2 ^ 52
  · rw [if_pos (c52.mpr h52)]
    obtain ⟨N, hN1, hN52, hNv, hflf, -, -, -, hcase⟩ := floor_frac x hxf h1 h52
    generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P
      at *
    obtain ⟨fl, j0⟩ := P
    dsimp only at *
    rcases hcase with ⟨heq, hz⟩ | ⟨hgt, hlt, -⟩
    · rw [hz, show (0 : UInt64) >>> 32 = 0 by decide,
        if_pos (show (0 : UInt64) < 0x3fe00000 by decide),
        if_pos (show ((0 : UInt64) == 0) = true by decide), odd_float fl N hflf hNv hN1 hN52,
        ← parity_abs n N (hN N heq)]
      apply signed_odd
      by_cases hp : N % 2 = 1
      · rw [decide_eq_true hp, if_pos rfl, if_pos hneg1, if_pos rfl, z2]
      · rw [decide_eq_false hp, if_neg (show ¬((false : Bool) = true) by decide), if_neg hone,
          if_neg (show ¬((false : Bool) = true) by decide), z1]
    · exact (not_frac _ n N hn hgt hlt).elim
  · rw [if_neg (fun h' => h52 (c52.mp h')), if_neg cinf]
    have h52' := not_lt.mp h52
    by_cases h53 : |value x.toBits| < 2 ^ 53
    · obtain ⟨N, hNx, hp⟩ := big_parity x hxf h52' h53
      have hlt := UInt64.lt_iff_toNat_lt.mp ((high53 x hxf).mpr h53)
      rw [if_neg (show ¬((x.toBits >>> 32) &&& 0x7fffffff ≥ 0x43400000) from
          fun h' => by have := UInt64.le_iff_toNat_le.mp h'; omega), hp,
        ← parity_abs n N (hN N hNx)]
      exact signed_odd _ _ _ (signed_zero _)
    · obtain ⟨k, hk⟩ := big_even x.toBits (not_lt.mp h53)
      have he : decide (n % 2 = 1) = false := by
        have : ((2 * k : ℕ) : ℤ) = |n| := by
          rw [hn, ← Int.cast_abs] at hk
          exact_mod_cast hk.symm
        rw [decide_eq_false_iff_not]
        rcases abs_cases n with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at this <;> push_cast at this <;>
          omega
      rw [if_pos (ge_of_not_lt _ _ (fun h' => h53 ((high53 x hxf).mp h'))), he]
      exact signed_odd _ _ _ (by rw [z1]; decide)

/-- `tanpi` of `n + 1/2` is `+∞` for even `n` and `-∞` for odd `n`. -/
theorem tanpi_half (x : Float) (hxf : Finite x.toBits) (n : Int)
    (hn : value x.toBits = n + 1 / 2) :
    (Sinpi.tanpi x).toBits = if n % 2 = 1 then 0xFFF0000000000000 else 0x7FF0000000000000 := by
  obtain ⟨hs, hf, hv, -, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, c29, c52, -⟩ := abs_thresholds x hxf
  obtain ⟨-, t2, -⟩ := thresholds x.abs _ |value x.toBits| hix hs hv
  obtain ⟨-, -, hinf, hninf⟩ := float_facts
  obtain ⟨M, hM⟩ := half_nat _ n hn
  have h52 := half_small x n hn
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  -- The sign of `x` against `n`.
  have hsg : Wasm.IEEE64.sign x.toBits = decide (n < 0) := by
    rcases lt_or_ge n 0 with h | h
    · rw [decide_eq_true h]
      apply sign_neg
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith
    · rw [decide_eq_false (not_lt.mpr h)]
      apply sign_pos
      have : (0 : ℝ) ≤ n := by exact_mod_cast h
      linarith
  have hMn : (M : ℤ) = if n < 0 then -n - 1 else n := by
    have hM' := hM
    rw [hn] at hM'
    split_ifs with h
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      rw [abs_of_neg (by linarith)] at hM'
      have : (M : ℝ) = ((-n - 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : (0 : ℝ) ≤ n := by exact_mod_cast (not_lt.mp h)
      rw [abs_of_nonneg (by linarith)] at hM'
      have : (M : ℝ) = (n : ℝ) := by linarith
      exact_mod_cast this
  have hpar : (Wasm.IEEE64.sign x.toBits != decide (M % 2 = 1)) = decide (n % 2 = 1) := by
    rw [hsg, Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_iff]
    split_ifs at hMn <;> omega
  rw [show (if n % 2 = 1 then (0xFFF0000000000000 : UInt64) else 0x7FF0000000000000) =
      if decide (n % 2 = 1) = true then 0xFFF0000000000000 else 0x7FF0000000000000 by
    simp only [decide_eq_true_eq], ← hpar]
  unfold Sinpi.tanpi
  dsimp only
  rw [ax_abs, neg_flag]
  by_cases h1 : |value x.toBits| < 1
  · have hM1 : M = 0 := by
      have : (M : ℝ) < 1 := by linarith
      have : M < 1 := by exact_mod_cast this
      omega
    rw [hM1] at hM ⊢
    rw [Nat.cast_zero, zero_add] at hM
    rw [if_pos (c1.mpr h1), if_neg (fun h' => by linarith [c29.mp h']),
      if_neg (show ¬((x.toBits >>> 32) &&& 0x7fffffff < 0x3fe00000) from
        fun h' => by linarith [t2.mp h']),
      if_pos ((beq_half _ hf).trans (by rw [hv, hM]; simp)),
      show decide (0 % 2 = 1) = false by decide]
    exact signed_inf _ _ _ (by rw [hinf]; rfl)
  · rw [if_neg (fun h' => h1 (c1.mp h')), if_pos (c52.mpr h52)]
    obtain ⟨N, hN1, hN52, hNv, hflf, -, hdf, hdv, hcase⟩ :=
      floor_frac x hxf (not_lt.mp h1) h52
    generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P
      at *
    obtain ⟨fl, j0⟩ := P
    dsimp only at *
    have hMN : M = N := by
      rcases hcase with ⟨heq, -⟩ | ⟨hgt, hlt, -⟩
      · exfalso
        rw [hM] at heq
        have : (2 * M + 1 : ℤ) = 2 * N := by
          have : (2 * (M : ℝ) + 1) = 2 * N := by linarith
          exact_mod_cast this
        omega
      · rw [hM] at hgt hlt
        have a1 : N < M + 1 := by
          have : (N : ℝ) < M + 1 := by linarith [show (0 : ℝ) < 1 / 2 ^ 52 by positivity]
          exact_mod_cast this
        have a2 : M < N + 1 := by
          have : (M : ℝ) < N + 1 := by linarith
          exact_mod_cast this
        omega
    have hF : |value x.toBits| - N = 1 / 2 := by rw [hM, hMN]; ring
    obtain ⟨-, t2', -⟩ := thresholds (x.abs - fl) ((x.abs - fl).toBits >>> 32)
      (|value x.toBits| - N) (by rw [Library.Numerics.Float64.Trig.TrigWords.shr_toNat]; rfl)
      (SinpiReflect.pos_toNat _ (by rw [hdv, hF]; norm_num)) hdv
    rw [if_neg (show ¬((x.abs - fl).toBits >>> 32 < 0x3fe00000) from
        fun h' => by linarith [t2'.mp h']), beq_half _ hdf, hdv, hF,
      if_pos (show decide ((1 : ℝ) / 2 = 1 / 2) = true by simp),
      odd_float fl N hflf hNv hN1 hN52, hMN]
    apply signed_inf
    by_cases hp : N % 2 = 1
    · rw [decide_eq_true hp, if_pos rfl, if_pos rfl, hninf]
    · rw [decide_eq_false hp, if_neg (show ¬((false : Bool) = true) by decide),
        if_neg (show ¬((false : Bool) = true) by decide), hinf]

#print axioms tanpi_int
#print axioms tanpi_half

end Library.Numerics.Float64.Sinpi.SinpiExactTan
