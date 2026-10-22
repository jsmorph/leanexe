import Library.Numerics.Float64.Tanh.Expm1FormWords

/-!
Subtracting 1 from a nonnegative word of value at least `2 ^ 55` returns the word, in every binade
up to the top one.  The exact difference lies within `2 ^ 1074` scaled units of the word's scaled
magnitude, far below half its spacing, so the rounding returns the word: within the binade when the
fraction is nonzero, and with a carry from the binade below when it is zero.
-/

namespace Library.Numerics.Float64.Tanh.Expm1SubOne
open CodeLib.IEEE64 LeanExe.ProofKit Expm1FormWords

set_option exponentiation.threshold 4096

/-- Rounding a magnitude whose significand `R` needs no carry. -/
theorem round_no_carry (n L R : Nat) (hn : 2 ^ 53 ≤ n) (hlog : Nat.log2 n = L)
    (hR : Wasm.IEEE32.roundShift n (L - 52) = R) (hR53 : R ≠ 2 ^ 53)
    (hE : L - 52 + 1 < 0x7FF) :
    Wasm.IEEE64.roundScaledMagnitude false n =
      Wasm.IEEE64.encodeFinite false (L - 52 + 1) (R - 2 ^ 52) := by
  have h52 : ¬ n < 2 ^ 52 := not_lt.mpr (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hn)
  have h53 : ¬ n < 2 ^ 53 := not_lt.mpr hn
  have hb : (R == 2 ^ 53) = false := by simpa using hR53
  unfold Wasm.IEEE64.roundScaledMagnitude
  rw [ite_eq_right h52, ite_eq_right h53]
  simp only [hlog, hR, hb, Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by omega)]

/-- Rounding a magnitude whose significand carries to `2 ^ 53`. -/
theorem round_carry (n L : Nat) (hn : 2 ^ 53 ≤ n) (hlog : Nat.log2 n = L)
    (hR : Wasm.IEEE32.roundShift n (L - 52) = 2 ^ 53) (hE : L - 52 + 2 < 0x7FF) :
    Wasm.IEEE64.roundScaledMagnitude false n =
      Wasm.IEEE64.encodeFinite false (L - 52 + 2) 0 := by
  have h52 : ¬ n < 2 ^ 52 := not_lt.mpr (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hn)
  have h53 : ¬ n < 2 ^ 53 := not_lt.mpr hn
  unfold Wasm.IEEE64.roundScaledMagnitude
  rw [ite_eq_right h52, ite_eq_right h53]
  simp only [hlog, hR, beq_self_eq_true, ite_true]
  rw [ite_eq_right (by omega), Nat.sub_self]

/-! Natural-number facts.  `omega` exceeds its recursion limit on facts with coefficients near
`2 ^ 52`, so these use monotonicity lemmas. -/

theorem diff_lower_pos (f P Q : Nat) (hf1 : 1 ≤ f) (hQ : Q ≤ P) :
    2 ^ 52 * P ≤ (2 ^ 52 + f) * P - Q := by
  rw [Nat.add_mul]
  exact Nat.le_sub_of_add_le (Nat.add_le_add_left (hQ.trans (Nat.le_mul_of_pos_left P hf1)) _)

theorem diff_upper (f P Q : Nat) (hf : f < 2 ^ 52) (hP : 0 < P) :
    (2 ^ 52 + f) * P - Q < 2 ^ 53 * P :=
  lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.mul_lt_mul_of_pos_right ((Nat.add_lt_add_left hf _).trans_eq (by norm_num)) hP)

theorem diff_lower_zero (P Q : Nat) (hQ : Q ≤ P) : 2 ^ 51 * P ≤ 2 ^ 52 * P - Q := by
  apply Nat.le_sub_of_add_le
  calc 2 ^ 51 * P + Q ≤ 2 ^ 51 * P + 2 ^ 51 * P :=
        Nat.add_le_add_left (hQ.trans (Nat.le_mul_of_pos_left P (by norm_num))) _
    _ = 2 ^ 52 * P := by ring

theorem log2_of_bounds (n L : Nat) (hl : 2 ^ L ≤ n) (hu : n < 2 ^ (L + 1)) : Nat.log2 n = L :=
  (Nat.log2_eq_iff (Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos L) hl))).2 ⟨hl, hu⟩

/-- The rounding of `(2 ^ 52 + f) 2 ^ (e - 1) - 2 ^ 1074`. -/
theorem diff_round (e f : Nat) (he : 1078 ≤ e) (hf : f < 2 ^ 52) :
    2 ^ 53 ≤ (2 ^ 52 + f) * 2 ^ (e - 1) - 2 ^ 1074 ∧
    (1 ≤ f → Nat.log2 ((2 ^ 52 + f) * 2 ^ (e - 1) - 2 ^ 1074) = 51 + e ∧
      Wasm.IEEE32.roundShift ((2 ^ 52 + f) * 2 ^ (e - 1) - 2 ^ 1074) (e - 1) = 2 ^ 52 + f) ∧
    (f = 0 → Nat.log2 ((2 ^ 52 + f) * 2 ^ (e - 1) - 2 ^ 1074) = 50 + e ∧
      Wasm.IEEE32.roundShift ((2 ^ 52 + f) * 2 ^ (e - 1) - 2 ^ 1074) (e - 2) = 2 ^ 53) := by
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (e - 1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ 1074 := ⟨_, rfl⟩
  rw [← hP, ← hQ]
  have hQP32 : Q * 2 ^ 3 ≤ P := by
    rw [hQ, hP, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQP : Q ≤ P := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hQP32
  have hP0 : 0 < P := by rw [hP]; positivity
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hQlt : Q ≤ (2 ^ 52 + f) * P := hQP.trans (Nat.le_mul_of_pos_left P (by positivity))
  have h51 : 2 ^ 51 * P ≤ (2 ^ 52 + f) * P - Q :=
    le_trans (diff_lower_zero P Q hQP) (Nat.sub_le_sub_right
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _)
  have hP4 : 4 ≤ P := by rw [hP]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
    (show 2 ≤ e - 1 by omega))
  refine ⟨le_trans (by calc 2 ^ 53 = 2 ^ 51 * 4 := by norm_num
      _ ≤ 2 ^ 51 * P := Nat.mul_le_mul_left _ hP4) h51, ?_, ?_⟩
  · intro hf1
    have hlow : 2 ^ (51 + e) ≤ (2 ^ 52 + f) * P - Q := by
      refine le_trans ?_ (diff_lower_pos f P Q hf1 hQP)
      rw [hP, ← pow_add, show 52 + (e - 1) = 51 + e by omega]
    have hupp : (2 ^ 52 + f) * P - Q < 2 ^ (51 + e + 1) := by
      refine lt_of_lt_of_le (diff_upper f P Q hf hP0) (le_of_eq ?_)
      rw [hP, ← pow_add, show 53 + (e - 1) = 51 + e + 1 by omega]
    refine ⟨log2_of_bounds _ _ hlow hupp, ?_⟩
    apply roundShift_eq _ _ _ (by omega)
    have hd : (((2 ^ 52 + f) * 2 ^ (e - 1) : Nat) : ℤ) - (((2 ^ 52 + f) * P - Q : Nat) : ℤ) =
        (Q : ℤ) := by
      rw [← hP, Nat.cast_sub hQlt]
      ring
    rw [hd, abs_of_pos (by exact_mod_cast hQ0)]
    have h3 : (Q : ℤ) * 2 ^ 3 ≤ 2 ^ (e - 1) := by rw [hP] at hQP32; exact_mod_cast hQP32
    have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ0
    nlinarith
  · intro hf0
    subst hf0
    have hP2 : P = 2 * 2 ^ (e - 2) := by
      rw [hP, ← pow_succ']; congr 1; omega
    have hlow : 2 ^ (50 + e) ≤ (2 ^ 52 + 0) * P - Q := by
      rw [add_zero]
      refine le_trans ?_ (diff_lower_zero P Q hQP)
      rw [hP, ← pow_add, show 51 + (e - 1) = 50 + e by omega]
    have hupp : (2 ^ 52 + 0) * P - Q < 2 ^ (50 + e + 1) := by
      rw [add_zero]
      refine lt_of_lt_of_le (Nat.sub_lt (Nat.mul_pos (by norm_num) hP0) hQ0) (le_of_eq ?_)
      rw [hP, ← pow_add, show 52 + (e - 1) = 50 + e + 1 by omega]
    refine ⟨log2_of_bounds _ _ hlow hupp, ?_⟩
    apply roundShift_eq _ _ _ (by omega)
    have hd : ((2 ^ 53 * 2 ^ (e - 2) : Nat) : ℤ) - (((2 ^ 52 + 0) * P - Q : Nat) : ℤ) = (Q : ℤ) := by
      have hQ2 : Q ≤ (2 ^ 52 + 0) * P := by rw [add_zero]; exact hQP.trans (Nat.le_mul_of_pos_left P (by positivity))
      rw [Nat.cast_sub hQ2, hP2]
      push_cast
      ring
    rw [hd, abs_of_pos (by exact_mod_cast hQ0)]
    have h3 : (Q : ℤ) * 2 ^ 3 ≤ 2 * 2 ^ (e - 2) := by rw [hP2] at hQP32; exact_mod_cast hQP32
    have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ0
    nlinarith

/-- Subtracting 1 from a nonnegative word from `2 ^ 55` on returns the word, in every binade up to
the top one. -/
theorem sub_one_large (v : UInt64) (hvf : Finite v) (hs : Wasm.IEEE64.sign v = false)
    (he : 1078 ≤ Wasm.IEEE64.exponent v) :
    Wasm.IEEE64.sub v 0x3FF0000000000000 = v := by
  have hv63 : v.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs; exact hs
  have hvf' := hvf
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hvf'
  have hel : Wasm.IEEE64.exponent v < 2047 := by
    have : Wasm.IEEE64.exponent v < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
    omega
  have hfl : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hbig, hpos, hzero⟩ := diff_round _ _ he hfl
  set e := Wasm.IEEE64.exponent v with hedef
  set f := Wasm.IEEE64.fraction v with hfdef
  set n := (2 ^ 52 + f) * 2 ^ (e - 1) - 2 ^ 1074 with hn
  have hneg1 : Wasm.IEEE64.negate 0x3FF0000000000000 = 0xBFF0000000000000 := by decide
  have h1f : Finite (0xBFF0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have h1s : Wasm.IEEE64.scaledValue (0xBFF0000000000000 : UInt64) = -((2 ^ 1074 : Nat) : ℤ) := by
    decide +kernel
  have hvs : Wasm.IEEE64.scaledValue v = (((2 ^ 52 + f) * 2 ^ (e - 1) : Nat) : ℤ) := by
    simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, ← hedef, ← hfdef]
    simp [show e ≠ 0 by omega]
  have hQlt : 2 ^ 1074 ≤ (2 ^ 52 + f) * 2 ^ (e - 1) := by
    have := hbig
    omega
  have hz : Wasm.IEEE64.scaledValue v + Wasm.IEEE64.scaledValue 0xBFF0000000000000 = (n : ℤ) := by
    rw [hvs, h1s, hn, Nat.cast_sub hQlt]
    ring
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hbig
  have hadd : Wasm.IEEE64.sub v 0x3FF0000000000000 = Wasm.IEEE64.roundScaledMagnitude false n := by
    unfold Wasm.IEEE64.sub
    rw [hneg1]
    simp only [Wasm.IEEE64.add, not_nan_of_finite hvf, not_nan_of_finite h1f,
      not_infinite_of_finite hvf, not_infinite_of_finite h1f, hz]
    have hne : ((n : ℤ) == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact_mod_cast hnpos.ne'
    have hcond : ¬ ((n : ℤ) == 0) = true := by rw [hne]; exact Bool.false_ne_true
    have hdec : decide ((n : ℤ) < 0) = false :=
      decide_eq_false (not_lt.mpr (Int.natCast_nonneg n))
    rw [ite_eq_right hcond, hdec, Int.natAbs_natCast]
    simp only [Bool.or_self, Bool.false_eq_true, ite_false]
  rw [hadd]
  have hvenc := encode_self v hv63
  rcases Nat.eq_zero_or_pos f with hf0 | hf1
  · obtain ⟨hlog, hr⟩ := hzero hf0
    rw [round_carry n (50 + e) hbig hlog (by rw [show 50 + e - 52 = e - 2 by omega]; exact hr)
      (by omega), show 50 + e - 52 + 2 = e by omega]
    rw [← hf0]
    exact hvenc
  · obtain ⟨hlog, hr⟩ := hpos hf1
    rw [round_no_carry n (51 + e) (2 ^ 52 + f) hbig hlog
      (by rw [show 51 + e - 52 = e - 1 by omega]; exact hr) (by omega) (by omega),
      show 51 + e - 52 + 1 = e by omega, Nat.add_sub_cancel_left]
    exact hvenc

#print axioms round_no_carry
#print axioms round_carry
#print axioms diff_round
#print axioms sub_one_large

end Library.Numerics.Float64.Tanh.Expm1SubOne
