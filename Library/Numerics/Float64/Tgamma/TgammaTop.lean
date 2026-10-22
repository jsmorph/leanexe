import LeanExe.ProofKit.F64Saturate
import LeanExe.ProofKit.F64Source
import LeanExe.ProofKit.F64AddNearest
import LeanExe.ProofKit.F64NearestDiv
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64RoundNearest
import LeanExe.ProofKit.F64Bits

/-!
Rounded addition and division up to the overflow threshold.  The ProofKit lemmas for nearest
rounding stop at `2 ^ 1022` or `2 ^ 1023`, while `tgamma` rounds `1/x` and `1/x - 1/2` in the top
binades for subnormal `x`.  `rsm_near` states that `roundScaledMagnitude` gives a finite word
within a relative `2 ^ -53` of every scaled magnitude below `2 ^ 2098 - 2 ^ 2045`, that is, of every
value below `2 ^ 1024 - 2 ^ 971`.  `add_top` and `div_top` follow for sums and quotients, and
`div_overflow` gives the infinity of a quotient of magnitude at least `2 ^ 1024`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaTop
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem enc_spec (neg : Bool) (e f : ℕ) (he1 : 1 ≤ e) (he : e ≤ 2046) (hf : f < 2 ^ 52) :
    Finite (Wasm.IEEE64.encodeFinite neg e f) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite neg e f) = neg ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite neg e f) = (2 ^ 52 + f) * 2 ^ (e - 1) := by
  have hex := F64Source.exponent_encodeFinite neg e f (by omega) hf
  have hfr := F64Source.fraction_encodeFinite neg e f (by omega) hf
  refine ⟨?_, F64Source.sign_encodeFinite neg e f (by omega) hf, ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [hex]
    simp only [bne_iff_ne, ne_eq]
    omega
  · have he0 : (e == 0) = false := by simpa using (show e ≠ 0 by omega)
    simp only [Wasm.IEEE64.scaledMagnitude, hex, hfr, he0, Bool.false_eq_true, ite_false]

theorem enc0_spec (neg : Bool) (f : ℕ) (hf : f < 2 ^ 52) :
    Finite (Wasm.IEEE64.encodeFinite neg 0 f) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite neg 0 f) = neg ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite neg 0 f) = f := by
  have hex := F64Source.exponent_encodeFinite neg 0 f (by norm_num) hf
  have hfr := F64Source.fraction_encodeFinite neg 0 f (by norm_num) hf
  refine ⟨?_, F64Source.sign_encodeFinite neg 0 f (by norm_num) hf, ?_⟩
  · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
    rw [hex]
    decide
  · simp only [Wasm.IEEE64.scaledMagnitude, hex, hfr, beq_self_eq_true, ite_true]

/-- `roundShift` rounds to within half a unit. -/
theorem roundShift_half (n s : ℕ) (hs : 1 ≤ s) :
    2 * |(Wasm.IEEE32.roundShift n s : ℤ) * 2 ^ s - n| ≤ 2 ^ s := by
  have h1 := F64AddNearest.roundShift_nearest n s (n / 2 ^ s) hs
  have h2 := F64AddNearest.roundShift_nearest n s (n / 2 ^ s + 1) hs
  have hd := Nat.div_add_mod n (2 ^ s)
  have hm := Nat.mod_lt n (show 0 < 2 ^ s by positivity)
  have hdZ : (n : ℤ) = 2 ^ s * ((n / 2 ^ s : ℕ) : ℤ) + ((n % 2 ^ s : ℕ) : ℤ) := by
    exact_mod_cast hd.symm
  have hmZ : ((n % 2 ^ s : ℕ) : ℤ) < 2 ^ s := by exact_mod_cast hm
  have hm0 : (0 : ℤ) ≤ ((n % 2 ^ s : ℕ) : ℤ) := by positivity
  have e1 : ((n / 2 ^ s : ℕ) : ℤ) * 2 ^ s - n = -((n % 2 ^ s : ℕ) : ℤ) := by
    linear_combination (-1 : ℤ) * hdZ
  have e2 : ((n / 2 ^ s + 1 : ℕ) : ℤ) * 2 ^ s - n = 2 ^ s - ((n % 2 ^ s : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linear_combination (-1 : ℤ) * hdZ
  rw [e1, abs_neg, abs_of_nonneg hm0] at h1
  rw [e2, abs_of_pos (show (0 : ℤ) < 2 ^ s - ((n % 2 ^ s : ℕ) : ℤ) by linarith)] at h2
  linarith

/-- **Rounding a scaled magnitude** below `2 ^ 2098 - 2 ^ 2045`: a finite word of the given sign
within a relative `2 ^ -53`. -/
theorem rsm_near (neg : Bool) (n : ℕ) (hn : n < 2 ^ 2098 - 2 ^ 2045) :
    Finite (Wasm.IEEE64.roundScaledMagnitude neg n) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude neg n) = neg ∧
      2 ^ 53 * |(Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude neg n) : ℤ) - n| ≤
        n := by
  by_cases h52 : n < 2 ^ 52
  · have key : Wasm.IEEE64.roundScaledMagnitude neg n = Wasm.IEEE64.encodeFinite neg 0 n := by
      unfold Wasm.IEEE64.roundScaledMagnitude
      rw [ite_eq_left h52]
    obtain ⟨hf, hsg, hm⟩ := enc0_spec neg n h52
    rw [key]
    refine ⟨hf, hsg, ?_⟩
    rw [hm]
    simp
  by_cases h53 : n < 2 ^ 53
  · have key : Wasm.IEEE64.roundScaledMagnitude neg n =
        Wasm.IEEE64.encodeFinite neg 1 (n - 2 ^ 52) := by
      unfold Wasm.IEEE64.roundScaledMagnitude
      rw [ite_eq_right h52, ite_eq_left h53]
    obtain ⟨hf, hsg, hm⟩ := enc_spec neg 1 (n - 2 ^ 52) le_rfl (by norm_num) (by omega)
    rw [key]
    refine ⟨hf, hsg, ?_⟩
    rw [hm, show (2 ^ 52 + (n - 2 ^ 52)) * 2 ^ (1 - 1) = n by
      rw [show 1 - 1 = 0 from rfl, pow_zero, mul_one]; omega]
    simp
  have hn0 : n ≠ 0 := by omega
  have hL53 : 53 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 (by omega)
  have hL2 : Nat.log2 n < 2098 := (Nat.log2_lt hn0).2 (by omega)
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.log2 n - 52 := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by omega
  have hs45 : s ≤ 2045 := by omega
  obtain ⟨R, hR⟩ : ∃ R, R = Wasm.IEEE32.roundShift n s := ⟨_, rfl⟩
  have hRe : 2 * |(R : ℤ) * 2 ^ s - n| ≤ 2 ^ s := by rw [hR]; exact roundShift_half n s hs1
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have hlo : (2 : ℤ) ^ 52 * 2 ^ s ≤ n := by
    have : (2 : ℕ) ^ 52 * 2 ^ s ≤ n := by
      rw [← pow_add, show 52 + s = Nat.log2 n by omega]; exact hL1
    exact_mod_cast this
  have hhi : (n : ℤ) < 2 ^ 53 * 2 ^ s := by
    have : n < (2 : ℕ) ^ 53 * 2 ^ s := by
      rw [← pow_add, show 53 + s = Nat.log2 n + 1 by omega]; exact hL3
    exact_mod_cast this
  have hR52 : 2 ^ 52 ≤ R := by
    by_contra hc
    push Not at hc
    have hc' : (R : ℤ) ≤ 2 ^ 52 - 1 := by
      have h1 : R + 1 ≤ 2 ^ 52 := by omega
      have h2 : ((R + 1 : ℕ) : ℤ) ≤ 2 ^ 52 := by exact_mod_cast h1
      push_cast at h2
      linarith
    have := mul_le_mul_of_nonneg_right hc' hP.le
    have h3 := neg_abs_le ((R : ℤ) * 2 ^ s - n)
    linarith
  have hR53 : R ≤ 2 ^ 53 := by
    by_contra hc
    push Not at hc
    have hc' : (2 : ℤ) ^ 53 + 1 ≤ R := by exact_mod_cast hc
    have := mul_le_mul_of_nonneg_right hc' hP.le
    have h3 := le_abs_self ((R : ℤ) * 2 ^ s - n)
    linarith
  have hn' : (n : ℤ) < 2 ^ 2098 - 2 ^ 2045 := by
    have h2 : ((2 ^ 2098 - 2 ^ 2045 : ℕ) : ℤ) = 2 ^ 2098 - 2 ^ 2045 := by norm_num
    have := (Nat.cast_lt (α := ℤ)).mpr hn
    rw [h2] at this
    exact this
  have herr : 2 ^ 53 * |(R : ℤ) * 2 ^ s - n| ≤ n := by
    have : (2 : ℤ) ^ 53 * |(R : ℤ) * 2 ^ s - n| ≤ 2 ^ 52 * 2 ^ s := by
      have h := mul_le_mul_of_nonneg_left hRe (by positivity : (0 : ℤ) ≤ 2 ^ 52)
      linarith
    linarith
  have h52' : ¬ n < 2 ^ 52 := h52
  have h53' : ¬ n < 2 ^ 53 := h53
  by_cases hR2 : R = 2 ^ 53
  · have hs44 : s ≤ 2044 := by
      by_contra hc
      have hs2045 : s = 2045 := by omega
      rw [hR2, hs2045] at hRe
      have h3 := le_abs_self (((2 ^ 53 : ℕ) : ℤ) * 2 ^ 2045 - n)
      push_cast at hRe h3
      linarith
    have hb : (Wasm.IEEE32.roundShift n (Nat.log2 n - 52) == 2 ^ 53) = true := by
      rw [← hs, ← hR, hR2, beq_self_eq_true]
    have key : Wasm.IEEE64.roundScaledMagnitude neg n = Wasm.IEEE64.encodeFinite neg (s + 2) 0 := by
      unfold Wasm.IEEE64.roundScaledMagnitude
      rw [ite_eq_right h52', ite_eq_right h53']
      set_option simprocs false in dsimp only
      rw [ite_eq_left hb]
      set_option simprocs false in dsimp only
      rw [ite_eq_right (show ¬ (0x7FF ≤ Nat.log2 n - 52 + 1 + 1) by omega), hs]
    obtain ⟨hf, hsg, hm⟩ := enc_spec neg (s + 2) 0 (by omega) (by omega) (by norm_num)
    rw [key]
    refine ⟨hf, hsg, ?_⟩
    rw [hm, show (2 ^ 52 + 0) * 2 ^ (s + 2 - 1) = R * 2 ^ s by
      rw [hR2, show s + 2 - 1 = s + 1 by omega, pow_succ]; ring]
    push_cast
    exact herr
  · have hR53' : R < 2 ^ 53 := lt_of_le_of_ne hR53 hR2
    have hb : ¬ ((Wasm.IEEE32.roundShift n (Nat.log2 n - 52) == 2 ^ 53) = true) := by
      rw [← hs, ← hR]; simpa using hR2
    have key : Wasm.IEEE64.roundScaledMagnitude neg n =
        Wasm.IEEE64.encodeFinite neg (s + 1) (R - 2 ^ 52) := by
      unfold Wasm.IEEE64.roundScaledMagnitude
      rw [ite_eq_right h52', ite_eq_right h53']
      set_option simprocs false in dsimp only
      rw [ite_eq_right hb]
      set_option simprocs false in dsimp only
      rw [ite_eq_right (show ¬ (0x7FF ≤ Nat.log2 n - 52 + 1) by omega), hR, hs]
    obtain ⟨hf, hsg, hm⟩ := enc_spec neg (s + 1) (R - 2 ^ 52) (by omega) (by omega) (by omega)
    rw [key]
    refine ⟨hf, hsg, ?_⟩
    rw [hm, show (2 ^ 52 + (R - 2 ^ 52)) * 2 ^ (s + 1 - 1) = R * 2 ^ s by
      rw [show s + 1 - 1 = s by omega, show 2 ^ 52 + (R - 2 ^ 52) = R by omega]]
    push_cast
    exact herr

/-- A grid point `R 2 ^ s` with `2 ^ 52 ≤ R < 2 ^ 53` packs exactly. -/
theorem rsm_exact (neg : Bool) (R s : ℕ) (hR1 : 2 ^ 52 ≤ R) (hR2 : R < 2 ^ 53) (hs1 : 1 ≤ s)
    (hs : s ≤ 2045) :
    Wasm.IEEE64.roundScaledMagnitude neg (R * 2 ^ s) =
      Wasm.IEEE64.encodeFinite neg (s + 1) (R - 2 ^ 52) := by
  have hP : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs1
  have h52' : ¬ R * 2 ^ s < 2 ^ 52 := by
    have : 2 ^ 52 * 2 ≤ R * 2 ^ s := Nat.mul_le_mul hR1 hP
    omega
  have h53' : ¬ R * 2 ^ s < 2 ^ 53 := by
    have : 2 ^ 52 * 2 ≤ R * 2 ^ s := Nat.mul_le_mul hR1 hP
    omega
  have hn0 : R * 2 ^ s ≠ 0 := by positivity
  have hlog : Nat.log2 (R * 2 ^ s) = 52 + s := by
    apply le_antisymm
    · have : R * 2 ^ s < 2 ^ (52 + s + 1) := by
        rw [show 52 + s + 1 = 53 + s by omega, pow_add]
        exact Nat.mul_lt_mul_of_pos_right hR2 (by positivity)
      have := (Nat.log2_lt hn0).2 this
      omega
    · apply (Nat.le_log2 hn0).2
      rw [pow_add]
      exact Nat.mul_le_mul_right _ hR1
  have hsh : Nat.log2 (R * 2 ^ s) - 52 = s := by omega
  have hrs : Wasm.IEEE32.roundShift (R * 2 ^ s) s = R := by
    unfold Wasm.IEEE32.roundShift
    have hq : R * 2 ^ s / 2 ^ s = R := Nat.mul_div_cancel R (by positivity)
    have hm : R * 2 ^ s % 2 ^ s = 0 := Nat.mul_mod_left R (2 ^ s)
    have hh : 0 < 2 ^ s / 2 := by omega
    simp only [hq, hm, hh, ite_true]
  have hb : ¬ ((Wasm.IEEE32.roundShift (R * 2 ^ s) (Nat.log2 (R * 2 ^ s) - 52) == 2 ^ 53) = true) := by
    rw [hsh, hrs]
    simpa using hR2.ne
  unfold Wasm.IEEE64.roundScaledMagnitude
  rw [ite_eq_right h52', ite_eq_right h53']
  set_option simprocs false in dsimp only
  rw [ite_eq_right hb]
  set_option simprocs false in dsimp only
  rw [ite_eq_right (show ¬ (0x7FF ≤ Nat.log2 (R * 2 ^ s) - 52 + 1) by omega), hsh, hrs]

/-- The value of a word from its sign and magnitude. -/
theorem value_sign (w : UInt64) :
    value w = (if Wasm.IEEE64.sign w then -(Wasm.IEEE64.scaledMagnitude w : ℝ)
      else (Wasm.IEEE64.scaledMagnitude w : ℝ)) / 2 ^ 1074 := by
  rw [value]
  simp only [Wasm.IEEE64.scaledValue]
  split_ifs <;> push_cast <;> ring

/-- **A rounded sum** below `2 ^ 1024 - 2 ^ 971` in magnitude is finite and within a relative
`2 ^ -53`. -/
theorem add_top (a b : UInt64) (ha : Finite a) (hb : Finite b) (h0 : value a + value b ≠ 0)
    (hmax : |value a + value b| < 2 ^ 1024 - 2 ^ 971) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ |value a + value b| / 2 ^ 53 := by
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := ⟨_, rfl⟩
  have hSv : value a + value b = (S : ℝ) / 2 ^ 1074 := by rw [value, value, hS]; push_cast; ring
  have hS0 : S ≠ 0 := by
    intro h
    apply h0
    rw [hSv, h]
    simp
  have hb0 : (S == 0) = false := by simpa using hS0
  have hadd : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) S.natAbs := by
    simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false, ← hS, hb0]
  have hnS : ((S.natAbs : ℕ) : ℝ) = |(S : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hn : S.natAbs < 2 ^ 2098 - 2 ^ 2045 := by
    have h1 : |(S : ℝ)| < 2 ^ 2098 - 2 ^ 2045 := by
      rw [hSv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
        div_lt_iff₀ (by positivity)] at hmax
      linarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 971) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2045)]
    rw [← hnS] at h1
    have h2 : ((2 ^ 2098 - 2 ^ 2045 : ℕ) : ℝ) = 2 ^ 2098 - 2 ^ 2045 := by norm_num
    rw [← h2] at h1
    exact_mod_cast h1
  obtain ⟨hf, hsg, herr⟩ := rsm_near (decide (S < 0)) S.natAbs hn
  rw [hadd]
  refine ⟨hf, ?_⟩
  set c := Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) S.natAbs
  have herrR : 2 ^ 53 * abs ((Wasm.IEEE64.scaledMagnitude c : ℝ) - |(S : ℝ)|) ≤ |(S : ℝ)| := by
    have := (Int.cast_le (R := ℝ)).mpr herr
    push_cast at this
    linarith
  rw [value_sign c, hsg, hSv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  rcases lt_or_gt_of_ne hS0 with hneg | hpos
  · have hSa : |(S : ℝ)| = -(S : ℝ) := abs_of_neg (by exact_mod_cast hneg)
    rw [hSa] at herrR
    simp only [decide_eq_true hneg, ite_true]
    rw [show -(Wasm.IEEE64.scaledMagnitude c : ℝ) / 2 ^ 1074 - (S : ℝ) / 2 ^ 1074 =
      -((Wasm.IEEE64.scaledMagnitude c : ℝ) - -(S : ℝ)) / 2 ^ 1074 by ring, abs_div, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), hSa, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg ((Wasm.IEEE64.scaledMagnitude c : ℝ) - -(S : ℝ))]
  · have hSa : |(S : ℝ)| = (S : ℝ) := abs_of_pos (by exact_mod_cast hpos)
    rw [hSa] at herrR
    simp only [decide_eq_false (not_lt.mpr hpos.le), Bool.false_eq_true, ite_false]
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), hSa, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg ((Wasm.IEEE64.scaledMagnitude c : ℝ) - (S : ℝ))]

theorem round_rational_gen (neg : Bool) (N D : Nat) (hD : 0 < D) (hl : 2 ^ 52 * D ≤ N) :
    ∃ R s : Nat, R ≤ 2 ^ 53 ∧
      Wasm.IEEE64.roundRationalMagnitude neg N D =
        Wasm.IEEE64.roundScaledMagnitude neg (R * 2 ^ s) ∧
      (2 : ℝ) ^ (52 + s) ≤ (N : ℝ) / D ∧ (N : ℝ) / D < 2 ^ (53 + s) ∧
      |(R : ℝ) * 2 ^ s - (N : ℝ) / D| ≤ 2 ^ s / 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  set I := N / D with hI
  have hI52 : 2 ^ 52 ≤ I := (Nat.le_div_iff_mul_le hD).2 hl
  have hI0 : I ≠ 0 := by positivity
  set L := Nat.log2 I with hL
  have hL52 : 52 ≤ L := (Nat.le_log2 hI0).2 hI52
  have hL1 : 2 ^ L ≤ I := Nat.log2_self_le hI0
  have hL3 : I < 2 ^ (L + 1) := Nat.lt_log2_self
  set s := L - 52 with hs
  have hsL : 52 + s = L := by omega
  have hx1 : (I : ℝ) ≤ (N : ℝ) / D := by
    rw [le_div_iff₀ hDR]; exact_mod_cast Nat.div_mul_le_self N D
  have hx2 : (N : ℝ) / D < I + 1 := by
    rw [div_lt_iff₀ hDR]
    have : N < (I + 1) * D := by
      have := Nat.lt_div_mul_add (a := N) hD
      rw [hI]; nlinarith
    exact_mod_cast this
  have hxlo : (2 : ℝ) ^ (52 + s) ≤ (N : ℝ) / D := by
    rw [hsL]
    have : ((2 ^ L : ℕ) : ℝ) ≤ I := by exact_mod_cast hL1
    push_cast at this
    linarith
  have hxhi : (N : ℝ) / D < 2 ^ (53 + s) := by
    rw [show 53 + s = L + 1 by omega]
    have : (I : ℝ) + 1 ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast hL3
    push_cast at this
    linarith
  set R := Wasm.IEEE32.roundQuotient N (D * 2 ^ s) with hR
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hRe : |(R : ℝ) * 2 ^ s - (N : ℝ) / D| ≤ 2 ^ s / 2 := by
    have h := F64NearestDiv.roundQuotient_error N (D * 2 ^ s) (by positivity)
    have h' : (R : ℝ) * 2 ^ s - (N : ℝ) / D = ((R : ℝ) - (N : ℝ) / ((D * 2 ^ s : ℕ) : ℝ)) * 2 ^ s := by
      push_cast; field_simp
    rw [h', abs_mul, abs_of_pos hP]
    calc |(R : ℝ) - (N : ℝ) / ((D * 2 ^ s : ℕ) : ℝ)| * 2 ^ s ≤ 1 / 2 * 2 ^ s :=
          mul_le_mul_of_nonneg_right h hP.le
      _ = 2 ^ s / 2 := by ring
  have hR53 : R ≤ 2 ^ 53 := by
    have h1 : (R : ℝ) * 2 ^ s ≤ 2 ^ 53 * 2 ^ s + 2 ^ s / 2 := by
      have := (abs_le.mp hRe).2
      have h2 : (2 : ℝ) ^ (53 + s) = 2 ^ 53 * 2 ^ s := pow_add _ _ _
      linarith
    have h3 : (R : ℝ) < 2 ^ 53 + 1 := by
      have : (R : ℝ) * 2 ^ s < (2 ^ 53 + 1) * 2 ^ s := by nlinarith
      exact lt_of_mul_lt_mul_right this hP.le
    have : R < 2 ^ 53 + 1 := by exact_mod_cast h3
    omega
  refine ⟨R, s, hR53, ?_, hxlo, hxhi, hRe⟩
  have hN0 : (N == 0) = false := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hl
    simpa using this.ne'
  have hD0 : (D == 0) = false := by simpa using hD.ne'
  unfold Wasm.IEEE64.roundRationalMagnitude
  simp only [hN0, hD0, Bool.false_eq_true, ite_false]
  congr 1
  rw [← hI, ← hL, ← hs]
  by_cases h0 : s = 0
  · have hb : (s == 0) = true := by simp [h0]
    simp only [hR, h0, pow_zero, Nat.mul_one, ite_self]
  · have hb : (s == 0) = false := by simpa using h0
    simp only [hb, Bool.false_eq_true, ite_false, hR]

/-- The division of two nonzero finite words as the rounding of the scaled quotient. -/
theorem div_eq (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    Wasm.IEEE64.div a b = Wasm.IEEE64.roundRationalMagnitude
      (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
      (Wasm.IEEE64.scaledMagnitude a * 2 ^ 1074) (Wasm.IEEE64.scaledMagnitude b) := by
  have hMa0 : (Wasm.IEEE64.scaledMagnitude a == 0) = false := by simpa using ha0
  have hMb0 : (Wasm.IEEE64.scaledMagnitude b == 0) = false := by simpa using hb0
  simp only [Wasm.IEEE64.div, not_nan_of_finite ha, not_nan_of_finite hb,
    not_infinite_of_finite ha, not_infinite_of_finite hb, hMa0, hMb0, Bool.or_false,
    Bool.false_eq_true, ite_false]

/-- `|a / b|` as a ratio of magnitudes. -/
theorem abs_quot (a b : UInt64) :
    |value a / value b| = (Wasm.IEEE64.scaledMagnitude a * 2 ^ 1074 : ℕ) /
      (Wasm.IEEE64.scaledMagnitude b : ℝ) / 2 ^ 1074 := by
  rw [abs_div, F64RoundNearest.abs_value, F64RoundNearest.abs_value]
  push_cast
  rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude b) with h | h
  · rw [h]; simp
  · field_simp; norm_num

/-- **A rounded quotient** of magnitude from 1 to `2 ^ 1024 - 2 ^ 971` is finite and within a
relative `2 ^ -53`. -/
theorem div_top (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hlo : 1 ≤ |value a / value b|) (hhi : |value a / value b| < 2 ^ 1024 - 2 ^ 971) :
    Finite (Wasm.IEEE64.div a b) ∧
      |value (Wasm.IEEE64.div a b) - value a / value b| ≤ |value a / value b| / 2 ^ 53 := by
  set Ma := Wasm.IEEE64.scaledMagnitude a with hMa
  set Mb := Wasm.IEEE64.scaledMagnitude b with hMb
  have hMbpos : 0 < Mb := Nat.pos_of_ne_zero hb0
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMbpos
  set N := Ma * 2 ^ 1074 with hN
  have hq := abs_quot a b
  rw [← hMa, ← hMb, ← hN] at hq
  set Q := (N : ℝ) / Mb with hQ
  have hQlo : (2 : ℝ) ^ 1074 ≤ Q := by
    rw [hq, le_div_iff₀ (by positivity)] at hlo
    linarith
  have hQhi : Q < 2 ^ 2098 - 2 ^ 2045 := by
    rw [hq, div_lt_iff₀ (by positivity)] at hhi
    linarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 971) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2045)]
  have hl : 2 ^ 52 * Mb ≤ N := by
    have : (2 : ℝ) ^ 52 * Mb ≤ N := by
      rw [hQ, le_div_iff₀ hMbR] at hQlo
      nlinarith [(by norm_num : (2 : ℝ) ^ 52 ≤ 2 ^ 1074)]
    exact_mod_cast this
  obtain ⟨R, s, hR53, heq, hxlo, hxhi, hRe⟩ :=
    round_rational_gen (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) N Mb hMbpos hl
  rw [← hQ] at hxlo hxhi hRe
  have hs45 : s ≤ 2045 := by
    by_contra hc
    have : (2 : ℝ) ^ 2098 ≤ 2 ^ (52 + s) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [(by norm_num : (2 : ℝ) ^ 2098 - 2 ^ 2045 ≤ 2 ^ 2098)]
  have hs1 : 1 ≤ s := by
    by_contra hc
    have hs0 : s = 0 := by omega
    rw [hs0] at hxhi
    linarith [(by norm_num : (2 : ℝ) ^ (53 + 0) < 2 ^ 1074)]
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hRe' := abs_le.mp hRe
  have hR52 : 2 ^ 52 ≤ R := by
    by_contra hc
    push Not at hc
    have hc' : (R : ℝ) + 1 ≤ 2 ^ 52 := by
      have : R + 1 ≤ 2 ^ 52 := hc
      exact_mod_cast this
    have h1 : ((R : ℝ) + 1) * 2 ^ s ≤ 2 ^ 52 * 2 ^ s := mul_le_mul_of_nonneg_right hc' hP.le
    rw [pow_add] at hxlo
    linarith
  -- the packed result is the grid point
  have hpack : Finite (Wasm.IEEE64.div a b) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.div a b) = (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.div a b) = R * 2 ^ s := by
    rw [div_eq a b ha hb ha0 hb0, heq]
    rcases lt_or_eq_of_le hR53 with hlt | heq53
    · rw [rsm_exact _ R s hR52 hlt hs1 hs45]
      obtain ⟨hf, hsg, hm⟩ := enc_spec (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) (s + 1)
        (R - 2 ^ 52) (by omega) (by omega) (by omega)
      refine ⟨hf, hsg, ?_⟩
      rw [hm, show s + 1 - 1 = s by omega, show 2 ^ 52 + (R - 2 ^ 52) = R by omega]
    · have hs44 : s ≤ 2044 := by
        by_contra hc
        have hs2045 : s = 2045 := by omega
        rw [heq53, hs2045] at hRe'
        push_cast at hRe'
        linarith [hRe'.2, (by norm_num : (2 : ℝ) ^ 53 * 2 ^ 2045 - 2 ^ 2045 / 2 ≥ 2 ^ 2098 - 2 ^ 2045)]
      rw [heq53, show 2 ^ 53 * 2 ^ s = 2 ^ 52 * 2 ^ (s + 1) by rw [pow_succ]; ring,
        rsm_exact _ (2 ^ 52) (s + 1) le_rfl (by norm_num) (by omega) (by omega)]
      obtain ⟨hf, hsg, hm⟩ := enc_spec (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) (s + 1 + 1)
        (2 ^ 52 - 2 ^ 52) (by omega) (by omega) (by norm_num)
      refine ⟨hf, hsg, ?_⟩
      rw [hm, show s + 1 + 1 - 1 = s + 1 by omega, pow_succ]
      norm_num
  obtain ⟨hf, hsg, hm⟩ := hpack
  refine ⟨hf, ?_⟩
  -- the signed values
  have hva := value_sign a
  have hvb := value_sign b
  have hvc := value_sign (Wasm.IEEE64.div a b)
  rw [hsg, hm] at hvc
  rw [← hMa] at hva
  rw [← hMb] at hvb
  have hMbne : (Mb : ℝ) ≠ 0 := hMbR.ne'
  have hquot : |value a / value b| = Q / 2 ^ 1074 := hq
  have hσ : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      value (Wasm.IEEE64.div a b) = σ * (((R * 2 ^ s : ℕ) : ℝ) / 2 ^ 1074) →
      value a / value b = σ * (Q / 2 ^ 1074) →
      |value (Wasm.IEEE64.div a b) - value a / value b| =
        |((R * 2 ^ s : ℕ) : ℝ) - Q| / 2 ^ 1074 := by
    intro σ hσ1 h1 h2
    rw [h1, h2, ← mul_sub, abs_mul, ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    rcases hσ1 with rfl | rfl <;> simp
  have hdiff : |value (Wasm.IEEE64.div a b) - value a / value b| =
      |((R * 2 ^ s : ℕ) : ℝ) - Q| / 2 ^ 1074 := by
    rw [hQ, hN]
    rw [hQ, hN] at hσ
    cases hsa : Wasm.IEEE64.sign a <;> cases hsb : Wasm.IEEE64.sign b <;>
      rw [hsa, hsb] at hvc <;> rw [hsa] at hva <;> rw [hsb] at hvb
    · apply hσ 1 (Or.inl rfl)
      · rw [hvc]; simp
      · rw [hva, hvb]; simp only [Bool.false_eq_true, ite_false]; push_cast; field_simp; norm_num
    · apply hσ (-1) (Or.inr rfl)
      · rw [hvc]; simp; ring
      · rw [hva, hvb]; simp only [Bool.false_eq_true, ite_false, ite_true]; push_cast
        field_simp; norm_num
    · apply hσ (-1) (Or.inr rfl)
      · rw [hvc]; simp; ring
      · rw [hva, hvb]; simp only [Bool.false_eq_true, ite_false, ite_true]; push_cast
        field_simp; norm_num
    · apply hσ 1 (Or.inl rfl)
      · rw [hvc]; simp
      · rw [hva, hvb]; simp only [ite_true]; push_cast; field_simp; norm_num
  rw [hdiff, hquot, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 2 * |((R * 2 ^ s : ℕ) : ℝ) - Q| ≤ 2 ^ s := by
    push_cast
    linarith [abs_le.mpr ⟨hRe'.1, hRe'.2⟩]
  rw [pow_add] at hxlo
  nlinarith

/-- **A quotient** of magnitude at least `2 ^ 1024` rounds to the infinity of its sign. -/
theorem div_overflow (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (h : 2 ^ 1024 ≤ |value a / value b|) :
    Wasm.IEEE64.div a b = Wasm.IEEE64.infinity (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  set Ma := Wasm.IEEE64.scaledMagnitude a with hMa
  set Mb := Wasm.IEEE64.scaledMagnitude b with hMb
  have hMbpos : 0 < Mb := Nat.pos_of_ne_zero hb0
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMbpos
  set N := Ma * 2 ^ 1074 with hN
  have hq := abs_quot a b
  rw [← hMa, ← hMb, ← hN] at hq
  set Q := (N : ℝ) / Mb with hQ
  have hQlo : (2 : ℝ) ^ 2098 ≤ Q := by
    rw [hq, le_div_iff₀ (by positivity)] at h
    linarith [(by norm_num : (2 : ℝ) ^ 1024 * 2 ^ 1074 = 2 ^ 2098)]
  have hl : 2 ^ 52 * Mb ≤ N := by
    have : (2 : ℝ) ^ 52 * Mb ≤ N := by
      rw [hQ, le_div_iff₀ hMbR] at hQlo
      nlinarith [(by norm_num : (2 : ℝ) ^ 52 ≤ 2 ^ 2098)]
    exact_mod_cast this
  obtain ⟨R, s, -, heq, hxlo, hxhi, hRe⟩ :=
    round_rational_gen (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) N Mb hMbpos hl
  rw [← hQ] at hxlo hxhi hRe
  have hs46 : 2046 ≤ s := by
    by_contra hc
    have : (2 : ℝ) ^ (53 + s) ≤ 2 ^ 2098 := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hRe' := abs_le.mp hRe
  have hR52 : 2 ^ 52 ≤ R := by
    by_contra hc
    push Not at hc
    have hc' : (R : ℝ) + 1 ≤ 2 ^ 52 := by
      have : R + 1 ≤ 2 ^ 52 := hc
      exact_mod_cast this
    have h1 : ((R : ℝ) + 1) * 2 ^ s ≤ 2 ^ 52 * 2 ^ s := mul_le_mul_of_nonneg_right hc' hP.le
    rw [pow_add] at hxlo
    linarith
  rw [div_eq a b ha hb ha0 hb0, heq]
  apply F64Saturate.round_overflow
  calc 2 ^ 2098 - 2 ^ 2044 ≤ 2 ^ 52 * 2 ^ 2046 := by norm_num
    _ ≤ R * 2 ^ s := Nat.mul_le_mul hR52 (Nat.pow_le_pow_right (by norm_num) hs46)

theorem fadd_top (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (h0 : value a.toBits + value b.toBits ≠ 0)
    (hmax : |value a.toBits + value b.toBits| < 2 ^ 1024 - 2 ^ 971) :
    Finite (a + b).toBits ∧
      |value (a + b).toBits - (value a.toBits + value b.toBits)| ≤
        |value a.toBits + value b.toBits| / 2 ^ 53 := by
  rw [F64Bits.toBits_add]
  exact add_top _ _ ha hb h0 hmax

theorem fsub_top (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (h0 : value a.toBits - value b.toBits ≠ 0)
    (hmax : |value a.toBits - value b.toBits| < 2 ^ 1024 - 2 ^ 971) :
    Finite (a - b).toBits ∧
      |value (a - b).toBits - (value a.toBits - value b.toBits)| ≤
        |value a.toBits - value b.toBits| / 2 ^ 53 := by
  rw [F64Bits.toBits_sub]
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value b.toBits hb
  have h := add_top a.toBits (Wasm.IEEE64.negate b.toBits) ha hnf (by rw [hnv]; simpa [sub_eq_add_neg] using h0)
    (by rw [hnv, ← sub_eq_add_neg]; exact hmax)
  rw [hnv, ← sub_eq_add_neg] at h
  exact h

theorem fdiv_top (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (ha0 : Wasm.IEEE64.scaledMagnitude a.toBits ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b.toBits ≠ 0)
    (hlo : 1 ≤ |value a.toBits / value b.toBits|)
    (hhi : |value a.toBits / value b.toBits| < 2 ^ 1024 - 2 ^ 971) :
    Finite (a / b).toBits ∧
      |value (a / b).toBits - value a.toBits / value b.toBits| ≤
        |value a.toBits / value b.toBits| / 2 ^ 53 := by
  rw [F64Bits.toBits_div]
  exact div_top _ _ ha hb ha0 hb0 hlo hhi

#print axioms rsm_near
#print axioms add_top
#print axioms div_top
#print axioms div_overflow

end Library.Numerics.Float64.Tgamma.TgammaTop
