import Verified.Examples.StrconvWords
import LeanExe.ProofKit.F64RoundFinish

/-!
Talos's executable roundings of a positive rational `N / D` and of a dyadic `n / 2 ^ k`, in units
of the least subnormal, equal the references.  `roundQuotient_spec` states that
`roundQuotient N D` is the integer nearest to `N / D`, the even one at a tie, and
`roundsTo_quotient` turns it into `StrconvGrid.RoundsTo` for a binade `E` that holds `N / D`.
`roundRationalMagnitude` chooses the binade from the bit length of `N / D` and rounds once with
`roundQuotient`, so `rational64` and `rational32` follow from `StrconvGrid.positive_reference` and
the encoding of the rounded significand (`scaled64`, `scaled32`).  `roundDyadicMagnitude`, which
Talos's `mul` uses, is the rational rounding with `D = 2 ^ k` (`dyadic64`, `dyadic32`), since
`roundShift n j` is `roundQuotient n (2 ^ j)` for `j ≥ 1` and the bit length of `n / 2 ^ k` is that
of `n` less `k`.
-/

namespace Verified.Examples.StrconvRational
open StrconvGrid StrconvWords LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `roundQuotient N D` is nearest to `N / D`, the even one at a tie. -/
theorem roundQuotient_spec (N D : ℕ) (hD : 0 < D) :
    2 * N ≤ (2 * Wasm.IEEE32.roundQuotient N D + 1) * D ∧
      2 * Wasm.IEEE32.roundQuotient N D * D ≤ 2 * N + D ∧
      (2 * N = (2 * Wasm.IEEE32.roundQuotient N D + 1) * D ∨
        2 * N + D = 2 * Wasm.IEEE32.roundQuotient N D * D →
        Wasm.IEEE32.roundQuotient N D % 2 = 0) := by
  have hq : N / D * D + N % D = N := Nat.div_add_mod' N D
  have hr : N % D < D := Nat.mod_lt N hD
  have hD0 : (D == 0) = false := by simpa using hD.ne'
  unfold Wasm.IEEE32.roundQuotient
  simp only [hD0, Bool.false_eq_true, ite_false]
  generalize N / D = q at hq ⊢
  generalize N % D = r at hq hr ⊢
  subst hq
  by_cases h1 : 2 * r < D
  · rw [if_pos h1]
    refine ⟨by nlinarith, by nlinarith, fun h => ?_⟩
    rcases h with h | h <;> nlinarith
  · rw [if_neg h1]
    by_cases h2 : D < 2 * r
    · rw [if_pos h2]
      refine ⟨by nlinarith, by nlinarith, fun h => ?_⟩
      rcases h with h | h <;> nlinarith
    · rw [if_neg h2]
      have h3 : 2 * r = D := by omega
      by_cases h4 : q % 2 = 0
      · have h4' : (q % 2 == 0) = true := by simpa using h4
        rw [if_pos h4']
        exact ⟨by nlinarith, by nlinarith, fun _ => h4⟩
      · have h4' : (q % 2 == 0) = false := by simpa using h4
        rw [if_neg (by simp [h4'])]
        exact ⟨by nlinarith, by nlinarith, fun _ => by omega⟩

/-- The integer nearest to `N / (D · 2 ^ (E - 1))` rounds `N / D` in a binade `E` that holds it. -/
theorem roundsTo_quotient (f : Fmt) (N D E : ℕ) (hD : 0 < D) (hE : 1 ≤ E)
    (h1 : N < 2 ^ f.p * 2 ^ (E - 1) * D)
    (h2 : E = 1 ∨ 2 ^ (f.p - 1) * 2 ^ (E - 1) * D ≤ N) :
    RoundsTo f ((N : ℝ) / D) E (Wasm.IEEE32.roundQuotient N (D * 2 ^ (E - 1))) := by
  have hD' : 0 < D * 2 ^ (E - 1) := by positivity
  obtain ⟨q1, q2, q3⟩ := roundQuotient_spec N (D * 2 ^ (E - 1)) hD'
  generalize Wasm.IEEE32.roundQuotient N (D * 2 ^ (E - 1)) = Q at q1 q2 q3 ⊢
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hNy : (N : ℝ) = ((N : ℝ) / D) * D := by field_simp
  set y := (N : ℝ) / D with hydef
  set S := (2 : ℝ) ^ (E - 1) with hS
  have c1 : 2 * (N : ℝ) ≤ (2 * Q + 1) * (D * S) := by
    have : ((2 * N : ℕ) : ℝ) ≤ (((2 * Q + 1) * (D * 2 ^ (E - 1)) : ℕ) : ℝ) := by exact_mod_cast q1
    push_cast at this; exact this
  have c2 : 2 * Q * (D * S) ≤ 2 * (N : ℝ) + D * S := by
    have : (((2 * Q * (D * 2 ^ (E - 1))) : ℕ) : ℝ) ≤ ((2 * N + D * 2 ^ (E - 1) : ℕ) : ℝ) := by
      exact_mod_cast q2
    push_cast at this; exact this
  refine ⟨hE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hydef, div_lt_iff₀ hDr]; exact_mod_cast h1
  · rcases h2 with h | h
    · exact Or.inl h
    · right; rw [hydef, le_div_iff₀ hDr]; exact_mod_cast h
  · have : (2 * y) * D ≤ ((2 * Q + 1) * S) * D := by
      calc (2 * y) * D = 2 * (N : ℝ) := by rw [hNy]; ring
        _ ≤ (2 * Q + 1) * (D * S) := c1
        _ = ((2 * Q + 1) * S) * D := by ring
    exact le_of_mul_le_mul_right this hDr
  · have : (2 * Q * S) * D ≤ (2 * y + S) * D := by
      calc (2 * Q * S) * D = 2 * Q * (D * S) := by ring
        _ ≤ 2 * (N : ℝ) + D * S := c2
        _ = (2 * y + S) * D := by rw [hNy]; ring
    exact le_of_mul_le_mul_right this hDr
  · intro ht
    apply q3
    rcases ht with ht | ht
    · left
      have : ((2 * N : ℕ) : ℝ) = (((2 * Q + 1) * (D * 2 ^ (E - 1)) : ℕ) : ℝ) := by
        push_cast
        calc 2 * (N : ℝ) = (2 * y) * D := by rw [hNy]; ring
          _ = ((2 * Q + 1) * S) * D := by rw [ht]
          _ = (2 * Q + 1) * (D * S) := by ring
      exact_mod_cast this
    · right
      have : ((2 * N + D * 2 ^ (E - 1) : ℕ) : ℝ) = ((2 * Q * (D * 2 ^ (E - 1)) : ℕ) : ℝ) := by
        push_cast
        calc 2 * (N : ℝ) + D * S = (2 * y + S) * D := by rw [hNy]; ring
          _ = (2 * Q * S) * D := by rw [ht]
          _ = 2 * Q * (D * S) := by ring
      exact_mod_cast this

/-- The bit length of `n / 2 ^ k` is that of `n` less `k`. -/
theorem log2_div_pow (n k : ℕ) : Nat.log2 (n / 2 ^ k) = Nat.log2 n - k := by
  by_cases hn : n < 2 ^ k
  · rw [Nat.div_eq_of_lt hn]
    by_cases h0 : n = 0
    · subst h0; simp
    · have := (Nat.log2_lt h0).mpr hn
      simp only [Nat.log2_zero]; omega
  · push Not at hn
    have h0 : n ≠ 0 := by have := Nat.two_pow_pos k; omega
    have hL := Nat.log2_self_le h0
    have hL2 := Nat.lt_log2_self (n := n)
    have hk : k ≤ Nat.log2 n := (Nat.le_log2 h0).mpr hn
    have hq0 : n / 2 ^ k ≠ 0 := by
      rw [Ne, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)]; omega
    rw [Nat.log2_eq_iff hq0]
    constructor
    · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k), ← pow_add,
        show Nat.log2 n - k + k = Nat.log2 n by omega]
      exact hL
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← pow_add,
        show Nat.log2 n - k + 1 + k = Nat.log2 n + 1 by omega]
      exact hL2

theorem roundShift_eq (n j : ℕ) (hj : 0 < j) :
    Wasm.IEEE32.roundShift n j = Wasm.IEEE32.roundQuotient n (2 ^ j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hp : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
  have hhalf : 2 ^ (i + 1) / 2 = 2 ^ i := by rw [pow_succ]; simp
  have hD0 : (2 ^ (i + 1) == 0) = false := by simpa using hp.ne'
  unfold Wasm.IEEE32.roundShift Wasm.IEEE32.roundQuotient
  simp only [hD0, Bool.false_eq_true, ite_false]
  try dsimp only
  try simp only [hhalf]
  have hr := Nat.mod_lt n hp
  have e : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
  by_cases h1 : n % 2 ^ (i + 1) < 2 ^ i
  · rw [if_pos h1, if_pos (show 2 * (n % 2 ^ (i + 1)) < 2 ^ (i + 1) by omega)]
  · rw [if_neg h1, if_neg (show ¬ 2 * (n % 2 ^ (i + 1)) < 2 ^ (i + 1) by omega)]
    by_cases h2 : 2 ^ i < n % 2 ^ (i + 1)
    · rw [if_pos h2, if_pos (show 2 ^ (i + 1) < 2 * (n % 2 ^ (i + 1)) by omega)]
    · rw [if_neg h2, if_neg (show ¬ 2 ^ (i + 1) < 2 * (n % 2 ^ (i + 1)) by omega)]

/-! ### Binary64 -/

theorem encode64 (e f : ℕ) : Wasm.IEEE64.encodeFinite false e f = UInt64.ofNat (e * 2 ^ 52 + f) := by
  simp [Wasm.IEEE64.encodeFinite]

theorem infinity64 : Wasm.IEEE64.infinity false = UInt64.ofNat (limit b64) := by
  rw [limit_b64]; decide

/-- The word of an exact significand `R ≤ 2 ^ 53` in binade `s + 1`. -/
theorem scaled64 (R s : ℕ) (hR : R ≤ 2 ^ 53) (hR1 : s = 0 ∨ 2 ^ 52 ≤ R) :
    Wasm.IEEE64.roundScaledMagnitude false (R * 2 ^ s) = UInt64.ofNat (packInf b64 (s + 1) R) := by
  have hL : limit b64 = 2047 * 4503599627370496 := by rw [limit_b64]
  have hF : b64.F = 2047 := rfl
  have e52 : (2 : ℕ) ^ 52 = 4503599627370496 := by norm_num
  have e53 : (2 : ℕ) ^ 53 = 2 * 4503599627370496 := by norm_num
  have hinf : Wasm.IEEE64.infinity false = UInt64.ofNat (2047 * 4503599627370496) := by
    rw [← hL, infinity64]
  unfold packInf pack
  rw [Nat.add_sub_cancel, half_b64, hL, hF, e52]
  rw [e52] at hR1
  rw [e53] at hR
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp only [pow_zero, mul_one, zero_mul, zero_add]
    rw [if_neg (show ¬ (2047 ≤ 0 + 1 ∨ 2047 * 4503599627370496 ≤ R) by omega)]
    unfold Wasm.IEEE64.roundScaledMagnitude
    rw [e52, e53]
    by_cases h1 : R < 4503599627370496
    · rw [if_pos h1, encode64]; simp
    by_cases h2 : R < 2 * 4503599627370496
    · rw [if_neg h1, if_pos h2, encode64, e52, show 1 * 4503599627370496 + (R - 4503599627370496) = R by omega]
    · have hR' : R = 2 * 4503599627370496 := by omega
      subst hR'
      rw [if_neg h1, if_neg h2]
      have hlog : Nat.log2 (2 * 4503599627370496) - 52 = 1 := by
        rw [← e53, Nat.log2_two_pow]
      have hround : Wasm.IEEE32.roundShift (2 * 4503599627370496) 1 = 4503599627370496 := by
        rw [show (2 : ℕ) * 4503599627370496 = 4503599627370496 * 2 ^ 1 by norm_num]
        exact F64RoundFinish.roundShift_mul_pow _ _ (by omega)
      simp only [hlog, hround]
      norm_num [encode64]
  · have hR2 : 2 ^ 52 ≤ R := by rw [e52]; omega
    rw [F64RoundFinish.roundScaled_mul_pow false R s hs hR2 (by rw [e53]; exact hR), e53, e52]
    by_cases hR' : R = 2 * 4503599627370496
    · subst hR'
      rw [if_pos rfl]
      by_cases hi : 2047 ≤ s + 2
      · rw [if_pos hi, if_pos (show 2047 ≤ s + 1 ∨
          2047 * 4503599627370496 ≤ s * 4503599627370496 + 2 * 4503599627370496 by right; omega),
          hinf]
      · rw [if_neg hi, if_neg (show ¬ (2047 ≤ s + 1 ∨
          2047 * 4503599627370496 ≤ s * 4503599627370496 + 2 * 4503599627370496) by omega),
          encode64, e52, show (s + 2) * 4503599627370496 + 0 = s * 4503599627370496 + 2 * 4503599627370496 by ring]
    · rw [if_neg hR']
      by_cases hi : 2047 ≤ s + 1
      · rw [if_pos hi, if_pos (show 2047 ≤ s + 1 ∨
          2047 * 4503599627370496 ≤ s * 4503599627370496 + R by left; exact hi), hinf]
      · rw [if_neg hi, if_neg (show ¬ (2047 ≤ s + 1 ∨
          2047 * 4503599627370496 ≤ s * 4503599627370496 + R) by omega), encode64]
        have hX : 4503599627370496 ≤ R := by rw [← e52]; exact hR2
        rw [e52, show (s + 1) * 4503599627370496 + (R - 4503599627370496) = s * 4503599627370496 + R by rw [Nat.add_mul, one_mul]; omega]

/-- Talos's rounding of a positive rational `N / D` in units of `2 ^ -1074` is the reference. -/
theorem rational64 (N D : ℕ) (hN : 0 < N) (hD : 0 < D) :
    Wasm.IEEE64.roundRationalMagnitude false N D = UInt64.ofNat (refPos b64 ((N : ℝ) / D)) := by
  set I := N / D with hI
  set s := Nat.log2 I - 52 with hs
  have hNI : N < (I + 1) * D := by
    rw [hI, Nat.add_mul, one_mul]; have := Nat.div_add_mod' N D; have := Nat.mod_lt N hD; omega
  have hI1 : I + 1 ≤ 2 ^ 53 * 2 ^ s := by
    have := Nat.lt_log2_self (n := I)
    have : 2 ^ (Nat.log2 I + 1) ≤ 2 ^ 53 * 2 ^ s := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hRT := roundsTo_quotient b64 N D (s + 1) hD (by omega)
    (by simp only [b64, Nat.add_sub_cancel]; nlinarith)
    (by
      rcases Nat.eq_zero_or_pos s with h | h
      · left; omega
      · right
        simp only [b64, Nat.add_sub_cancel, show 53 - 1 = 52 from rfl]
        have hI0 : I ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; omega
        have h1 := Nat.log2_self_le hI0
        have h2 : 2 ^ 52 * 2 ^ s = 2 ^ Nat.log2 I := by rw [← pow_add]; congr 1; omega
        rw [h2]
        calc 2 ^ Nat.log2 I * D ≤ I * D := Nat.mul_le_mul_right _ h1
          _ ≤ N := Nat.div_mul_le_self N D)
  rw [Nat.add_sub_cancel] at hRT
  have hbounds := significand_bounds b64 _ _ _ hRT
  rw [positive_reference b64 _ _ _ hRT, ← scaled64 _ s (by rw [half_b64] at hbounds; omega)
    (by rcases hbounds.2 with h | h
        · left; omega
        · right; rw [half_b64] at h; exact h)]
  have hN0 : (N == 0) = false := by simpa using hN.ne'
  have hD0 : (D == 0) = false := by simpa using hD.ne'
  unfold Wasm.IEEE64.roundRationalMagnitude
  simp only [hN0, hD0, Bool.false_eq_true, ite_false]
  rw [← hI, ← hs]
  by_cases h0 : s = 0
  · simp [h0]
  · simp [h0]

/-- Talos's rounding of a positive dyadic `n / 2 ^ k` in units of `2 ^ -1074` is the
reference. -/
theorem dyadic64 (n k : ℕ) (hn : 0 < n) :
    Wasm.IEEE64.roundDyadicMagnitude false n k = UInt64.ofNat (refPos b64 ((n : ℝ) / 2 ^ k)) := by
  have h := rational64 n (2 ^ k) hn (Nat.two_pow_pos k)
  push_cast at h
  rw [← h]
  have hn0 : (n == 0) = false := by simpa using hn.ne'
  have hd0 : (2 ^ k == 0) = false := by simpa using (Nat.two_pow_pos k).ne'
  unfold Wasm.IEEE64.roundDyadicMagnitude Wasm.IEEE64.roundRationalMagnitude
  simp only [hn0, hd0, Bool.false_eq_true, ite_false]
  rw [log2_div_pow, show Nat.log2 n - k - 52 = Nat.log2 n - (k + 52) by omega]
  by_cases hs : Nat.log2 n - (k + 52) = 0
  · simp only [hs, beq_self_eq_true, ite_true]
    by_cases hk : k = 0
    · subst hk
      have h1 : Wasm.IEEE32.roundQuotient n 1 = n := by
        unfold Wasm.IEEE32.roundQuotient
        simp [Nat.mod_one, Nat.div_one]
      simp only [beq_self_eq_true, ite_true, pow_zero, h1]
    · have hk' : (k == 0) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ite_false]
      rw [roundShift_eq n k (Nat.pos_of_ne_zero hk)]
  · have hs' : (Nat.log2 n - (k + 52) == 0) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ite_false]
    rw [roundShift_eq n _ (by omega), pow_add]

#print axioms roundQuotient_spec
#print axioms roundsTo_quotient
#print axioms scaled64
#print axioms rational64
#print axioms dyadic64

/-! ### Binary32 -/

theorem encode32 (e f : ℕ) : Wasm.IEEE32.encodeFinite false e f = UInt32.ofNat (e * 2 ^ 23 + f) := by
  simp [Wasm.IEEE32.encodeFinite]

theorem infinity32 : Wasm.IEEE32.infinity false = UInt32.ofNat (limit b32) := by
  rw [limit_b32]; decide

/-- The word of an exact significand `R ≤ 2 ^ 24` in binade 1. -/
theorem scaled32 (R : ℕ) (hR : R ≤ 2 ^ 24) :
    Wasm.IEEE32.roundScaledMagnitude false R = UInt32.ofNat (packInf b32 1 R) := by
  have hL : limit b32 = 255 * 8388608 := by rw [limit_b32]
  have hF : b32.F = 255 := rfl
  have e23 : (2 : ℕ) ^ 23 = 8388608 := by norm_num
  have e24 : (2 : ℕ) ^ 24 = 2 * 8388608 := by norm_num
  unfold packInf pack
  rw [Nat.sub_self, zero_mul, zero_add, hL, hF]
  rw [e24] at hR
  rw [if_neg (show ¬ (255 ≤ 1 ∨ 255 * 8388608 ≤ R) by omega)]
  unfold Wasm.IEEE32.roundScaledMagnitude
  rw [e23, e24]
  by_cases h1 : R < 8388608
  · rw [if_pos h1, encode32]; simp
  by_cases h2 : R < 2 * 8388608
  · rw [if_neg h1, if_pos h2, encode32, e23, show 1 * 8388608 + (R - 8388608) = R by omega]
  · have hR' : R = 2 * 8388608 := by omega
    subst hR'
    rw [if_neg h1, if_neg h2]
    have hlog : Nat.log2 (2 * 8388608) - 23 = 1 := by
      rw [← e24, Nat.log2_two_pow]
    have hround : Wasm.IEEE32.roundShift (2 * 8388608) 1 = 8388608 := by
      rw [show (2 : ℕ) * 8388608 = 8388608 * 2 ^ 1 by norm_num]
      exact F64RoundFinish.roundShift_mul_pow _ _ (by omega)
    simp only [hlog, hround]
    norm_num [encode32]

/-- Talos's binary32 rounding of a positive rational `N / D` in units of `2 ^ -149` is the
reference. -/
theorem rational32 (N D : ℕ) (hN : 0 < N) (hD : 0 < D) :
    Wasm.IEEE32.roundRationalMagnitude false N D = UInt32.ofNat (refPos b32 ((N : ℝ) / D)) := by
  set I := N / D with hI
  set s := Nat.log2 I - 23 with hs
  have hNI : N < (I + 1) * D := by
    rw [hI, Nat.add_mul, one_mul]; have := Nat.div_add_mod' N D; have := Nat.mod_lt N hD; omega
  have hI1 : I + 1 ≤ 2 ^ 24 * 2 ^ s := by
    have := Nat.lt_log2_self (n := I)
    have : 2 ^ (Nat.log2 I + 1) ≤ 2 ^ 24 * 2 ^ s := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hRT := roundsTo_quotient b32 N D (s + 1) hD (by omega)
    (by simp only [b32, Nat.add_sub_cancel]; nlinarith)
    (by
      rcases Nat.eq_zero_or_pos s with h | h
      · left; omega
      · right
        simp only [b32, Nat.add_sub_cancel, show 24 - 1 = 23 from rfl]
        have hI0 : I ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; omega
        have h1 := Nat.log2_self_le hI0
        have h2 : 2 ^ 23 * 2 ^ s = 2 ^ Nat.log2 I := by rw [← pow_add]; congr 1; omega
        rw [h2]
        calc 2 ^ Nat.log2 I * D ≤ I * D := Nat.mul_le_mul_right _ h1
          _ ≤ N := Nat.div_mul_le_self N D)
  rw [Nat.add_sub_cancel] at hRT
  have hbounds := significand_bounds b32 _ _ _ hRT
  rw [half_b32] at hbounds
  rw [positive_reference b32 _ _ _ hRT]
  have hN0 : (N == 0) = false := by simpa using hN.ne'
  have hD0 : (D == 0) = false := by simpa using hD.ne'
  unfold Wasm.IEEE32.roundRationalMagnitude
  simp only [hN0, hD0, Bool.false_eq_true, ite_false]
  rw [← hI, ← hs]
  by_cases h0 : s = 0
  · have h0' : (s == 0) = true := by simpa using h0
    simp only [h0', ite_true]
    rw [show Wasm.IEEE32.roundQuotient N (D * 2 ^ s) = Wasm.IEEE32.roundQuotient N D by
      rw [h0, pow_zero, mul_one]] at hbounds ⊢
    rw [scaled32 _ (by omega), h0]
  · have h0' : (s == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ite_false]
    have hQ1 : 2 ^ 23 ≤ Wasm.IEEE32.roundQuotient N (D * 2 ^ s) := by
      rcases hbounds.2 with h | h
      · omega
      · exact h
    generalize Wasm.IEEE32.roundQuotient N (D * 2 ^ s) = R at hbounds hQ1 ⊢
    have hL : limit b32 = 255 * 8388608 := by rw [limit_b32]
    have hF : b32.F = 255 := rfl
    have e23 : (2 : ℕ) ^ 23 = 8388608 := by norm_num
    have e24 : (2 : ℕ) ^ 24 = 2 * 8388608 := by norm_num
    have hinf : Wasm.IEEE32.infinity false = UInt32.ofNat (255 * 8388608) := by rw [← hL, infinity32]
    unfold packInf pack
    rw [Nat.add_sub_cancel, half_b32, hL, hF, e23, e24]
    rw [e23] at hQ1
    have hR : R ≤ 2 * 8388608 := by have := hbounds.1; omega
    by_cases hR' : R = 2 * 8388608
    · subst hR'
      simp only [beq_self_eq_true, ite_true]
      by_cases hi : 255 ≤ s + 1 + 1
      · rw [if_pos hi, if_pos (show 255 ≤ s + 1 ∨
          255 * 8388608 ≤ s * 8388608 + 2 * 8388608 by right; omega), hinf]
      · rw [if_neg hi, if_neg (show ¬ (255 ≤ s + 1 ∨
          255 * 8388608 ≤ s * 8388608 + 2 * 8388608) by omega), encode32, e23,
          show (s + 1 + 1) * 8388608 + (8388608 - 8388608) = s * 8388608 + 2 * 8388608 by ring_nf]
    · have hR'' : (R == 2 * 8388608) = false := by simpa using hR'
      simp only [hR'', Bool.false_eq_true, ite_false]
      by_cases hi : 255 ≤ s + 1
      · rw [if_pos hi, if_pos (show 255 ≤ s + 1 ∨ 255 * 8388608 ≤ s * 8388608 + R by left; exact hi),
          hinf]
      · rw [if_neg hi, if_neg (show ¬ (255 ≤ s + 1 ∨ 255 * 8388608 ≤ s * 8388608 + R) by omega),
          encode32, e23,
          show (s + 1) * 8388608 + (R - 8388608) = s * 8388608 + R by rw [Nat.add_mul, one_mul]; omega]

/-- Talos's binary32 rounding of a positive dyadic `n / 2 ^ k` in units of `2 ^ -149` is the
reference. -/
theorem dyadic32 (n k : ℕ) (hn : 0 < n) :
    Wasm.IEEE32.roundDyadicMagnitude false n k = UInt32.ofNat (refPos b32 ((n : ℝ) / 2 ^ k)) := by
  have h := rational32 n (2 ^ k) hn (Nat.two_pow_pos k)
  push_cast at h
  rw [← h]
  have hn0 : (n == 0) = false := by simpa using hn.ne'
  have hd0 : (2 ^ k == 0) = false := by simpa using (Nat.two_pow_pos k).ne'
  unfold Wasm.IEEE32.roundDyadicMagnitude Wasm.IEEE32.roundRationalMagnitude
  simp only [hn0, hd0, Bool.false_eq_true, ite_false]
  rw [log2_div_pow, show Nat.log2 n - k - 23 = Nat.log2 n - (k + 23) by omega]
  by_cases hs : Nat.log2 n - (k + 23) = 0
  · simp only [hs, beq_self_eq_true, ite_true]
    by_cases hk : k = 0
    · subst hk
      have h1 : Wasm.IEEE32.roundQuotient n 1 = n := by
        unfold Wasm.IEEE32.roundQuotient
        simp [Nat.mod_one, Nat.div_one]
      simp only [beq_self_eq_true, ite_true, pow_zero, h1]
    · have hk' : (k == 0) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ite_false]
      rw [roundShift_eq n k (Nat.pos_of_ne_zero hk)]
  · have hs' : (Nat.log2 n - (k + 23) == 0) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ite_false]
    rw [roundShift_eq n _ (by omega), pow_add]

#print axioms scaled32
#print axioms rational32
#print axioms dyadic32

end Verified.Examples.StrconvRational
