import Library.Numerics.Decimal.PrintFloat.PrintFloatShortest
import Library.Numerics.Decimal.PrintFloat.PrintFloatLayout
import Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem
import Library.Numerics.Decimal.Shared.StrconvInterval

/-!
The binary64 words of the printers.  For a finite nonzero word `w` of magnitude bits
`n = w mod 2 ^ 63`, `sig64 n`, `bin64 n`, and `low64 n` are the significand `Q`, the binade `E`,
and the flag of the start of a normal binade that `PrintFloat.print64With` computes from the bits
(`print64_code`).  `n = pack b64 E Q` (`pack_sig`), so `Library.Numerics.Decimal.Shared.StrconvInterval.interval_iff` makes
`round64` of a decimal equal to `w` exactly when its sign is that of `w` and its magnitude lies in
the interval `[lo, hi]` of `PrintFloatSearch`, the ends included when `Q` is even (`round64_iff`).
`shortest64` joins this with `PrintFloatShort.shortest_of_choice`: the decimal of the code's
choice is `Shortest64` and has no trailing zero.
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatWord
open PrintFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.ParseFloat.ParseFloatRound Library.Numerics.Decimal.Shared.StrconvRound Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvGrid
  StrconvWords StrconvInterval PrintFloatShort PrintFloatQuot PrintFloatSearch PrintFloatPick
  PrintFloatShortest PrintFloatLayout ParseFloatTheorem

set_option exponentiation.threshold 4096

/-- The significand of the magnitude bits `n`. -/
def sig64 (n : ℕ) : ℕ := if n / 2 ^ 52 = 0 then n % 2 ^ 52 else n % 2 ^ 52 + 2 ^ 52

/-- The binade of the magnitude bits `n`. -/
def bin64 (n : ℕ) : ℕ := if n / 2 ^ 52 = 0 then 1 else n / 2 ^ 52

/-- The magnitude bits `n` start a normal binade above the first. -/
def low64 (n : ℕ) : Bool := decide (2 ≤ n / 2 ^ 52 ∧ n % 2 ^ 52 = 0)

theorem pack_sig (n : ℕ) : pack b64 (bin64 n) (sig64 n) = n := by
  unfold pack bin64 sig64
  rw [half_b64]
  split_ifs <;> omega

theorem canonical_sig (n : ℕ) (hn : n < 0x7FF0000000000000) (h0 : 0 < n) :
    Canonical b64 (bin64 n) (sig64 n) := by
  unfold Canonical bin64 sig64
  rw [half_b64]
  split_ifs <;> omega

theorem bounds_sig (n : ℕ) (hn : n < 0x7FF0000000000000) (h0 : 0 < n) :
    WordBounds (sig64 n) (bin64 n) 1074 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num⟩ <;> simp only [sig64, bin64] <;>
    split_ifs <;> omega

theorem sig_pos (n : ℕ) (h0 : 0 < n) : 1 ≤ sig64 n := by
  unfold sig64; split_ifs <;> omega

theorem bin_pos (n : ℕ) : 1 ≤ bin64 n := by
  unfold bin64; split_ifs <;> omega

theorem canon_sig (n : ℕ) : bin64 n = 1 ∨ 16 ≤ sig64 n := by
  unfold bin64 sig64; split_ifs <;> omega

/-- `mag` of the magnitude bits. -/
theorem mag_sig (n : ℕ) : mag b64 n = sig64 n * 2 ^ (bin64 n - 1) := by
  unfold mag sig64 bin64
  rw [half_b64]
  split_ifs with h1 h2 h2
  · simp only [Nat.sub_self, pow_zero, mul_one]; omega
  · omega
  · omega
  · ring

/-- The interval of `StrconvInterval` scaled by `2 ^ 1074` is that of `PrintFloatSearch`. -/
theorem inside_iff (n : ℕ) (hn : n < 0x7FF0000000000000) (h0 : 0 < n) (y : ℝ) :
    InInterval b64 (bin64 n) (sig64 n) (y * 2 ^ 1074) ↔
      Inside (cl (sig64 n)) (lo (sig64 n) (bin64 n) 1074 (low64 n)) (hi (sig64 n) (bin64 n) 1074)
        y := by
  have hQ := sig_pos n h0
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hS : (2 : ℝ) ^ (1074 + 2) = 2 ^ 1074 * 4 := by norm_num
  have hlo : lo (sig64 n) (bin64 n) 1074 (low64 n) * 2 ^ 1074 =
      Library.Numerics.Decimal.Shared.StrconvInterval.lower b64 (bin64 n) (sig64 n) := by
    unfold lo rv nl Library.Numerics.Decimal.Shared.StrconvInterval.lower low64
    rw [half_b64, hS]
    have e : (2 ≤ bin64 n ∧ sig64 n = 2 ^ 52) ↔ (2 ≤ n / 2 ^ 52 ∧ n % 2 ^ 52 = 0) := by
      unfold bin64 sig64; split_ifs <;> omega
    by_cases hl : 2 ≤ n / 2 ^ 52 ∧ n % 2 ^ 52 = 0
    · rw [decide_eq_true hl, ite_eq_left rfl, ite_eq_left (e.mpr hl)]
      have : ((4 * sig64 n - 1 : ℕ) : ℝ) = 4 * (sig64 n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      field_simp
    · rw [decide_eq_false hl, ite_eq_right Bool.false_ne_true,
        ite_eq_right (fun h => hl (e.mp h))]
      have : ((4 * sig64 n - 2 : ℕ) : ℝ) = 2 * (2 * (sig64 n : ℝ) - 1) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      field_simp
      ring
  have hhi : hi (sig64 n) (bin64 n) 1074 * 2 ^ 1074 = upper (bin64 n) (sig64 n) := by
    unfold hi rv upper
    rw [hS]
    push_cast
    field_simp
    ring
  unfold InInterval Inside cl
  rw [← hlo, ← hhi]
  by_cases he : sig64 n % 2 = 0
  · rw [ite_eq_left he, ite_eq_left (decide_eq_true he)]
    rw [mul_le_mul_iff_of_pos_right hp, mul_le_mul_iff_of_pos_right hp]
  · rw [ite_eq_right he, ite_eq_right (by rw [decide_eq_false he]; exact Bool.false_ne_true)]
    rw [mul_lt_mul_iff_of_pos_right hp, mul_lt_mul_iff_of_pos_right hp]

/-- The magnitude bits of a finite word lie below the encoding of infinity. -/
theorem finite_bits (w : UInt64) (hf : Wasm.IEEE64.isFinite w = true) :
    w.toNat % 2 ^ 63 < 0x7FF0000000000000 := by
  unfold Wasm.IEEE64.isFinite Wasm.IEEE64.exponent at hf
  simp only [bne_iff_ne, ne_eq] at hf
  have := w.toNat_lt
  simp only [Nat.reducePow] at hf this ⊢
  omega

/-- **The rounding of a decimal to a finite nonzero binary64 word.** -/
theorem round64_iff (w : UInt64) (hf : Wasm.IEEE64.isFinite w = true)
    (hz : w.toNat % 2 ^ 63 ≠ 0) (neg : Bool) (d : ℕ) (e : ℤ) :
    round64 (.dec neg d e) = w ↔
      neg = Wasm.IEEE64.sign w ∧
        Inside (cl (sig64 (w.toNat % 2 ^ 63)))
          (lo (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074 (low64 (w.toNat % 2 ^ 63)))
          (hi (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074) (dv d e) := by
  obtain ⟨n, hn⟩ : ∃ n, n = w.toNat % 2 ^ 63 := ⟨_, rfl⟩
  rw [← hn]
  have hfin := finite_bits w hf
  rw [← hn] at hfin hz
  have h0 : 0 < n := Nat.pos_of_ne_zero hz
  have hwlt := w.toNat_lt
  have hy0 : (0 : ℝ) ≤ (d : ℝ) * 10 ^ e * 2 ^ 1074 := by positivity
  have key : refPos b64 ((d : ℝ) * 10 ^ e * 2 ^ 1074) = n ↔
      Inside (cl (sig64 n)) (lo (sig64 n) (bin64 n) 1074 (low64 n)) (hi (sig64 n) (bin64 n) 1074)
        (dv d e) := by
    have hL : pack b64 (bin64 n) (sig64 n) < limit b64 := by rw [pack_sig, limit_b64]; exact hfin
    have h := interval_iff b64 (bin64 n) (sig64 n) (canonical_sig n hfin h0) hL _ hy0
    rw [pack_sig] at h
    rw [h, inside_iff n hfin h0]
    rfl
  rw [round64_dec, ← key]
  have hr := limit64 ((d : ℝ) * 10 ^ e * 2 ^ 1074)
  generalize refPos b64 ((d : ℝ) * 10 ^ e * 2 ^ 1074) = r at hr ⊢
  have hrr : (UInt64.ofNat r).toNat = r := ofNat_toNat _ (by omega)
  unfold withSign64 Wasm.IEEE64.sign
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [hrr] at this
      refine ⟨by rw [eq_comm, decide_eq_false_iff_not]; omega, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [eq_comm, decide_eq_false_iff_not] at h1
      apply UInt64.toNat_inj.mp
      rw [hrr]
      omega
  · simp only [ite_true]
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      rw [negate64 _ (by rw [hrr]; omega), hrr] at this
      refine ⟨by rw [eq_comm, decide_eq_true_iff]; omega, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [eq_comm, decide_eq_true_iff] at h1
      apply UInt64.toNat_inj.mp
      rw [negate64 _ (by rw [hrr]; omega), hrr]
      omega

/-- The magnitude of a word in units of the least subnormal through its magnitude bits. -/
theorem scaledMagnitude_eq (w : UInt64) :
    Wasm.IEEE64.scaledMagnitude w = mag b64 (w.toNat % 2 ^ 63) := by
  have hw := w.toNat_lt
  have he : Wasm.IEEE64.exponent w = w.toNat % 2 ^ 63 / 2 ^ 52 := by
    unfold Wasm.IEEE64.exponent; omega
  have hfr : Wasm.IEEE64.fraction w = w.toNat % 2 ^ 63 % 2 ^ 52 := by
    unfold Wasm.IEEE64.fraction; omega
  unfold Wasm.IEEE64.scaledMagnitude mag
  rw [he, hfr, half_b64]
  simp only [beq_iff_eq]
  split_ifs <;> omega

theorem bits_ne_zero (w : UInt64) (hz : Wasm.IEEE64.scaledMagnitude w ≠ 0) :
    w.toNat % 2 ^ 63 ≠ 0 := by
  intro h
  apply hz
  rw [scaledMagnitude_eq, h, mag, ite_eq_left (by rw [half_b64]; norm_num)]

/-- The value of a finite binary64 word through its significand and binade. -/
theorem value_eq (w : UInt64) :
    CodeLib.IEEE64.value w = (if Wasm.IEEE64.sign w then -1 else 1) *
      vv (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074 := by
  have hm := scaledMagnitude_eq w
  have hv : vv (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074 =
      (mag b64 (w.toNat % 2 ^ 63) : ℝ) / 2 ^ 1074 := by
    unfold vv rv
    rw [mag_sig]
    push_cast
    rw [show (2 : ℝ) ^ (1074 + 2) = 2 ^ 1074 * 4 by norm_num]
    field_simp
  rw [hv, CodeLib.IEEE64.value, Wasm.IEEE64.scaledValue, hm]
  split_ifs <;> push_cast <;> ring

theorem toReal_dec (neg : Bool) (d : ℕ) (e : ℤ) :
    Num.toReal (.dec neg d e) = (if neg then -1 else 1) * dv d e := by
  rw [dv, ← mul_assoc]; rfl

/-- `Num.toReal` of a decimal of sign `s` minus the value of a word of sign `s`. -/
theorem dist_eq (w : UInt64) (d : ℕ) (e : ℤ) :
    |Num.toReal (.dec (Wasm.IEEE64.sign w) d e) - CodeLib.IEEE64.value w| =
      |dv d e - vv (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074| := by
  rw [value_eq, toReal_dec, ← mul_sub, abs_mul]
  split_ifs <;> norm_num

/-- **The code's choice is `Shortest64`**: a positive decimal `t · 10 ^ k` in the interval of a
finite nonzero word `w` that is the printers' choice at the top exponent has no trailing zero and
is `Shortest64 w (sign w) t k`. -/
theorem shortest64 (w : UInt64) (hf : Wasm.IEEE64.isFinite w = true)
    (hz : w.toNat % 2 ^ 63 ≠ 0) (t : ℕ) (k : ℤ) (ht0 : 0 < t)
    (hin : Inside (cl (sig64 (w.toNat % 2 ^ 63)))
      (lo (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074 (low64 (w.toNat % 2 ^ 63)))
      (hi (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074) (dv t k))
    (hc : Choice (cl (sig64 (w.toNat % 2 ^ 63)))
      (lo (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074 (low64 (w.toNat % 2 ^ 63)))
      (hi (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074)
      (vv (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074)
      (top (sig64 (w.toNat % 2 ^ 63)) (bin64 (w.toNat % 2 ^ 63)) 1074 (low64 (w.toNat % 2 ^ 63))
        (sig_pos _ (Nat.pos_of_ne_zero hz)) (bin_pos _) (by norm_num)) t k) :
    t % 10 ≠ 0 ∧ Shortest64 w (Wasm.IEEE64.sign w) t k := by
  have h0 := Nat.pos_of_ne_zero hz
  have hQ := sig_pos _ h0
  obtain ⟨hmod, hord⟩ := shortest_of_choice _ _ _ _ (lo_pos hQ) (hi_le hQ) _
    (top_top hQ (bin_pos _) (by norm_num)) (ex_top hQ (bin_pos _) (by norm_num)) t k ht0 hin hc
  refine ⟨hmod, (round64_iff w hf hz _ t k).mpr ⟨rfl, hin⟩, ?_⟩
  intro neg' d' e' h'
  obtain ⟨hneg, hin'⟩ := (round64_iff w hf hz neg' d' e').mp h'
  subst hneg
  have hd' : 0 < d' := by
    by_contra hc'
    have hl := hin'.lo_le
    rw [show d' = 0 by omega, dv, Nat.cast_zero, zero_mul] at hl
    linarith [lo_pos (E := bin64 (w.toNat % 2 ^ 63)) (nu := 1074)
      (low := low64 (w.toNat % 2 ^ 63)) hQ]
  rw [dist_eq, dist_eq]
  rcases hord d' e' hd' hin' with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    rcases h2 with h | ⟨h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨h3, ?_⟩
      rcases h4 with h | h
      · left
        rw [toReal_dec, toReal_dec, h]
      · exact Or.inr h

/-! ### The code -/

theorem sign_bits (w : UInt64) : (w >>> 63 == 1) = Wasm.IEEE64.sign w := by
  have hw := w.toNat_lt
  have hn : (w >>> 63).toNat = w.toNat / 2 ^ 63 := by
    simp only [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from rfl,
      Nat.shiftRight_eq_div_pow]
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, hn, Wasm.IEEE64.sign, decide_eq_true_iff,
    show (1 : UInt64).toNat = 1 from rfl]
  omega

theorem ef_bits (w : UInt64) : ((w >>> 52) &&& 0x7FF).toNat = w.toNat % 2 ^ 63 / 2 ^ 52 := by
  have hw := w.toNat_lt
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, show (52 : UInt64).toNat % 64 = 52 from rfl,
    Nat.shiftRight_eq_div_pow, show (0x7FF : UInt64).toNat = 2 ^ 11 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem fr_bits (w : UInt64) : (w &&& 0xFFFFFFFFFFFFF).toNat = w.toNat % 2 ^ 63 % 2 ^ 52 := by
  rw [UInt64.toNat_and, show (0xFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 52 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The decimal that `PrintFloat.shortest` computes for a finite nonzero binary64 word. -/
def sh64 (w : UInt64) : UInt64 × UInt64 :=
  shortest (UInt64.ofNat (sig64 (w.toNat % 2 ^ 63))) (UInt64.ofNat (bin64 (w.toNat % 2 ^ 63)))
    (UInt64.ofNat 1074) (low64 (w.toNat % 2 ^ 63))

/-- `print64With` of a finite nonzero word lays out `sh64`. -/
theorem print64_code (ecma : Bool) (w : UInt64) (hf : Wasm.IEEE64.isFinite w = true)
    (hz : w.toNat % 2 ^ 63 ≠ 0) :
    print64With ecma w =
      if ecma then ecmaLayoutW (Wasm.IEEE64.sign w) (sh64 w).1 (sh64 w).2
      else sciLayoutW (Wasm.IEEE64.sign w) (sh64 w).1 (sh64 w).2 := by
  have hfin := finite_bits w hf
  have he := ef_bits w
  have hfr := fr_bits w
  obtain ⟨n, hn⟩ : ∃ n, n = w.toNat % 2 ^ 63 := ⟨_, rfl⟩
  rw [← hn] at he hfr hfin hz
  have c0 : (0 : UInt64).toNat = 0 := rfl
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have e7 : ((w >>> 52) &&& 0x7FF == 0x7FF) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, he,
      show (0x7FF : UInt64).toNat = 2047 from rfl]
    omega
  have e0 : ((w >>> 52) &&& 0x7FF == 0) = decide (n / 2 ^ 52 = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, he, c0, decide_eq_true_iff]
  have f0 : (w &&& 0xFFFFFFFFFFFFF == 0) = decide (n % 2 ^ 52 = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, hfr, c0, decide_eq_true_iff]
  have g2 : decide ((w >>> 52) &&& 0x7FF ≥ 2) = decide (2 ≤ n / 2 ^ 52) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ge_iff_le, UInt64.le_iff_toNat_le,
      he, show (2 : UInt64).toNat = 2 from rfl]
  have hz2 : (decide (n / 2 ^ 52 = 0) && decide (n % 2 ^ 52 = 0)) = false := by
    rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    omega
  have hQ : (if n / 2 ^ 52 = 0 then w &&& 0xFFFFFFFFFFFFF
      else (w &&& 0xFFFFFFFFFFFFF) + 0x10000000000000) = UInt64.ofNat (sig64 n) := by
    apply UInt64.toNat_inj.mp
    unfold sig64
    split_ifs with h
    · rw [hfr, UInt64.toNat_ofNat_of_lt' (by omega)]
    · rw [UInt64.toNat_add, hfr, show (0x10000000000000 : UInt64).toNat = 2 ^ 52 from rfl,
        UInt64.toNat_ofNat_of_lt' (by omega)]
      omega
  have hE : (if n / 2 ^ 52 = 0 then (1 : UInt64) else (w >>> 52) &&& 0x7FF) =
      UInt64.ofNat (bin64 n) := by
    apply UInt64.toNat_inj.mp
    unfold bin64
    split_ifs with h
    · rfl
    · rw [he, UInt64.toNat_ofNat_of_lt' (by omega)]
  have hl : (decide (2 ≤ n / 2 ^ 52) && decide (n % 2 ^ 52 = 0)) = low64 n := by
    rw [low64, Bool.decide_and]
  unfold print64With
  dsimp only
  rw [sign_bits]
  simp only [e7, e0, f0, hz2, g2, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
  rw [hQ, hE, hl, hn]
  rfl

/-- **The layouts of a finite nonzero binary64 word**: `print64` and `print64Ecma` lay out a
decimal `t · 10 ^ k` with no trailing zero that is `Shortest64`. -/
theorem layout64 (w : UInt64) (hf : Wasm.IEEE64.isFinite w = true) (hz : w.toNat % 2 ^ 63 ≠ 0) :
    ∃ t k, t % 10 ≠ 0 ∧ 1 ≤ t ∧ t < 10 ^ 19 ∧ -1100 ≤ k ∧ k ≤ 700 ∧
      Shortest64 w (Wasm.IEEE64.sign w) t k ∧
      print64 w = words (sciLayout (Wasm.IEEE64.sign w) t k) ∧
      print64Ecma w = words (ecmaLayout (Wasm.IEEE64.sign w) t k) := by
  have hfin := finite_bits w hf
  have h0 := Nat.pos_of_ne_zero hz
  have hb := bounds_sig _ hfin h0
  have hsh : sh64 w = shortest (UInt64.ofNat (sig64 (w.toNat % 2 ^ 63)))
      (UInt64.ofNat (bin64 (w.toNat % 2 ^ 63))) (UInt64.ofNat 1074) (low64 (w.toNat % 2 ^ 63)) :=
    rfl
  obtain ⟨ht0, ht62, hk1, hk2, hin, hc⟩ :=
    shortest_spec (low := low64 (w.toNat % 2 ^ 63)) hb (canon_sig _)
  rw [← hsh] at ht0 ht62 hk1 hk2 hin hc
  have hT1 := top_ge (low := low64 (w.toNat % 2 ^ 63)) hb.hQ hb.hE (by norm_num : 1 ≤ 1074)
  have hT2 := top_lt_start (low := low64 (w.toNat % 2 ^ 63)) hb.hQ hb.hE (by norm_num : 1 ≤ 1074)
  have hT3 := (jstart_le hb).1
  obtain ⟨hmod, hs⟩ := shortest64 w hf hz _ _ ht0 hin hc
  refine ⟨(sh64 w).1.toNat, ((sh64 w).2.toNat : ℤ) - 2 ^ 62, hmod, ht0, by omega, by omega,
    by omega, hs, ?_, ?_⟩
  · have h := sci_spec (Wasm.IEEE64.sign w) (sh64 w).1.toNat (sh64 w).2.toNat (by omega)
      (by omega) (by omega)
    rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at h
    unfold print64
    rw [print64_code false w hf hz, ← h]
    rfl
  · have h := ecma_spec (Wasm.IEEE64.sign w) (sh64 w).1.toNat (sh64 w).2.toNat (by omega)
      (by omega) (by omega)
    rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at h
    unfold print64Ecma
    rw [print64_code true w hf hz, ← h]
    rfl

#print axioms round64_iff
#print axioms value_eq
#print axioms shortest64
#print axioms print64_code
#print axioms layout64

end Library.Numerics.Decimal.PrintFloat.PrintFloatWord
