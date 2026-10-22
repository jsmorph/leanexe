import Library.Numerics.Decimal.PrintFloat.PrintFloatWord

/-!
The binary32 words of the printers, as `PrintFloatWord` has them for binary64.  For a finite
nonzero word `x` of magnitude bits `n = x mod 2 ^ 31`, `sig32 n`, `bin32 n`, and `low32 n` are the
significand, the binade, and the flag of the start of a normal binade that
`PrintFloat.print32With` computes from the bits of `x.toUInt64` (`print32_code`).  `round32_iff`
characterizes the decimals that round to `x`, `shortest32` shows that the code's choice is
`Shortest32`, and `layout32` gives the layouts of `print32` and `print32Ecma`.  `print32_low`
states that the printers read only the low 32 bits of their argument.
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatWord32
open PrintFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.ParseFloat.ParseFloatRound Library.Numerics.Decimal.Shared.StrconvRound Library.Numerics.Decimal.Shared.StrconvGrammar Library.Numerics.Decimal.Shared.StrconvGrid
  Library.Numerics.Decimal.Shared.StrconvWords Library.Numerics.Decimal.Shared.StrconvInterval PrintFloatShort PrintFloatQuot PrintFloatSearch PrintFloatPick
  PrintFloatShortest PrintFloatLayout Library.Numerics.Decimal.ParseFloat.ParseFloatTheorem

set_option exponentiation.threshold 4096

/-- The significand of the magnitude bits `n`. -/
def sig32 (n : ℕ) : ℕ := if n / 2 ^ 23 = 0 then n % 2 ^ 23 else n % 2 ^ 23 + 2 ^ 23

/-- The binade of the magnitude bits `n`. -/
def bin32 (n : ℕ) : ℕ := if n / 2 ^ 23 = 0 then 1 else n / 2 ^ 23

/-- The magnitude bits `n` start a normal binade above the first. -/
def low32 (n : ℕ) : Bool := decide (2 ≤ n / 2 ^ 23 ∧ n % 2 ^ 23 = 0)

theorem pack_sig (n : ℕ) : pack b32 (bin32 n) (sig32 n) = n := by
  unfold pack bin32 sig32
  rw [half_b32]
  split_ifs <;> omega

theorem canonical_sig (n : ℕ) (hn : n < 0x7F800000) (h0 : 0 < n) :
    Canonical b32 (bin32 n) (sig32 n) := by
  unfold Canonical bin32 sig32
  rw [half_b32]
  split_ifs <;> omega

theorem bounds_sig (n : ℕ) (hn : n < 0x7F800000) (h0 : 0 < n) :
    WordBounds (sig32 n) (bin32 n) 149 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num⟩ <;> simp only [sig32, bin32] <;>
    split_ifs <;> omega

theorem sig_pos (n : ℕ) (h0 : 0 < n) : 1 ≤ sig32 n := by
  unfold sig32; split_ifs <;> omega

theorem bin_pos (n : ℕ) : 1 ≤ bin32 n := by
  unfold bin32; split_ifs <;> omega

theorem canon_sig (n : ℕ) : bin32 n = 1 ∨ 16 ≤ sig32 n := by
  unfold bin32 sig32; split_ifs <;> omega

/-- `mag` of the magnitude bits. -/
theorem mag_sig (n : ℕ) : mag b32 n = sig32 n * 2 ^ (bin32 n - 1) := by
  unfold mag sig32 bin32
  rw [half_b32]
  split_ifs with h1 h2 h2
  · simp only [Nat.sub_self, pow_zero, mul_one]; omega
  · omega
  · omega
  · ring

/-- The interval of `StrconvInterval` scaled by `2 ^ 149` is that of `PrintFloatSearch`. -/
theorem inside_iff (n : ℕ) (hn : n < 0x7F800000) (h0 : 0 < n) (y : ℝ) :
    InInterval b32 (bin32 n) (sig32 n) (y * 2 ^ 149) ↔
      Inside (cl (sig32 n)) (lo (sig32 n) (bin32 n) 149 (low32 n)) (hi (sig32 n) (bin32 n) 149)
        y := by
  have hQ := sig_pos n h0
  have hp : (0 : ℝ) < 2 ^ 149 := by positivity
  have hS : (2 : ℝ) ^ (149 + 2) = 2 ^ 149 * 4 := by norm_num
  have hlo : lo (sig32 n) (bin32 n) 149 (low32 n) * 2 ^ 149 =
      Library.Numerics.Decimal.Shared.StrconvInterval.lower b32 (bin32 n) (sig32 n) := by
    unfold lo rv nl Library.Numerics.Decimal.Shared.StrconvInterval.lower low32
    rw [half_b32, hS]
    have e : (2 ≤ bin32 n ∧ sig32 n = 2 ^ 23) ↔ (2 ≤ n / 2 ^ 23 ∧ n % 2 ^ 23 = 0) := by
      unfold bin32 sig32; split_ifs <;> omega
    by_cases hl : 2 ≤ n / 2 ^ 23 ∧ n % 2 ^ 23 = 0
    · rw [decide_eq_true hl, ite_eq_left rfl, ite_eq_left (e.mpr hl)]
      have : ((4 * sig32 n - 1 : ℕ) : ℝ) = 4 * (sig32 n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      field_simp
    · rw [decide_eq_false hl, ite_eq_right Bool.false_ne_true,
        ite_eq_right (fun h => hl (e.mp h))]
      have : ((4 * sig32 n - 2 : ℕ) : ℝ) = 2 * (2 * (sig32 n : ℝ) - 1) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      field_simp
      ring
  have hhi : hi (sig32 n) (bin32 n) 149 * 2 ^ 149 = upper (bin32 n) (sig32 n) := by
    unfold hi rv upper
    rw [hS]
    push_cast
    field_simp
    ring
  unfold InInterval Inside cl
  rw [← hlo, ← hhi]
  by_cases he : sig32 n % 2 = 0
  · rw [ite_eq_left he, ite_eq_left (decide_eq_true he)]
    rw [mul_le_mul_iff_of_pos_right hp, mul_le_mul_iff_of_pos_right hp]
  · rw [ite_eq_right he, ite_eq_right (by rw [decide_eq_false he]; exact Bool.false_ne_true)]
    rw [mul_lt_mul_iff_of_pos_right hp, mul_lt_mul_iff_of_pos_right hp]

/-- The magnitude bits of a finite word lie below the encoding of infinity. -/
theorem finite_bits (x : UInt32) (hf : Wasm.IEEE32.isFinite x = true) :
    x.toNat % 2 ^ 31 < 0x7F800000 := by
  unfold Wasm.IEEE32.isFinite Wasm.IEEE32.exponent at hf
  simp only [bne_iff_ne, ne_eq] at hf
  have := x.toNat_lt
  simp only [Nat.reducePow] at hf this ⊢
  omega

/-- **The rounding of a decimal to a finite nonzero binary32 word.** -/
theorem round32_iff (x : UInt32) (hf : Wasm.IEEE32.isFinite x = true)
    (hz : x.toNat % 2 ^ 31 ≠ 0) (neg : Bool) (d : ℕ) (e : ℤ) :
    round32 (.dec neg d e) = x ↔
      neg = Wasm.IEEE32.sign x ∧
        Inside (cl (sig32 (x.toNat % 2 ^ 31)))
          (lo (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149 (low32 (x.toNat % 2 ^ 31)))
          (hi (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149) (dv d e) := by
  obtain ⟨n, hn⟩ : ∃ n, n = x.toNat % 2 ^ 31 := ⟨_, rfl⟩
  rw [← hn]
  have hfin := finite_bits x hf
  rw [← hn] at hfin hz
  have h0 : 0 < n := Nat.pos_of_ne_zero hz
  have hwlt := x.toNat_lt
  have hy0 : (0 : ℝ) ≤ (d : ℝ) * 10 ^ e * 2 ^ 149 := by positivity
  have key : refPos b32 ((d : ℝ) * 10 ^ e * 2 ^ 149) = n ↔
      Inside (cl (sig32 n)) (lo (sig32 n) (bin32 n) 149 (low32 n)) (hi (sig32 n) (bin32 n) 149)
        (dv d e) := by
    have hL : pack b32 (bin32 n) (sig32 n) < limit b32 := by rw [pack_sig, limit_b32]; exact hfin
    have h := interval_iff b32 (bin32 n) (sig32 n) (canonical_sig n hfin h0) hL _ hy0
    rw [pack_sig] at h
    rw [h, inside_iff n hfin h0]
    rfl
  rw [round32_dec, ← key]
  have hr := limit32 ((d : ℝ) * 10 ^ e * 2 ^ 149)
  generalize refPos b32 ((d : ℝ) * 10 ^ e * 2 ^ 149) = r at hr ⊢
  have hrr : (UInt32.ofNat r).toNat = r :=
    UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 2 ^ 32 from rfl]; omega)
  unfold withSign32 Wasm.IEEE32.sign
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro h
      have := congrArg UInt32.toNat h
      rw [hrr] at this
      refine ⟨by rw [eq_comm, decide_eq_false_iff_not]; omega, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [eq_comm, decide_eq_false_iff_not] at h1
      apply UInt32.toNat_inj.mp
      rw [hrr]
      omega
  · simp only [ite_true]
    constructor
    · intro h
      have := congrArg UInt32.toNat h
      rw [negate32 _ (by rw [hrr]; omega), hrr] at this
      refine ⟨by rw [eq_comm, decide_eq_true_iff]; omega, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [eq_comm, decide_eq_true_iff] at h1
      apply UInt32.toNat_inj.mp
      rw [negate32 _ (by rw [hrr]; omega), hrr]
      omega

/-- The magnitude of a word in units of the least subnormal through its magnitude bits. -/
theorem scaledMagnitude_eq (x : UInt32) :
    Wasm.IEEE32.scaledMagnitude x = mag b32 (x.toNat % 2 ^ 31) := by
  have hw := x.toNat_lt
  have he : Wasm.IEEE32.exponent x = x.toNat % 2 ^ 31 / 2 ^ 23 := by
    unfold Wasm.IEEE32.exponent; omega
  have hfr : Wasm.IEEE32.fraction x = x.toNat % 2 ^ 31 % 2 ^ 23 := by
    unfold Wasm.IEEE32.fraction; omega
  unfold Wasm.IEEE32.scaledMagnitude mag
  rw [he, hfr, half_b32]
  simp only [beq_iff_eq]
  split_ifs <;> omega

theorem bits_ne_zero (x : UInt32) (hz : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    x.toNat % 2 ^ 31 ≠ 0 := by
  intro h
  apply hz
  rw [scaledMagnitude_eq, h, mag, ite_eq_left (by rw [half_b32]; norm_num)]

/-- The value of a finite binary32 word through its significand and binade. -/
theorem value_eq (x : UInt32) :
    CodeLib.IEEE32.value x = (if Wasm.IEEE32.sign x then -1 else 1) *
      vv (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149 := by
  have hm := scaledMagnitude_eq x
  have hv : vv (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149 =
      (mag b32 (x.toNat % 2 ^ 31) : ℝ) / 2 ^ 149 := by
    unfold vv rv
    rw [mag_sig]
    push_cast
    rw [show (2 : ℝ) ^ (149 + 2) = 2 ^ 149 * 4 by norm_num]
    field_simp
  rw [hv, CodeLib.IEEE32.value, Wasm.IEEE32.scaledValue, hm]
  split_ifs <;> push_cast <;> ring

/-- `Num.toReal` of a decimal of sign `s` minus the value of a word of sign `s`. -/
theorem dist_eq (x : UInt32) (d : ℕ) (e : ℤ) :
    |Num.toReal (.dec (Wasm.IEEE32.sign x) d e) - CodeLib.IEEE32.value x| =
      |dv d e - vv (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149| := by
  rw [value_eq, PrintFloatWord.toReal_dec, ← mul_sub, abs_mul]
  split_ifs <;> norm_num

/-- **The code's choice is `Shortest32`**: a positive decimal `t · 10 ^ k` in the interval of a
finite nonzero word `x` that is the printers' choice at the top exponent has no trailing zero and
is `Shortest32 x (sign x) t k`. -/
theorem shortest32 (x : UInt32) (hf : Wasm.IEEE32.isFinite x = true)
    (hz : x.toNat % 2 ^ 31 ≠ 0) (t : ℕ) (k : ℤ) (ht0 : 0 < t)
    (hin : Inside (cl (sig32 (x.toNat % 2 ^ 31)))
      (lo (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149 (low32 (x.toNat % 2 ^ 31)))
      (hi (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149) (dv t k))
    (hc : Choice (cl (sig32 (x.toNat % 2 ^ 31)))
      (lo (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149 (low32 (x.toNat % 2 ^ 31)))
      (hi (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149)
      (vv (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149)
      (top (sig32 (x.toNat % 2 ^ 31)) (bin32 (x.toNat % 2 ^ 31)) 149 (low32 (x.toNat % 2 ^ 31))
        (sig_pos _ (Nat.pos_of_ne_zero hz)) (bin_pos _) (by norm_num)) t k) :
    t % 10 ≠ 0 ∧ Shortest32 x (Wasm.IEEE32.sign x) t k := by
  have h0 := Nat.pos_of_ne_zero hz
  have hQ := sig_pos _ h0
  obtain ⟨hmod, hord⟩ := shortest_of_choice _ _ _ _ (lo_pos hQ) (hi_le hQ) _
    (top_top hQ (bin_pos _) (by norm_num)) (ex_top hQ (bin_pos _) (by norm_num)) t k ht0 hin hc
  refine ⟨hmod, (round32_iff x hf hz _ t k).mpr ⟨rfl, hin⟩, ?_⟩
  intro neg' d' e' h'
  obtain ⟨hneg, hin'⟩ := (round32_iff x hf hz neg' d' e').mp h'
  subst hneg
  have hd' : 0 < d' := by
    by_contra hc'
    have hl := hin'.lo_le
    rw [show d' = 0 by omega, dv, Nat.cast_zero, zero_mul] at hl
    linarith [lo_pos (E := bin32 (x.toNat % 2 ^ 31)) (nu := 149)
      (low := low32 (x.toNat % 2 ^ 31)) hQ]
  rw [dist_eq, dist_eq]
  rcases hord d' e' hd' hin' with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, ?_⟩
    rcases h2 with h | ⟨h3, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨h3, ?_⟩
      rcases h4 with h | h
      · left
        rw [PrintFloatWord.toReal_dec, PrintFloatWord.toReal_dec, h]
      · exact Or.inr h

/-! ### The code -/

theorem toNat_mask (x : UInt32) : x.toUInt64 &&& 0xFFFFFFFF = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  rw [UInt64.toNat_and, UInt32.toNat_toUInt64,
    show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem sign_bits (x : UInt32) : (x.toUInt64 >>> 31 == 1) = Wasm.IEEE32.sign x := by
  have hx := x.toNat_lt
  have hn : (x.toUInt64 >>> 31).toNat = x.toNat / 2 ^ 31 := by
    simp only [UInt64.toNat_shiftRight, show (31 : UInt64).toNat % 64 = 31 from rfl,
      Nat.shiftRight_eq_div_pow, UInt32.toNat_toUInt64]
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, hn, Wasm.IEEE32.sign, decide_eq_true_iff,
    show (1 : UInt64).toNat = 1 from rfl]
  omega

theorem ef_bits (x : UInt32) :
    ((x.toUInt64 >>> 23) &&& 0xFF).toNat = x.toNat % 2 ^ 31 / 2 ^ 23 := by
  have hx := x.toNat_lt
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, show (23 : UInt64).toNat % 64 = 23 from rfl,
    Nat.shiftRight_eq_div_pow, show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt32.toNat_toUInt64]
  omega

theorem fr_bits (x : UInt32) : (x.toUInt64 &&& 0x7FFFFF).toNat = x.toNat % 2 ^ 31 % 2 ^ 23 := by
  rw [UInt64.toNat_and, show (0x7FFFFF : UInt64).toNat = 2 ^ 23 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt32.toNat_toUInt64]
  omega

/-- The decimal that `PrintFloat.shortest` computes for a finite nonzero binary32 word. -/
def sh32 (x : UInt32) : UInt64 × UInt64 :=
  shortest (UInt64.ofNat (sig32 (x.toNat % 2 ^ 31))) (UInt64.ofNat (bin32 (x.toNat % 2 ^ 31)))
    (UInt64.ofNat 149) (low32 (x.toNat % 2 ^ 31))

/-- `print32With` of a finite nonzero word lays out `sh32`. -/
theorem print32_code (ecma : Bool) (x : UInt32) (hf : Wasm.IEEE32.isFinite x = true)
    (hz : x.toNat % 2 ^ 31 ≠ 0) :
    print32With ecma x.toUInt64 =
      if ecma then ecmaLayoutW (Wasm.IEEE32.sign x) (sh32 x).1 (sh32 x).2
      else sciLayoutW (Wasm.IEEE32.sign x) (sh32 x).1 (sh32 x).2 := by
  have hfin := finite_bits x hf
  have he := ef_bits x
  have hfr := fr_bits x
  obtain ⟨n, hn⟩ : ∃ n, n = x.toNat % 2 ^ 31 := ⟨_, rfl⟩
  rw [← hn] at he hfr hfin hz
  have c0 : (0 : UInt64).toNat = 0 := rfl
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have e7 : ((x.toUInt64 >>> 23) &&& 0xFF == 0xFF) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, he,
      show (0xFF : UInt64).toNat = 255 from rfl]
    omega
  have e0 : ((x.toUInt64 >>> 23) &&& 0xFF == 0) = decide (n / 2 ^ 23 = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, he, c0, decide_eq_true_iff]
  have f0 : (x.toUInt64 &&& 0x7FFFFF == 0) = decide (n % 2 ^ 23 = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, hfr, c0, decide_eq_true_iff]
  have g2 : decide ((x.toUInt64 >>> 23) &&& 0xFF ≥ 2) = decide (2 ≤ n / 2 ^ 23) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ge_iff_le, UInt64.le_iff_toNat_le,
      he, show (2 : UInt64).toNat = 2 from rfl]
  have hz2 : (decide (n / 2 ^ 23 = 0) && decide (n % 2 ^ 23 = 0)) = false := by
    rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    omega
  have hQ : (if n / 2 ^ 23 = 0 then x.toUInt64 &&& 0x7FFFFF
      else (x.toUInt64 &&& 0x7FFFFF) + 0x800000) = UInt64.ofNat (sig32 n) := by
    apply UInt64.toNat_inj.mp
    unfold sig32
    split_ifs with h
    · rw [hfr, UInt64.toNat_ofNat_of_lt' (by omega)]
    · rw [UInt64.toNat_add, hfr, show (0x800000 : UInt64).toNat = 2 ^ 23 from rfl,
        UInt64.toNat_ofNat_of_lt' (by omega)]
      omega
  have hE : (if n / 2 ^ 23 = 0 then (1 : UInt64) else (x.toUInt64 >>> 23) &&& 0xFF) =
      UInt64.ofNat (bin32 n) := by
    apply UInt64.toNat_inj.mp
    unfold bin32
    split_ifs with h
    · rfl
    · rw [he, UInt64.toNat_ofNat_of_lt' (by omega)]
  have hl : (decide (2 ≤ n / 2 ^ 23) && decide (n % 2 ^ 23 = 0)) = low32 n := by
    rw [low32, Bool.decide_and]
  unfold print32With
  dsimp only
  rw [toNat_mask, sign_bits]
  simp only [e7, e0, f0, hz2, g2, decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
  rw [hQ, hE, hl, hn]
  rfl

/-- **The layouts of a finite nonzero binary32 word**: `print32` and `print32Ecma` lay out a
decimal `t · 10 ^ k` with no trailing zero that is `Shortest32`. -/
theorem layout32 (x : UInt32) (hf : Wasm.IEEE32.isFinite x = true) (hz : x.toNat % 2 ^ 31 ≠ 0) :
    ∃ t k, t % 10 ≠ 0 ∧ 1 ≤ t ∧ t < 10 ^ 19 ∧ -1100 ≤ k ∧ k ≤ 700 ∧
      Shortest32 x (Wasm.IEEE32.sign x) t k ∧
      print32 x.toUInt64 = words (sciLayout (Wasm.IEEE32.sign x) t k) ∧
      print32Ecma x.toUInt64 = words (ecmaLayout (Wasm.IEEE32.sign x) t k) := by
  have hfin := finite_bits x hf
  have h0 := Nat.pos_of_ne_zero hz
  have hb := bounds_sig _ hfin h0
  have hsh : sh32 x = shortest (UInt64.ofNat (sig32 (x.toNat % 2 ^ 31)))
      (UInt64.ofNat (bin32 (x.toNat % 2 ^ 31))) (UInt64.ofNat 149) (low32 (x.toNat % 2 ^ 31)) :=
    rfl
  obtain ⟨ht0, ht62, hk1, hk2, hin, hc⟩ :=
    shortest_spec (low := low32 (x.toNat % 2 ^ 31)) hb (canon_sig _)
  rw [← hsh] at ht0 ht62 hk1 hk2 hin hc
  have hT1 := top_ge (low := low32 (x.toNat % 2 ^ 31)) hb.hQ hb.hE (by norm_num : 1 ≤ 149)
  have hT2 := top_lt_start (low := low32 (x.toNat % 2 ^ 31)) hb.hQ hb.hE (by norm_num : 1 ≤ 149)
  have hT3 := (jstart_le hb).1
  obtain ⟨hmod, hs⟩ := shortest32 x hf hz _ _ ht0 hin hc
  refine ⟨(sh32 x).1.toNat, ((sh32 x).2.toNat : ℤ) - 2 ^ 62, hmod, ht0, by omega, by omega,
    by omega, hs, ?_, ?_⟩
  · have h := sci_spec (Wasm.IEEE32.sign x) (sh32 x).1.toNat (sh32 x).2.toNat (by omega)
      (by omega) (by omega)
    rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at h
    unfold print32
    rw [print32_code false x hf hz, ← h]
    rfl
  · have h := ecma_spec (Wasm.IEEE32.sign x) (sh32 x).1.toNat (sh32 x).2.toNat (by omega)
      (by omega) (by omega)
    rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at h
    unfold print32Ecma
    rw [print32_code true x hf hz, ← h]
    rfl

/-- **The printers read the low 32 bits.** -/
theorem print32_low (w : UInt64) : print32 w = print32 w.toUInt32.toUInt64 := by
  have h : w &&& 0xFFFFFFFF = w.toUInt32.toUInt64 &&& 0xFFFFFFFF := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32,
      show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  unfold print32 print32With
  rw [h]

theorem print32Ecma_low (w : UInt64) : print32Ecma w = print32Ecma w.toUInt32.toUInt64 := by
  have h : w &&& 0xFFFFFFFF = w.toUInt32.toUInt64 &&& 0xFFFFFFFF := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32,
      show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  unfold print32Ecma print32With
  rw [h]

#print axioms round32_iff
#print axioms value_eq
#print axioms shortest32
#print axioms print32_code
#print axioms layout32
#print axioms print32_low
#print axioms print32Ecma_low

end Library.Numerics.Decimal.PrintFloat.PrintFloatWord32
