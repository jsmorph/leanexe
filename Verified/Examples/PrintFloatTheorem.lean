import Verified.Examples.PrintFloatWord32
import Verified.Examples.PrintFloatDerive

/-!
The theorems of the specification of [the printers](PrintFloat.md).  For every binary64 word `w`,
`print64 w` and `print64Ecma w` are numbers of the general grammar that round back to `canon64 w`
(`print64_derives`), so the general parser reads them back as `canon64 w` (`print64_roundtrip`).
The strings of finite words are numbers of RFC 8259's grammar (`print64_json`), and those of finite
nonzero words denote a decimal that is `Shortest64` (`print64_shortest`), laid out by `sciLayout`
and `ecmaLayout` (`print64_layout`).  The binary32 theorems take `x : UInt32` with the input
`x.toUInt64`, and `PrintFloatWord32.print32_low` reduces every other input to that form.
-/

namespace Verified.Examples.PrintFloatTheorem
open PrintFloat ParseFloat StrconvRound StrconvGrammar StrconvGrid StrconvWords StrconvDecode
  ParseFloatTheorem PrintFloatShort PrintFloatDigits PrintFloatDerive

set_option exponentiation.threshold 4096

/-! ### Trailing zeros -/

theorem strip_unique (s s' i j : ℕ) (hs : s % 10 ≠ 0) (hs' : s' % 10 ≠ 0)
    (h : s * 10 ^ i = s' * 10 ^ j) : s = s' := by
  rcases le_total i j with hij | hij
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have h' : s = s' * 10 ^ d :=
      Nat.eq_of_mul_eq_mul_right (show 0 < 10 ^ i by positivity) (by rw [h, pow_add]; ring)
    cases d with
    | zero => simpa using h'
    | succ d => exact absurd (by rw [h', pow_succ, ← mul_assoc, Nat.mul_mod_left]) hs
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have h' : s' = s * 10 ^ d :=
      Nat.eq_of_mul_eq_mul_right (show 0 < 10 ^ j by positivity) (by rw [← h, pow_add]; ring)
    cases d with
    | zero => simpa using h'.symm
    | succ d => exact absurd (by rw [h', pow_succ, ← mul_assoc, Nat.mul_mod_left]) hs'

theorem stripZeros_shift (t z : ℕ) : stripZeros (t * 10 ^ z) = stripZeros t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [zero_mul]
  · obtain ⟨-, h2, a, ha⟩ := stripZeros_spec t ht
    obtain ⟨-, h2', b, hb⟩ := stripZeros_spec (t * 10 ^ z) (by positivity)
    apply strip_unique _ _ b (a + z) h2' h2
    rw [← hb, pow_add, ← mul_assoc, ← ha]

theorem dec_shift (t z : ℕ) :
    ((t * 10 ^ z : ℕ) : ℝ) * (10 : ℝ) ^ (0 : ℤ) = (t : ℝ) * 10 ^ (z : ℤ) := by
  have := dv_shift t z 0
  unfold dv at this
  rw [this, zero_add]

theorem toReal_shift (neg : Bool) (t z : ℕ) :
    Num.toReal (.dec neg (t * 10 ^ z) 0) = Num.toReal (.dec neg t z) := by
  rw [PrintFloatWord.toReal_dec, PrintFloatWord.toReal_dec, dv_shift, zero_add]

/-- The plain ECMAScript layout with trailing zeros denotes a `Shortest64` decimal. -/
theorem shortest64_shift (w : UInt64) (neg : Bool) (t z : ℕ) (h : Shortest64 w neg t z) :
    Shortest64 w neg (t * 10 ^ z) 0 := by
  have hr : round64 (.dec neg (t * 10 ^ z) 0) = round64 (.dec neg t z) := by
    rw [round64_dec, round64_dec, dec_shift]
  have hsig : sigDigits (t * 10 ^ z) = sigDigits t := by unfold sigDigits; rw [stripZeros_shift]
  refine ⟨hr.trans h.1, fun neg' d' e' h' => ?_⟩
  rw [hsig, toReal_shift, stripZeros_shift]
  exact h.2 neg' d' e' h'

theorem shortest32_shift (x : UInt32) (neg : Bool) (t z : ℕ) (h : Shortest32 x neg t z) :
    Shortest32 x neg (t * 10 ^ z) 0 := by
  have hr : round32 (.dec neg (t * 10 ^ z) 0) = round32 (.dec neg t z) := by
    rw [round32_dec, round32_dec, dec_shift]
  have hsig : sigDigits (t * 10 ^ z) = sigDigits t := by unfold sigDigits; rw [stripZeros_shift]
  refine ⟨hr.trans h.1, fun neg' d' e' h' => ?_⟩
  rw [hsig, toReal_shift, stripZeros_shift]
  exact h.2 neg' d' e' h'

/-! ### Zeros, infinities, and NaNs -/

theorem refPos_zero (f : Fmt) : refPos f 0 = 0 := by
  have hB := half_pos f
  have hT : ¬ threshold f ≤ 0 := by
    rw [threshold_eq]
    have : (1 : ℝ) ≤ half f := by exact_mod_cast hB
    have : (0 : ℝ) < 2 ^ (f.F - 3) := by positivity
    intro h
    nlinarith
  unfold refPos
  rw [ite_eq_right hT]
  have hm0 : mag f 0 = 0 := by unfold mag; rw [ite_eq_left hB]
  apply nearest_even_unique f 0 _ 0 (Classical.choose_spec (exists_nearest_even f 0))
  refine ⟨⟨?_, fun m _ => ?_⟩, fun m _ => ?_⟩
  · unfold limit; have := f.hF; positivity
  · rw [hm0, Nat.cast_zero, sub_zero, abs_zero]; exact abs_nonneg _
  · omega

theorem round64_zero (neg : Bool) : round64 (.dec neg 0 0) = withSign64 neg 0 := by
  rw [round64_dec, Nat.cast_zero, zero_mul, zero_mul, refPos_zero]
  rfl

theorem round32_zero (neg : Bool) : round32 (.dec neg 0 0) = withSign32 neg 0 := by
  rw [round32_dec, Nat.cast_zero, zero_mul, zero_mul, refPos_zero]
  rfl

theorem sign_general (neg : Bool) : Sign true (if neg then ascii "-" else []) neg := by
  cases neg
  · exact Sign.none true
  · exact Sign.minus true

theorem sign_length (neg : Bool) : (if neg then ascii "-" else []).length ≤ 1 := by
  cases neg <;> decide

theorem nan_derives : Derives true (ascii "NaN") .nan := by
  simpa only [List.nil_append] using
    Derives.nan [] (ascii "NaN") false (Sign.none true) (by decide)

theorem inf_derives (neg : Bool) :
    Derives true ((if neg then ascii "-" else []) ++ ascii "Infinity") (.inf neg) :=
  Derives.inf _ (ascii "Infinity") neg (sign_general neg) (by decide)

theorem zero_sci_derives (neg : Bool) :
    Derives false ((if neg then ascii "-" else []) ++ ascii "0e0") (.dec neg 0 0) := by
  have h := Derives.json (if neg then ascii "-" else []) (ascii "0") [] [] _ neg _ (sign_json neg)
    JsonInt.zero JsonFrac.none
    (OptExponent.some _ _ (Exponent.plain 0x65 (ascii "0") marker_e (by decide) (by decide)))
  rw [List.append_nil, List.append_assoc,
    show ascii "0" ++ 0x65 :: ascii "0" = ascii "0e0" by decide,
    show decValue (ascii "0" ++ []) = 0 by decide,
    show ((decValue (ascii "0") : ℕ) : ℤ) - (([] : List UInt8).length : ℤ) = 0 by decide] at h
  exact h

theorem zero_ecma_derives (neg : Bool) :
    Derives false ((if neg then ascii "-" else []) ++ ascii "0") (.dec neg 0 0) := by
  have h := Derives.json (if neg then ascii "-" else []) (ascii "0") [] [] [] neg 0 (sign_json neg)
    JsonInt.zero JsonFrac.none OptExponent.none
  rw [List.append_nil, List.append_nil, show decValue (ascii "0" ++ []) = 0 by decide,
    show (0 : ℤ) - (([] : List UInt8).length : ℤ) = 0 by decide] at h
  exact h

theorem special_nan (neg inf ecma : Bool) : special neg inf true ecma = words (ascii "NaN") := by
  cases neg <;> cases inf <;> cases ecma <;> decide

theorem special_inf (neg ecma : Bool) :
    special neg true false ecma = words ((if neg then ascii "-" else []) ++ ascii "Infinity") := by
  cases neg <;> cases ecma <;> decide

theorem special_zero (neg ecma : Bool) :
    special neg false false ecma =
      words ((if neg then ascii "-" else []) ++ if ecma then ascii "0" else ascii "0e0") := by
  cases neg <;> cases ecma <;> decide

theorem zero_derives (neg ecma : Bool) :
    Derives false ((if neg then ascii "-" else []) ++ if ecma then ascii "0" else ascii "0e0")
      (.dec neg 0 0) := by
  cases ecma
  · exact zero_sci_derives neg
  · exact zero_ecma_derives neg

theorem zero_length (neg ecma : Bool) :
    ((if neg then ascii "-" else []) ++ if ecma then ascii "0" else ascii "0e0").length <
      2 ^ 32 := by
  cases neg <;> cases ecma <;> decide

/-! ### Lengths -/

theorem sci_length (neg : Bool) (t : ℕ) (k : ℤ) (ht : t < 10 ^ 19) (hk1 : -1100 ≤ k)
    (hk2 : k ≤ 700) : (sciLayout neg t k).length < 2 ^ 32 := by
  have h1 := dlen_le t 19 ht (by norm_num)
  unfold dlen at h1
  have h2 := dlen_le (k + (digitsOf t).length - 1).natAbs 19 (by omega) (by norm_num)
  unfold dlen at h2
  have h3 := sign_length neg
  unfold sciLayout
  dsimp only
  simp only [List.length_append, List.length_take]
  have h4 : (if (digitsOf t).length = 1 then [] else ascii "." ++ (digitsOf t).drop 1).length ≤
      1 + (digitsOf t).length := by
    split_ifs
    · simp
    · simp only [List.length_append, List.length_drop]
      rw [show (ascii ".").length = 1 from rfl]
      omega
  have h5 : (if k + ((digitsOf t).length : ℤ) - 1 < 0 then ascii "-" else []).length ≤ 1 := by
    split_ifs <;> decide
  rw [show (ascii "e").length = 1 from rfl]
  omega

theorem ecma_length (neg : Bool) (t : ℕ) (k : ℤ) (ht : t < 10 ^ 19) (hk1 : -1100 ≤ k)
    (hk2 : k ≤ 700) : (ecmaLayout neg t k).length < 2 ^ 32 := by
  have h1 := dlen_le t 19 ht (by norm_num)
  unfold dlen at h1
  have h2 := dlen_le (k + ((digitsOf t).length : ℤ) - 1).natAbs 19 (by omega) (by norm_num)
  unfold dlen at h2
  have la : (ascii "-").length = 1 := rfl
  have lb : (ascii "+").length = 1 := rfl
  have lc : (ascii ".").length = 1 := rfl
  have ld : (ascii "e").length = 1 := rfl
  have le : (ascii "0.").length = 2 := rfl
  unfold ecmaLayout
  dsimp only
  rw [List.length_append]
  refine lt_of_le_of_lt (Nat.add_le_add (sign_length neg) (?_ : _ ≤ 2000)) (by norm_num)
  split_ifs <;>
    simp only [List.length_append, List.length_replicate, List.length_take, List.length_drop,
      List.length_nil, la, lb, lc, ld, le] <;>
    omega

/-! ### Binary64 -/

theorem canon64_finite (w : UInt64) (hf : Wasm.IEEE64.isFinite w = true) : canon64 w = w := by
  have h : Wasm.IEEE64.isNaN w = false := by
    unfold Wasm.IEEE64.isNaN
    unfold Wasm.IEEE64.isFinite at hf
    rw [Bool.and_eq_false_iff]
    left
    simpa using hf
  unfold canon64
  rw [h]
  rfl

theorem zero_word64 (w : UInt64) (hz : w.toNat % 2 ^ 63 = 0) :
    withSign64 (Wasm.IEEE64.sign w) 0 = w := by
  have hw := w.toNat_lt
  apply UInt64.toNat_inj.mp
  unfold withSign64 Wasm.IEEE64.sign
  by_cases hs : 2 ^ 63 ≤ w.toNat
  · rw [decide_eq_true hs, ite_eq_left rfl, ParseFloatTheorem.negate64 0 (by decide)]
    simp only [UInt64.toNat_zero]
    omega
  · rw [decide_eq_false hs, ite_eq_right Bool.false_ne_true, UInt64.toNat_zero]
    omega

theorem inf_word64 (w : UInt64) (hf : Wasm.IEEE64.isFinite w = false)
    (hn : Wasm.IEEE64.isNaN w = false) :
    withSign64 (Wasm.IEEE64.sign w) 0x7FF0000000000000 = w := by
  have hw := w.toNat_lt
  unfold Wasm.IEEE64.isFinite at hf
  unfold Wasm.IEEE64.isNaN at hn
  simp only [bne_eq_false_iff_eq] at hf
  rw [hf] at hn
  simp only [beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
  unfold Wasm.IEEE64.exponent at hf
  unfold Wasm.IEEE64.fraction at hn
  apply UInt64.toNat_inj.mp
  unfold withSign64 Wasm.IEEE64.sign
  by_cases hs : 2 ^ 63 ≤ w.toNat
  · rw [decide_eq_true hs, ite_eq_left rfl, ParseFloatTheorem.negate64 _ (by decide)]
    rw [show (0x7FF0000000000000 : UInt64).toNat = 0x7FF0000000000000 from rfl]
    omega
  · rw [decide_eq_false hs, ite_eq_right Bool.false_ne_true,
      show (0x7FF0000000000000 : UInt64).toNat = 0x7FF0000000000000 from rfl]
    omega

theorem print64_nonfinite (ecma : Bool) (w : UInt64) (hf : Wasm.IEEE64.isFinite w = false) :
    print64With ecma w = special (Wasm.IEEE64.sign w) true (Wasm.IEEE64.isNaN w) ecma := by
  have hw := w.toNat_lt
  have he := PrintFloatWord.ef_bits w
  have hfr := PrintFloatWord.fr_bits w
  unfold Wasm.IEEE64.isFinite Wasm.IEEE64.exponent at hf
  simp only [bne_eq_false_iff_eq] at hf
  have e7 : ((w >>> 52) &&& 0x7FF == 0x7FF) = true := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, he, show (0x7FF : UInt64).toNat = 2047 from rfl]
    omega
  have hn : (w &&& 0xFFFFFFFFFFFFF != 0) = Wasm.IEEE64.isNaN w := by
    unfold Wasm.IEEE64.isNaN Wasm.IEEE64.exponent Wasm.IEEE64.fraction
    rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq, ← UInt64.toNat_inj, hfr,
      UInt64.toNat_zero]
    omega
  unfold print64With
  dsimp only
  rw [PrintFloatWord.sign_bits]
  simp only [e7, ↓reduceIte, hn]

theorem print64_zero (ecma : Bool) (w : UInt64) (hz : w.toNat % 2 ^ 63 = 0) :
    print64With ecma w = special (Wasm.IEEE64.sign w) false false ecma := by
  have he := PrintFloatWord.ef_bits w
  have hfr := PrintFloatWord.fr_bits w
  have e7 : ((w >>> 52) &&& 0x7FF == 0x7FF) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, he,
      show (0x7FF : UInt64).toNat = 2047 from rfl]
    omega
  have ez : ((w >>> 52) &&& 0x7FF == 0 && w &&& 0xFFFFFFFFFFFFF == 0) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, ← UInt64.toNat_inj, he, hfr, UInt64.toNat_zero]
    omega
  unfold print64With
  dsimp only
  rw [PrintFloatWord.sign_bits]
  simp only [e7, ez, Bool.false_eq_true, ↓reduceIte]

/-- Both printers' strings of a binary64 word: a number of the general grammar that rounds to
`canon64 w`, of RFC 8259's grammar for a finite word, shorter than `2 ^ 32` bytes, and for a
finite nonzero word the layout of a `Shortest64` decimal. -/
theorem derives64 (ecma : Bool) (w : UInt64) :
    ∃ s n, print64With ecma w = words s ∧ Derives true s n ∧
      (Wasm.IEEE64.isFinite w = true → Derives false s n) ∧ round64 n = canon64 w ∧
      s.length < 2 ^ 32 ∧
      (Wasm.IEEE64.isFinite w = true → Wasm.IEEE64.scaledMagnitude w ≠ 0 →
        ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧
          s = if ecma then ecmaLayout neg t k else sciLayout neg t k) := by
  by_cases hf : Wasm.IEEE64.isFinite w = true
  · by_cases hz : w.toNat % 2 ^ 63 = 0
    · have hd := zero_derives (Wasm.IEEE64.sign w) ecma
      refine ⟨_, _, by rw [print64_zero ecma w hz, special_zero], derives_general hd,
        fun _ => hd, ?_, zero_length _ _,
        fun _ hz' => absurd hz (PrintFloatWord.bits_ne_zero w hz')⟩
      rw [round64_zero, zero_word64 w hz, canon64_finite w hf]
    · obtain ⟨t, k, hmod, ht1, ht19, hk1, hk2, hs, hp, he⟩ := PrintFloatWord.layout64 w hf hz
      cases ecma
      · have hd := sci_derives (Wasm.IEEE64.sign w) t k ht1
        exact ⟨_, _, hp, derives_general hd, fun _ => hd, by rw [hs.1, canon64_finite w hf],
          sci_length _ _ _ ht19 hk1 hk2, fun _ _ => ⟨_, t, k, hmod, hs, rfl⟩⟩
      · rcases ecma_derives (Wasm.IEEE64.sign w) t k ht1 with hd | ⟨z, rfl, hd⟩
        · exact ⟨_, _, he, derives_general hd, fun _ => hd, by rw [hs.1, canon64_finite w hf],
            ecma_length _ _ _ ht19 hk1 hk2, fun _ _ => ⟨_, t, k, hmod, hs, rfl⟩⟩
        · exact ⟨_, _, he, derives_general hd, fun _ => hd,
            by rw [(shortest64_shift w _ t z hs).1, canon64_finite w hf],
            ecma_length _ _ _ ht19 hk1 hk2, fun _ _ => ⟨_, t, z, hmod, hs, rfl⟩⟩
  · have hfF : Wasm.IEEE64.isFinite w = false := by simpa using hf
    by_cases hnan : Wasm.IEEE64.isNaN w = true
    · refine ⟨_, _, by rw [print64_nonfinite ecma w hfF, hnan, special_nan], nan_derives,
        fun h => absurd h hf, ?_, by decide, fun h => absurd h hf⟩
      unfold canon64
      rw [ite_eq_left hnan]
      rfl
    · have hnF : Wasm.IEEE64.isNaN w = false := by simpa using hnan
      refine ⟨_, _, by rw [print64_nonfinite ecma w hfF, hnF, special_inf], inf_derives _,
        fun h => absurd h hf, ?_, ?_, fun h => absurd h hf⟩
      · unfold canon64
        rw [hnF, ite_eq_right Bool.false_ne_true]
        exact inf_word64 w hfF hnF
      · have := sign_length (Wasm.IEEE64.sign w)
        rw [List.length_append, show (ascii "Infinity").length = 8 from rfl]
        omega

/-- **Every string of `print64` is a number of the general grammar that rounds to the word**,
the canonical NaN for a NaN. -/
theorem print64_derives (w : UInt64) :
    ∃ s n, print64 w = words s ∧ Derives true s n ∧ round64 n = canon64 w := by
  obtain ⟨s, n, h1, h2, -, h4, -, -⟩ := derives64 false w
  exact ⟨s, n, h1, h2, h4⟩

theorem print64Ecma_derives (w : UInt64) :
    ∃ s n, print64Ecma w = words s ∧ Derives true s n ∧ round64 n = canon64 w := by
  obtain ⟨s, n, h1, h2, -, h4, -, -⟩ := derives64 true w
  exact ⟨s, n, h1, h2, h4⟩

/-- **The round trip**: the general parser reads `print64 w` back as `canon64 w`. -/
theorem print64_roundtrip (w : UInt64) : parse64 true (print64 w) = (true, canon64 w) := by
  obtain ⟨s, n, h1, h2, -, h4, h5, -⟩ := derives64 false w
  show parse64 true (print64With false w) = _
  rw [h1, parse64_accept true s n h5 h2, h4]

theorem print64Ecma_roundtrip (w : UInt64) : parse64 true (print64Ecma w) = (true, canon64 w) := by
  obtain ⟨s, n, h1, h2, -, h4, h5, -⟩ := derives64 true w
  show parse64 true (print64With true w) = _
  rw [h1, parse64_accept true s n h5 h2, h4]

/-- The strings of a finite word are numbers of RFC 8259's grammar. -/
theorem print64_json (w : UInt64) (hf : Wasm.IEEE64.isFinite w) :
    (∃ s n, print64 w = words s ∧ Derives false s n) ∧
      ∃ s n, print64Ecma w = words s ∧ Derives false s n := by
  obtain ⟨s, n, h1, -, h3, -, -⟩ := derives64 false w
  obtain ⟨s', n', h1', -, h3', -, -⟩ := derives64 true w
  exact ⟨⟨s, n, h1, h3 hf⟩, s', n', h1', h3' hf⟩

/-- **The shortest decimal**: the string of a finite nonzero word is a number of RFC 8259's
grammar that denotes a `Shortest64` decimal. -/
theorem print64_shortest (w : UInt64) (hf : Wasm.IEEE64.isFinite w)
    (hz : Wasm.IEEE64.scaledMagnitude w ≠ 0) :
    ∃ s neg d e, print64 w = words s ∧ Derives false s (.dec neg d e) ∧ Shortest64 w neg d e := by
  obtain ⟨t, k, -, ht1, -, -, -, hs, hp, -⟩ :=
    PrintFloatWord.layout64 w hf (PrintFloatWord.bits_ne_zero w hz)
  exact ⟨_, _, _, _, hp, sci_derives _ t k ht1, hs⟩

theorem print64Ecma_shortest (w : UInt64) (hf : Wasm.IEEE64.isFinite w)
    (hz : Wasm.IEEE64.scaledMagnitude w ≠ 0) :
    ∃ s neg d e, print64Ecma w = words s ∧ Derives false s (.dec neg d e) ∧
      Shortest64 w neg d e := by
  obtain ⟨t, k, -, ht1, -, -, -, hs, -, he⟩ :=
    PrintFloatWord.layout64 w hf (PrintFloatWord.bits_ne_zero w hz)
  rcases ecma_derives (Wasm.IEEE64.sign w) t k ht1 with hd | ⟨z, rfl, hd⟩
  · exact ⟨_, _, _, _, he, hd, hs⟩
  · exact ⟨_, _, _, _, he, hd, shortest64_shift w _ t z hs⟩

/-- **The layouts**: both strings of a finite nonzero word lay out one `Shortest64` decimal with no
trailing zero. -/
theorem print64_layout (w : UInt64) (hf : Wasm.IEEE64.isFinite w)
    (hz : Wasm.IEEE64.scaledMagnitude w ≠ 0) :
    ∃ neg t k, t % 10 ≠ 0 ∧ Shortest64 w neg t k ∧
      print64 w = words (sciLayout neg t k) ∧ print64Ecma w = words (ecmaLayout neg t k) := by
  obtain ⟨t, k, hmod, -, -, -, -, hs, hp, he⟩ :=
    PrintFloatWord.layout64 w hf (PrintFloatWord.bits_ne_zero w hz)
  exact ⟨_, t, k, hmod, hs, hp, he⟩

/-! ### Binary32 -/

theorem canon32_finite (x : UInt32) (hf : Wasm.IEEE32.isFinite x = true) : canon32 x = x := by
  have h : Wasm.IEEE32.isNaN x = false := by
    unfold Wasm.IEEE32.isNaN
    unfold Wasm.IEEE32.isFinite at hf
    rw [Bool.and_eq_false_iff]
    left
    simpa using hf
  unfold canon32
  rw [h]
  rfl

theorem zero_word32 (x : UInt32) (hz : x.toNat % 2 ^ 31 = 0) :
    withSign32 (Wasm.IEEE32.sign x) 0 = x := by
  have hx := x.toNat_lt
  apply UInt32.toNat_inj.mp
  unfold withSign32 Wasm.IEEE32.sign
  by_cases hs : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true hs, ite_eq_left rfl, ParseFloatTheorem.negate32 0 (by decide)]
    simp only [UInt32.toNat_zero]
    omega
  · rw [decide_eq_false hs, ite_eq_right Bool.false_ne_true, UInt32.toNat_zero]
    omega

theorem inf_word32 (x : UInt32) (hf : Wasm.IEEE32.isFinite x = false)
    (hn : Wasm.IEEE32.isNaN x = false) : withSign32 (Wasm.IEEE32.sign x) 0x7F800000 = x := by
  have hx := x.toNat_lt
  unfold Wasm.IEEE32.isFinite at hf
  unfold Wasm.IEEE32.isNaN at hn
  simp only [bne_eq_false_iff_eq] at hf
  rw [hf] at hn
  simp only [beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
  unfold Wasm.IEEE32.exponent at hf
  unfold Wasm.IEEE32.fraction at hn
  apply UInt32.toNat_inj.mp
  unfold withSign32 Wasm.IEEE32.sign
  by_cases hs : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true hs, ite_eq_left rfl, ParseFloatTheorem.negate32 _ (by decide)]
    rw [show (0x7F800000 : UInt32).toNat = 0x7F800000 from rfl]
    omega
  · rw [decide_eq_false hs, ite_eq_right Bool.false_ne_true,
      show (0x7F800000 : UInt32).toNat = 0x7F800000 from rfl]
    omega

theorem print32_nonfinite (ecma : Bool) (x : UInt32) (hf : Wasm.IEEE32.isFinite x = false) :
    print32With ecma x.toUInt64 = special (Wasm.IEEE32.sign x) true (Wasm.IEEE32.isNaN x) ecma := by
  have hx := x.toNat_lt
  have he := PrintFloatWord32.ef_bits x
  have hfr := PrintFloatWord32.fr_bits x
  unfold Wasm.IEEE32.isFinite Wasm.IEEE32.exponent at hf
  simp only [bne_eq_false_iff_eq] at hf
  have e7 : ((x.toUInt64 >>> 23) &&& 0xFF == 0xFF) = true := by
    rw [beq_iff_eq, ← UInt64.toNat_inj, he, show (0xFF : UInt64).toNat = 255 from rfl]
    omega
  have hn : (x.toUInt64 &&& 0x7FFFFF != 0) = Wasm.IEEE32.isNaN x := by
    unfold Wasm.IEEE32.isNaN Wasm.IEEE32.exponent Wasm.IEEE32.fraction
    rw [Bool.eq_iff_iff]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq, ← UInt64.toNat_inj, hfr,
      UInt64.toNat_zero]
    omega
  unfold print32With
  dsimp only
  rw [PrintFloatWord32.toNat_mask, PrintFloatWord32.sign_bits]
  simp only [e7, ↓reduceIte, hn]

theorem print32_zero (ecma : Bool) (x : UInt32) (hz : x.toNat % 2 ^ 31 = 0) :
    print32With ecma x.toUInt64 = special (Wasm.IEEE32.sign x) false false ecma := by
  have he := PrintFloatWord32.ef_bits x
  have hfr := PrintFloatWord32.fr_bits x
  have e7 : ((x.toUInt64 >>> 23) &&& 0xFF == 0xFF) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, he,
      show (0xFF : UInt64).toNat = 255 from rfl]
    omega
  have ez : ((x.toUInt64 >>> 23) &&& 0xFF == 0 && x.toUInt64 &&& 0x7FFFFF == 0) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, ← UInt64.toNat_inj, he, hfr, UInt64.toNat_zero]
    omega
  unfold print32With
  dsimp only
  rw [PrintFloatWord32.toNat_mask, PrintFloatWord32.sign_bits]
  simp only [e7, ez, Bool.false_eq_true, ↓reduceIte]

/-- Both printers' strings of a binary32 word, as `derives64`. -/
theorem derives32 (ecma : Bool) (x : UInt32) :
    ∃ s n, print32With ecma x.toUInt64 = words s ∧ Derives true s n ∧
      (Wasm.IEEE32.isFinite x = true → Derives false s n) ∧ round32 n = canon32 x ∧
      s.length < 2 ^ 32 ∧
      (Wasm.IEEE32.isFinite x = true → Wasm.IEEE32.scaledMagnitude x ≠ 0 →
        ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 x neg t k ∧
          s = if ecma then ecmaLayout neg t k else sciLayout neg t k) := by
  by_cases hf : Wasm.IEEE32.isFinite x = true
  · by_cases hz : x.toNat % 2 ^ 31 = 0
    · have hd := zero_derives (Wasm.IEEE32.sign x) ecma
      refine ⟨_, _, by rw [print32_zero ecma x hz, special_zero], derives_general hd,
        fun _ => hd, ?_, zero_length _ _,
        fun _ hz' => absurd hz (PrintFloatWord32.bits_ne_zero x hz')⟩
      rw [round32_zero, zero_word32 x hz, canon32_finite x hf]
    · obtain ⟨t, k, hmod, ht1, ht19, hk1, hk2, hs, hp, he⟩ := PrintFloatWord32.layout32 x hf hz
      cases ecma
      · have hd := sci_derives (Wasm.IEEE32.sign x) t k ht1
        exact ⟨_, _, hp, derives_general hd, fun _ => hd, by rw [hs.1, canon32_finite x hf],
          sci_length _ _ _ ht19 hk1 hk2, fun _ _ => ⟨_, t, k, hmod, hs, rfl⟩⟩
      · rcases ecma_derives (Wasm.IEEE32.sign x) t k ht1 with hd | ⟨z, rfl, hd⟩
        · exact ⟨_, _, he, derives_general hd, fun _ => hd, by rw [hs.1, canon32_finite x hf],
            ecma_length _ _ _ ht19 hk1 hk2, fun _ _ => ⟨_, t, k, hmod, hs, rfl⟩⟩
        · exact ⟨_, _, he, derives_general hd, fun _ => hd,
            by rw [(shortest32_shift x _ t z hs).1, canon32_finite x hf],
            ecma_length _ _ _ ht19 hk1 hk2, fun _ _ => ⟨_, t, z, hmod, hs, rfl⟩⟩
  · have hfF : Wasm.IEEE32.isFinite x = false := by simpa using hf
    by_cases hnan : Wasm.IEEE32.isNaN x = true
    · refine ⟨_, _, by rw [print32_nonfinite ecma x hfF, hnan, special_nan], nan_derives,
        fun h => absurd h hf, ?_, by decide, fun h => absurd h hf⟩
      unfold canon32
      rw [ite_eq_left hnan]
      rfl
    · have hnF : Wasm.IEEE32.isNaN x = false := by simpa using hnan
      refine ⟨_, _, by rw [print32_nonfinite ecma x hfF, hnF, special_inf], inf_derives _,
        fun h => absurd h hf, ?_, ?_, fun h => absurd h hf⟩
      · unfold canon32
        rw [hnF, ite_eq_right Bool.false_ne_true]
        exact inf_word32 x hfF hnF
      · have := sign_length (Wasm.IEEE32.sign x)
        rw [List.length_append, show (ascii "Infinity").length = 8 from rfl]
        omega

theorem print32_derives (x : UInt32) :
    ∃ s n, print32 x.toUInt64 = words s ∧ Derives true s n ∧ round32 n = canon32 x := by
  obtain ⟨s, n, h1, h2, -, h4, -, -⟩ := derives32 false x
  exact ⟨s, n, h1, h2, h4⟩

theorem print32Ecma_derives (x : UInt32) :
    ∃ s n, print32Ecma x.toUInt64 = words s ∧ Derives true s n ∧ round32 n = canon32 x := by
  obtain ⟨s, n, h1, h2, -, h4, -, -⟩ := derives32 true x
  exact ⟨s, n, h1, h2, h4⟩

theorem print32_roundtrip (x : UInt32) :
    parse32 true (print32 x.toUInt64) = (true, (canon32 x).toUInt64) := by
  obtain ⟨s, n, h1, h2, -, h4, h5, -⟩ := derives32 false x
  show parse32 true (print32With false x.toUInt64) = _
  rw [h1, parse32_accept true s n h5 h2, h4]

theorem print32Ecma_roundtrip (x : UInt32) :
    parse32 true (print32Ecma x.toUInt64) = (true, (canon32 x).toUInt64) := by
  obtain ⟨s, n, h1, h2, -, h4, h5, -⟩ := derives32 true x
  show parse32 true (print32With true x.toUInt64) = _
  rw [h1, parse32_accept true s n h5 h2, h4]

theorem print32_json (x : UInt32) (hf : Wasm.IEEE32.isFinite x) :
    (∃ s n, print32 x.toUInt64 = words s ∧ Derives false s n) ∧
      ∃ s n, print32Ecma x.toUInt64 = words s ∧ Derives false s n := by
  obtain ⟨s, n, h1, -, h3, -, -⟩ := derives32 false x
  obtain ⟨s', n', h1', -, h3', -, -⟩ := derives32 true x
  exact ⟨⟨s, n, h1, h3 hf⟩, s', n', h1', h3' hf⟩

theorem print32_shortest (x : UInt32) (hf : Wasm.IEEE32.isFinite x)
    (hz : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    ∃ s neg d e, print32 x.toUInt64 = words s ∧ Derives false s (.dec neg d e) ∧
      Shortest32 x neg d e := by
  obtain ⟨t, k, -, ht1, -, -, -, hs, hp, -⟩ :=
    PrintFloatWord32.layout32 x hf (PrintFloatWord32.bits_ne_zero x hz)
  exact ⟨_, _, _, _, hp, sci_derives _ t k ht1, hs⟩

theorem print32Ecma_shortest (x : UInt32) (hf : Wasm.IEEE32.isFinite x)
    (hz : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    ∃ s neg d e, print32Ecma x.toUInt64 = words s ∧ Derives false s (.dec neg d e) ∧
      Shortest32 x neg d e := by
  obtain ⟨t, k, -, ht1, -, -, -, hs, -, he⟩ :=
    PrintFloatWord32.layout32 x hf (PrintFloatWord32.bits_ne_zero x hz)
  rcases ecma_derives (Wasm.IEEE32.sign x) t k ht1 with hd | ⟨z, rfl, hd⟩
  · exact ⟨_, _, _, _, he, hd, hs⟩
  · exact ⟨_, _, _, _, he, hd, shortest32_shift x _ t z hs⟩

theorem print32_layout (x : UInt32) (hf : Wasm.IEEE32.isFinite x)
    (hz : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    ∃ neg t k, t % 10 ≠ 0 ∧ Shortest32 x neg t k ∧
      print32 x.toUInt64 = words (sciLayout neg t k) ∧
      print32Ecma x.toUInt64 = words (ecmaLayout neg t k) := by
  obtain ⟨t, k, hmod, -, -, -, -, hs, hp, he⟩ :=
    PrintFloatWord32.layout32 x hf (PrintFloatWord32.bits_ne_zero x hz)
  exact ⟨_, t, k, hmod, hs, hp, he⟩

#print axioms print64_derives
#print axioms print64Ecma_derives
#print axioms print64_roundtrip
#print axioms print64Ecma_roundtrip
#print axioms print64_json
#print axioms print64_shortest
#print axioms print64Ecma_shortest
#print axioms print64_layout
#print axioms print32_derives
#print axioms print32Ecma_derives
#print axioms print32_roundtrip
#print axioms print32Ecma_roundtrip
#print axioms print32_json
#print axioms print32_shortest
#print axioms print32Ecma_shortest
#print axioms print32_layout

end Verified.Examples.PrintFloatTheorem
