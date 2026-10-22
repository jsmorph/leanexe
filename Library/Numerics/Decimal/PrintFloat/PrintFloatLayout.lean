import Library.Numerics.Decimal.PrintFloat.PrintFloatDigits

/-!
The layouts of the printers: `sciLayoutW` and `ecmaLayoutW` write the bytes of `sciLayout` and
`ecmaLayout` (`sci_spec`, `ecma_spec`).  Both are concatenations of runs of digits and fixed bytes,
and `words` takes a concatenation of lists to the concatenation of their arrays (`words_append`), so
the proofs compare the runs one by one: `digitsFrom` writes a slice of `digitsOf t`
(`digitsFrom_spec`), `byte1` one byte, and `zeros` a run of the digit `0` (`zeros_spec`).  The
code's exponents are biased by `2 ^ 62`.
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatLayout
open PrintFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.ParseFloat.ParseFloatRound Library.Numerics.Decimal.Shared.StrconvRound Library.Numerics.Decimal.Shared.StrconvGrammar PrintFloatDigits
  Library.Numerics.Decimal.ParseFloat.ParseFloatScan

set_option exponentiation.threshold 4096

theorem words_append (a b : List UInt8) : words (a ++ b) = words a ++ words b := by
  simp [words]

/-- An array built from bytes is the array of the list of those bytes. -/
theorem build_words (n : UInt64) (f : UInt64 → UInt64) (l : List UInt8)
    (hl : l.length = n.toNat)
    (hf : ∀ i, i < n.toNat → f (UInt64.ofNat i) = (byteAt l i).toUInt64) :
    LeanExe.build n f = words l := by
  unfold LeanExe.build words
  apply Array.ext
  · simp [hl]
  · intro i h1 h2
    simp only [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map]
    simp only [Array.size_ofFn] at h1
    rw [hf i h1, byteAt_lt l i (by omega)]

theorem ofNat_add (a b : ℕ) (h : a + b < 2 ^ 64) :
    UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_add' _ _ (by rw [ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]; omega),
    ofNat_toNat _ (by omega), ofNat_toNat _ (by omega), ofNat_toNat _ h]

theorem ofNat_sub (a b : ℕ) (h : b ≤ a) (ha : a < 2 ^ 64) :
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_sub' _ _ (by rw [ofNat_toNat b (by omega), ofNat_toNat a ha]; omega),
    ofNat_toNat a ha, ofNat_toNat b (by omega), ofNat_toNat (a - b) (by omega)]

/-- `digitsFrom` writes the slice of `cnt` digits of `t` from digit `s`. -/
theorem digitsFrom_spec (t s cnt : ℕ) (s' cnt' : UInt64) (hs' : s'.toNat = s)
    (hc' : cnt'.toNat = cnt) (ht : t < 10 ^ 19) (hs : s + cnt ≤ dlen t) :
    digitsFrom (UInt64.ofNat t) (UInt64.ofNat (dlen t)) s' cnt' =
      words (((digitsOf t).drop s).take cnt) := by
  have hL := dlen_le t 19 ht (by norm_num)
  have hlen : (digitsOf t).length = dlen t := rfl
  unfold digitsFrom
  apply build_words
  · rw [hc', List.length_take, List.length_drop, hlen]
    omega
  · intro i hi
    rw [hc'] at hi
    have hsi : s' + UInt64.ofNat i = UInt64.ofNat (s + i) := by
      rw [← hs', ← ofNat_toNat s'.toNat (by omega)]
      simp only [UInt64.ofNat_toNat]
      apply UInt64.toNat_inj.mp
      rw [toNat_add' _ _ (by rw [ofNat_toNat _ (by omega)]; omega), ofNat_toNat _ (by omega),
        ofNat_toNat _ (by omega)]
    rw [hsi]
    have hb : byteAt (((digitsOf t).drop s).take cnt) i = byteAt (digitsOf t) (s + i) := by
      rw [byteAt_lt _ _ (by rw [List.length_take, List.length_drop, hlen]; omega),
        byteAt_lt _ _ (by rw [hlen]; omega)]
      simp only [List.getElem_take, List.getElem_drop]
    rw [hb, digitsOf_get t (s + i) (by omega)]
    apply UInt64.toNat_inj.mp
    rw [digitAt_spec t (dlen t) (s + i) (by omega) hL (by omega)]
    simp only [UInt8.toNat_toUInt64, dig_toNat]

theorem zeros_spec (n : ℕ) (hn : n < 2 ^ 64) :
    zeros (UInt64.ofNat n) = words (List.replicate n 0x30) := by
  unfold zeros
  apply build_words
  · rw [List.length_replicate, ofNat_toNat _ hn]
  · intro i hi
    rw [ofNat_toNat _ hn] at hi
    rw [byteAt_lt _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]
    rfl

theorem no_bytes : noBytes = words [] := by decide

theorem byte_dash : byte1 0x2D = words (ascii "-") := by decide

theorem byte_plus : byte1 0x2B = words (ascii "+") := by decide

theorem byte_point : byte1 0x2E = words (ascii ".") := by decide

theorem byte_e : byte1 0x65 = words (ascii "e") := by decide

theorem byte_zero_point : byte1 0x30 ++ byte1 0x2E = words (ascii "0.") := by decide

theorem sign_bytes (neg : Bool) :
    (if neg then byte1 0x2D else noBytes) = words (if neg then ascii "-" else []) := by
  cases neg <;> decide

/-- The number of digits of the code. -/
theorem numDigits_eq (t : ℕ) (ht : t < 10 ^ 19) :
    numDigits (UInt64.ofNat t) = UInt64.ofNat (dlen t) := by
  apply UInt64.toNat_inj.mp
  have hL := dlen_le t 19 ht (by norm_num)
  rw [numDigits_spec t ht, ofNat_toNat _ (by omega)]

/-- All the digits of `t`. -/
theorem digits_all (t : ℕ) (ht : t < 10 ^ 19) :
    digitsFrom (UInt64.ofNat t) (UInt64.ofNat (dlen t)) 0 (UInt64.ofNat (dlen t)) =
      words (digitsOf t) := by
  have hL := dlen_le t 19 ht (by norm_num)
  have h := digitsFrom_spec t 0 (dlen t) 0 (UInt64.ofNat (dlen t)) rfl
    (ofNat_toNat _ (by omega)) ht (by omega)
  rw [h, List.drop_zero,
    List.take_of_length_le (show (digitsOf t).length ≤ dlen t from le_rfl)]

/-- The digits of `t` after the first, with a point before them when there are any. -/
theorem tail_digits (t : ℕ) (ht : t < 10 ^ 19) :
    (if UInt64.ofNat (dlen t) == 1 then noBytes
      else byte1 0x2E ++ digitsFrom (UInt64.ofNat t) (UInt64.ofNat (dlen t)) 1
        (UInt64.ofNat (dlen t) - 1)) =
      words (if (digitsOf t).length = 1 then [] else ascii "." ++ (digitsOf t).drop 1) := by
  have hL := dlen_le t 19 ht (by norm_num)
  have h1 := dlen_pos t
  have hlen : (digitsOf t).length = dlen t := rfl
  by_cases hd : dlen t = 1
  · rw [ite_eq_left (by rw [hd]; decide), hlen, ite_eq_left hd, no_bytes]
  · rw [ite_eq_right (by
      rw [beq_iff_eq]; intro h; apply hd
      have := congrArg UInt64.toNat h
      rwa [ofNat_toNat _ (by omega)] at this), hlen, ite_eq_right hd, words_append, byte_point,
      digitsFrom_spec t 1 (dlen t - 1) 1 _ rfl (by
        rw [toNat_sub' _ _
            (by rw [ofNat_toNat _ (by omega)]; simp only [UInt64.reduceToNat]; omega),
          ofNat_toNat _ (by omega)]
        simp only [UInt64.reduceToNat]) ht (by omega),
      List.take_of_length_le (by rw [List.length_drop, hlen])]

/-- The first digit of `t`. -/
theorem first_digit (t : ℕ) (ht : t < 10 ^ 19) :
    digitsFrom (UInt64.ofNat t) (UInt64.ofNat (dlen t)) 0 1 = words ((digitsOf t).take 1) := by
  rw [digitsFrom_spec t 0 1 0 1 rfl rfl ht (by have := dlen_pos t; omega), List.drop_zero]

/-- The digits of the exponent `x`, through its word `xa` and its count `numDigits xa`. -/
theorem exp_digits (x : ℕ) (hx : x < 10 ^ 19) :
    digitsFrom (UInt64.ofNat x) (numDigits (UInt64.ofNat x)) 0 (numDigits (UInt64.ofNat x)) =
      words (digitsOf x) := by
  rw [numDigits_eq x hx]
  exact digits_all x hx

/-- **The scientific layout** for `1 ≤ t < 10 ^ 19` and a biased exponent `kb` within `2 ^ 20` of
`2 ^ 62`. -/
theorem sci_spec (neg : Bool) (t kb : ℕ) (ht : t < 10 ^ 19)
    (hk1 : 2 ^ 62 - 2 ^ 20 ≤ kb) (hk2 : kb ≤ 2 ^ 62 + 2 ^ 20) :
    sciLayoutW neg (UInt64.ofNat t) (UInt64.ofNat kb) =
      words (sciLayout neg t ((kb : ℤ) - 2 ^ 62)) := by
  have hL := dlen_le t 19 ht (by norm_num)
  have h1 := dlen_pos t
  have hlen : (digitsOf t).length = dlen t := rfl
  have hxb : UInt64.ofNat kb + UInt64.ofNat (dlen t) - 1 = UInt64.ofNat (kb + dlen t - 1) := by
    apply UInt64.toNat_inj.mp
    have e1 : (UInt64.ofNat kb + UInt64.ofNat (dlen t)).toNat = kb + dlen t := by
      rw [toNat_add' _ _ (by rw [ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]; omega),
        ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]
    rw [toNat_sub' _ _ (by rw [e1]; simp only [UInt64.reduceToNat]; omega), e1,
      ofNat_toNat _ (by omega)]
    simp only [UInt64.reduceToNat]
  unfold sciLayoutW sciLayout
  dsimp only
  rw [numDigits_eq t ht, hxb, hlen]
  -- the exponent of the first digit
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (kb : ℤ) - 2 ^ 62 + (dlen t : ℤ) - 1 := ⟨_, rfl⟩
  rw [← hx]
  have hxa : x.natAbs < 10 ^ 19 := by omega
  by_cases hneg : kb + dlen t - 1 < 2 ^ 62
  · have hc : decide (UInt64.ofNat (kb + dlen t - 1) < 0x4000000000000000) = true := by
      rw [decide_eq_true_iff, UInt64.lt_iff_toNat_lt, ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    have hxn : x < 0 := by omega
    have ha : (0x4000000000000000 : UInt64) - UInt64.ofNat (kb + dlen t - 1) =
        UInt64.ofNat x.natAbs := by
      apply UInt64.toNat_inj.mp
      rw [toNat_sub' _ _ (by rw [ofNat_toNat _ (by omega)]; simp only [UInt64.reduceToNat]; omega),
        ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    simp only [hc, ↓reduceIte, ha]
    rw [ite_eq_left hxn, sign_bytes, first_digit t ht, tail_digits t ht, byte_e, byte_dash,
      exp_digits _ hxa]
    simp only [words_append, hlen]
  · have hc : decide (UInt64.ofNat (kb + dlen t - 1) < 0x4000000000000000) = false := by
      rw [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    have hxn : ¬ x < 0 := by omega
    have ha : UInt64.ofNat (kb + dlen t - 1) - 0x4000000000000000 = UInt64.ofNat x.natAbs := by
      apply UInt64.toNat_inj.mp
      rw [toNat_sub' _ _ (by rw [ofNat_toNat _ (by omega)]; simp only [UInt64.reduceToNat]; omega),
        ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]
      omega
    simp only [hc, Bool.false_eq_true, ↓reduceIte, ha]
    rw [ite_eq_right hxn, sign_bytes, first_digit t ht, tail_digits t ht, byte_e, no_bytes,
      exp_digits _ hxa]
    simp only [words_append, hlen]

/-- A Boolean comparison of words below `2 ^ 63` as the comparison of their values. -/
theorem le_word (a b : ℕ) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    decide (UInt64.ofNat a ≤ UInt64.ofNat b) = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, UInt64.le_iff_toNat_le,
    ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]

theorem lt_word (a b : ℕ) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    decide (UInt64.ofNat a < UInt64.ofNat b) = decide (a < b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, UInt64.lt_iff_toNat_lt,
    ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]

/-- **The ECMAScript layout** for `1 ≤ t < 10 ^ 19` and a biased exponent `kb` within `2 ^ 20` of
`2 ^ 62`. -/
theorem ecma_spec (neg : Bool) (t kb : ℕ) (ht : t < 10 ^ 19)
    (hk1 : 2 ^ 62 - 2 ^ 20 ≤ kb) (hk2 : kb ≤ 2 ^ 62 + 2 ^ 20) :
    ecmaLayoutW neg (UInt64.ofNat t) (UInt64.ofNat kb) =
      words (ecmaLayout neg t ((kb : ℤ) - 2 ^ 62)) := by
  have hL := dlen_le t 19 ht (by norm_num)
  have h1 := dlen_pos t
  have hlen : (digitsOf t).length = dlen t := rfl
  have hnb : UInt64.ofNat kb + UInt64.ofNat (dlen t) = UInt64.ofNat (kb + dlen t) :=
    ofNat_add _ _ (by omega)
  -- the words of the code's constants
  have c0 : (0x4000000000000000 : UInt64) = UInt64.ofNat (2 ^ 62) := rfl
  have c1 : (0x4000000000000001 : UInt64) = UInt64.ofNat (2 ^ 62 + 1) := rfl
  have c21 : (0x4000000000000015 : UInt64) = UInt64.ofNat (2 ^ 62 + 21) := rfl
  have hc0d : (0x4000000000000000 : UInt64) + UInt64.ofNat (dlen t) =
      UInt64.ofNat (2 ^ 62 + dlen t) := by rw [c0, ofNat_add _ _ (by omega)]
  have hn6 : UInt64.ofNat (kb + dlen t) + 6 = UInt64.ofNat (kb + dlen t + 6) := by
    rw [show (6 : UInt64) = UInt64.ofNat 6 from rfl, ofNat_add _ _ (by omega)]
  unfold ecmaLayoutW ecmaLayout
  dsimp only
  rw [numDigits_eq t ht, hnb, hlen, hc0d, hn6]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (kb : ℤ) - 2 ^ 62 + (dlen t : ℤ) := ⟨_, rfl⟩
  rw [← hn, sign_bytes, words_append]
  congr 1
  have g1 : decide (UInt64.ofNat (kb + dlen t) ≥ UInt64.ofNat (2 ^ 62 + dlen t)) =
      decide ((dlen t : ℤ) ≤ n) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ge_iff_le, UInt64.le_iff_toNat_le,
      ofNat_toNat _ (by omega), ofNat_toNat _ (by omega)]
    omega
  have g2 : decide (UInt64.ofNat (kb + dlen t) ≤ 0x4000000000000015) = decide (n ≤ 21) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, UInt64.le_iff_toNat_le,
      ofNat_toNat _ (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have g3 : decide (UInt64.ofNat (kb + dlen t) > 0x4000000000000000) = decide (0 < n) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, gt_iff_lt, UInt64.lt_iff_toNat_lt,
      ofNat_toNat _ (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have g4 : decide (UInt64.ofNat (kb + dlen t + 6) > 0x4000000000000000) = decide (-6 < n) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, gt_iff_lt, UInt64.lt_iff_toNat_lt,
      ofNat_toNat _ (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have g5 : decide (UInt64.ofNat (kb + dlen t) ≤ 0x4000000000000000) = decide (n ≤ 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, UInt64.le_iff_toNat_le,
      ofNat_toNat _ (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have g6 : decide (UInt64.ofNat (kb + dlen t) ≥ 0x4000000000000001) = decide (0 ≤ n - 1) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ge_iff_le, UInt64.le_iff_toNat_le,
      ofNat_toNat _ (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  simp only [g1, g2, g3, g4, g5, g6]
  have hsub (hp : 0 ≤ n) : UInt64.ofNat (kb + dlen t) - 0x4000000000000000 =
      UInt64.ofNat (kb + dlen t - 2 ^ 62) := by
    rw [c0, ofNat_sub _ _ (by omega) (by omega)]
  by_cases k1 : (dlen t : ℤ) ≤ n ∧ n ≤ 21
  · -- the digits and zeros
    have b1 : (decide ((dlen t : ℤ) ≤ n) && decide (n ≤ 21)) = true := by simp [k1]
    rw [ite_eq_left b1, ite_eq_left k1, words_append, digits_all t ht]
    congr 1
    have hz : UInt64.ofNat (kb + dlen t) - 0x4000000000000000 - UInt64.ofNat (dlen t) =
        UInt64.ofNat (n - dlen t).toNat := by
      rw [hsub (by omega), ofNat_sub _ _ (by omega) (by omega)]
      exact congrArg UInt64.ofNat (by omega)
    rw [hz, zeros_spec _ (by omega)]
  have b1 : (decide ((dlen t : ℤ) ≤ n) && decide (n ≤ 21)) = false := by
    rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    exact k1 h
  rw [ite_eq_right (by rw [b1]; exact Bool.false_ne_true), ite_eq_right k1]
  by_cases k2 : 0 < n ∧ n ≤ 21
  · -- a point inside the digits
    have b2 : (decide (0 < n) && decide (n ≤ 21)) = true := by simp [k2]
    rw [ite_eq_left b2, ite_eq_left k2]
    have hnt : n.toNat < dlen t := by omega
    have hp : UInt64.ofNat (kb + dlen t) - 0x4000000000000000 = UInt64.ofNat n.toNat := by
      rw [hsub (by omega)]
      exact congrArg UInt64.ofNat (by omega)
    rw [hp, words_append, words_append, byte_point,
      digitsFrom_spec t 0 n.toNat 0 _ rfl (ofNat_toNat _ (by omega)) ht (by omega),
      digitsFrom_spec t n.toNat (dlen t - n.toNat) _ _ (ofNat_toNat _ (by omega)) (by
        rw [ofNat_sub _ _ (by omega) (by omega), ofNat_toNat _ (by omega)]) ht (by omega),
      List.drop_zero, List.take_of_length_le
        (show (List.drop n.toNat (digitsOf t)).length ≤ dlen t - n.toNat by
          rw [List.length_drop, hlen])]
  have b2 : (decide (0 < n) && decide (n ≤ 21)) = false := by
    rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    exact k2 h
  rw [ite_eq_right (by rw [b2]; exact Bool.false_ne_true), ite_eq_right k2]
  by_cases k3 : -6 < n ∧ n ≤ 0
  · -- `0.` and zeros before the digits
    have b3 : (decide (-6 < n) && decide (n ≤ 0)) = true := by simp [k3]
    rw [ite_eq_left b3, ite_eq_left k3]
    have hz : (0x4000000000000000 : UInt64) - UInt64.ofNat (kb + dlen t) =
        UInt64.ofNat (-n).toNat := by
      rw [c0, ofNat_sub _ _ (by omega) (by omega)]
      exact congrArg UInt64.ofNat (by omega)
    rw [hz, zeros_spec _ (by omega), digits_all t ht, byte_zero_point, words_append, words_append]
  have b3 : (decide (-6 < n) && decide (n ≤ 0)) = false := by
    rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    exact k3 h
  rw [ite_eq_right (by rw [b3]; exact Bool.false_ne_true), ite_eq_right k3]
  -- the exponent form
  have hxa : (n - 1).natAbs < 10 ^ 19 := by omega
  by_cases k4 : 0 ≤ n - 1
  · have ha : UInt64.ofNat (kb + dlen t) - 0x4000000000000001 = UInt64.ofNat (n - 1).natAbs := by
      rw [c1, ofNat_sub _ _ (by omega) (by omega)]
      exact congrArg UInt64.ofNat (by omega)
    have hk4 : decide (0 ≤ n - 1) = true := decide_eq_true k4
    simp only [hk4, ↓reduceIte, ha]
    rw [ite_eq_left k4, first_digit t ht, tail_digits t ht, byte_e, byte_plus, exp_digits _ hxa]
    simp only [words_append, hlen]
  · have ha : (0x4000000000000001 : UInt64) - UInt64.ofNat (kb + dlen t) =
        UInt64.ofNat (n - 1).natAbs := by
      rw [c1, ofNat_sub _ _ (by omega) (by omega)]
      exact congrArg UInt64.ofNat (by omega)
    have hk4 : decide (0 ≤ n - 1) = false := decide_eq_false k4
    simp only [hk4, Bool.false_eq_true, ↓reduceIte, ha]
    rw [ite_eq_right k4, first_digit t ht, tail_digits t ht, byte_e, byte_dash, exp_digits _ hxa]
    simp only [words_append, hlen]

#print axioms build_words
#print axioms digitsFrom_spec
#print axioms sci_spec
#print axioms ecma_spec

end Library.Numerics.Decimal.PrintFloat.PrintFloatLayout
