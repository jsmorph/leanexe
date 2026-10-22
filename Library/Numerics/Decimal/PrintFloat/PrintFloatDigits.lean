import Library.Numerics.Decimal.PrintFloat.Compiled
import Library.Numerics.Decimal.PrintFloat.PrintFloatShort
import Library.Numerics.Decimal.ParseFloat.ParseFloatScan
import Library.Numerics.Arithmetic.Uscale.UscaleDiv

/-!
The decimal digits of the printers.  `Library.Numerics.Decimal.Shared.StrconvRound.digitsOf n` has `dlen n` digits, digit `i`
being the byte `n / 10 ^ (dlen n - 1 - i) % 10 + 48` (`digitsOf_get`), with `dlen n` the number of
digits of `n` for `n ≥ 1` and 1 for 0.  The code's `numDigits` and `digitAt` compute the same
(`numDigits_spec`, `digitAt_spec`), and `decValue` reads the digits back as `n`
(`decValue_digitsOf`).
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatDigits
open PrintFloat Library.Numerics.Arithmetic.Uscale.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.ParseFloat.ParseFloatRound Library.Numerics.Decimal.Shared.StrconvRound Library.Numerics.Decimal.Shared.StrconvGrammar PrintFloatShort
  ParseFloatScan

set_option exponentiation.threshold 4096

theorem digitChar_byte (d : ℕ) (hd : d < 10) :
    (Nat.digitChar d).toUInt8 = UInt8.ofNat (d + 48) := by
  interval_cases d <;> rfl

/-- The number of decimal digits that `digitsOf` writes. -/
def dlen (n : ℕ) : ℕ := (digitsOf n).length

/-- Digit `i` of `n`, most significant first, as an ASCII byte. -/
def dig (n L i : ℕ) : UInt8 := UInt8.ofNat (n / 10 ^ (L - 1 - i) % 10 + 48)

theorem digitsOf_small (n : ℕ) (hn : n < 10) : digitsOf n = [UInt8.ofNat (n + 48)] := by
  unfold digitsOf
  rw [Nat.toDigits_eq_ite (by norm_num), ite_eq_left hn]
  simp [digitChar_byte n hn]

theorem digitsOf_big (n : ℕ) (hn : 10 ≤ n) :
    digitsOf n = digitsOf (n / 10) ++ [UInt8.ofNat (n % 10 + 48)] := by
  unfold digitsOf
  rw [Nat.toDigits_eq_ite (by norm_num), ite_eq_right (by omega)]
  simp [digitChar_byte (n % 10) (Nat.mod_lt _ (by norm_num))]

theorem dlen_eq (n : ℕ) : dlen n = if n < 10 then 1 else dlen (n / 10) + 1 := by
  unfold dlen
  split_ifs with h
  · rw [digitsOf_small n h]; rfl
  · rw [digitsOf_big n (by omega), List.length_append]; rfl

theorem digitsOf_eq (n : ℕ) :
    digitsOf n = (List.range (dlen n)).map (fun i => dig n (dlen n) i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · rw [dlen_eq, ite_eq_left h, digitsOf_small n h]
      simp [dig, Nat.mod_eq_of_lt h]
    · have hn := ih (n / 10) (by omega)
      rw [digitsOf_big n (by omega), hn, dlen_eq n, ite_eq_right h, List.range_succ,
        List.map_append]
      congr 1
      · apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        unfold dig
        rw [show dlen (n / 10) + 1 - 1 - i = (dlen (n / 10) - 1 - i) + 1 by omega, pow_succ',
          ← Nat.div_div_eq_div_mul]
      · simp [dig]

theorem dlen_pos (n : ℕ) : 1 ≤ dlen n := by
  rw [dlen_eq]; split_ifs <;> omega

/-- `dlen` is the number of digits of `Nat.digits` for `n ≥ 1`. -/
theorem dlen_nd (n : ℕ) (hn : 1 ≤ n) : dlen n = nd n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [dlen_eq]
    split_ifs with h
    · exact (nd_one n hn (by omega)).symm
    · rw [ih (n / 10) (by omega) (by omega)]
      unfold nd
      rw [Nat.digits_def' (by norm_num) (show 0 < n by omega), List.length_cons]

theorem lt_pow_dlen (n : ℕ) : n < 10 ^ dlen n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; positivity
  · rw [dlen_nd n h]; exact lt_pow_nd n

theorem pow_dlen_le (n : ℕ) (hn : 1 ≤ n) : 10 ^ (dlen n - 1) ≤ n := by
  rw [dlen_nd n hn]; exact pow_nd_le n (by omega)

theorem dlen_le (n k : ℕ) (h : n < 10 ^ k) (hk : 1 ≤ k) : dlen n ≤ k := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; rw [dlen_eq]; simp; omega
  · rw [dlen_nd n h0]; exact nd_le n k h (by omega)

theorem digitsOf_get (n i : ℕ) (hi : i < dlen n) : byteAt (digitsOf n) i = dig n (dlen n) i := by
  rw [byteAt_lt _ _ (by unfold dlen at hi; exact hi)]
  have := digitsOf_eq n
  simp only [this, List.getElem_map, List.getElem_range]

theorem dig_toNat (n L i : ℕ) : (dig n L i).toNat = n / 10 ^ (L - 1 - i) % 10 + 48 := by
  unfold dig
  have h := Nat.mod_lt (n / 10 ^ (L - 1 - i)) (show 0 < 10 by norm_num)
  have hlt : n / 10 ^ (L - 1 - i) % 10 + 48 < UInt8.size := by
    rw [show UInt8.size = 256 from rfl]; omega
  rw [UInt8.toNat_ofNat_of_lt' hlt]

/-- `decValue` reads the digits back. -/
theorem decValue_digitsOf (n : ℕ) : decValue (digitsOf n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · rw [digitsOf_small n h]
      simp [decValue]
      omega
    · rw [digitsOf_big n (by omega), Library.Numerics.Decimal.ParseFloat.ParseFloatScan.decValue_snoc, ih (n / 10) (by omega)]
      have h10 := Nat.mod_lt n (show 0 < 10 by norm_num)
      have hlt : n % 10 + 48 < UInt8.size := by rw [show UInt8.size = 256 from rfl]; omega
      rw [UInt8.toNat_ofNat_of_lt' hlt]
      omega

/-- Every digit is an ASCII digit. -/
theorem digitsOf_digits (n : ℕ) : ∀ b ∈ digitsOf n, isDigit b = true := by
  rw [digitsOf_eq]
  intro b hb
  simp only [List.mem_map, List.mem_range] at hb
  obtain ⟨i, _, rfl⟩ := hb
  have h := Nat.mod_lt (n / 10 ^ (dlen n - 1 - i)) (show 0 < 10 by norm_num)
  unfold dig isDigit
  generalize n / 10 ^ (dlen n - 1 - i) % 10 = d at h
  interval_cases d <;> decide

/-- The first digit of a positive number is not zero. -/
theorem digitsOf_head (n : ℕ) (hn : 1 ≤ n) : byteAt (digitsOf n) 0 ≠ 0x30 := by
  rw [digitsOf_get n 0 (by have := dlen_pos n; omega)]
  have h1 := pow_dlen_le n hn
  have h2 := lt_pow_dlen n
  have hq : 1 ≤ n / 10 ^ (dlen n - 1 - 0) ∧ n / 10 ^ (dlen n - 1 - 0) < 10 := by
    rw [Nat.sub_zero]
    constructor
    · exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ']
      rw [show dlen n - 1 + 1 = dlen n by have := dlen_pos n; omega]; exact h2
  intro h
  have := congrArg UInt8.toNat h
  rw [dig_toNat, Nat.mod_eq_of_lt hq.2] at this
  simp at this; omega

/-! ### The code's digits -/

theorem numDigits_spec (n : ℕ) (hn : n < 10 ^ 19) :
    (numDigits (UInt64.ofNat n)).toNat = dlen n := by
  have hnn : (UInt64.ofNat n).toNat = n := ofNat_toNat _ (by omega)
  have hL1 := dlen_pos n
  have hL2 : dlen n ≤ 19 := dlen_le n 19 hn (by norm_num)
  unfold numDigits LeanExe.repeatWhile
  have key : ∀ f k, 1 ≤ k → k ≤ dlen n → dlen n - k ≤ f →
      (LeanExe.repeatWhile.go (fun k => decide (k < 19) && decide (pow10Word k ≤ UInt64.ofNat n))
        (fun k => k + 1) f (UInt64.ofNat k)).toNat = dlen n := by
    intro f
    induction f with
    | zero =>
      intro k h1 h2 h3
      simp only [LeanExe.repeatWhile.go]
      rw [ofNat_toNat _ (by omega)]
      omega
    | succ f ih =>
      intro k h1 h2 h3
      simp only [LeanExe.repeatWhile.go]
      have hk : (UInt64.ofNat k).toNat = k := ofNat_toNat _ (by omega)
      by_cases hlt : k < dlen n
      · have hc : (decide (UInt64.ofNat k < 19) &&
            decide (pow10Word (UInt64.ofNat k) ≤ UInt64.ofNat n)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨by rw [UInt64.lt_iff_toNat_lt, hk]; simp; omega, ?_⟩
          rw [UInt64.le_iff_toNat_le, pow10Word_spec _ (by rw [hk]; omega), hk, hnn]
          have := pow_dlen_le n (by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · subst h0; rw [dlen_eq] at hlt; simp at hlt; omega
            · exact h0)
          exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) this
        rw [ite_eq_left hc]
        have hs : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat_inj.mp
          rw [toNat_add' _ _ (by rw [hk]; simp; omega), hk, ofNat_toNat _ (by omega)]; rfl
        rw [hs]; exact ih (k + 1) (by omega) (by omega) (by omega)
      · have hke : k = dlen n := by omega
        have hc : ¬ (decide (UInt64.ofNat k < 19) &&
            decide (pow10Word (UInt64.ofNat k) ≤ UInt64.ofNat n)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
          intro h19
          have h19' : k < 19 := by rw [UInt64.lt_iff_toNat_lt, hk] at h19; simpa using h19
          rw [UInt64.le_iff_toNat_le, pow10Word_spec _ (by rw [hk]; omega), hk, hnn, hke]
          have := lt_pow_dlen n
          omega
        rw [ite_eq_right hc, hk, hke]
  exact key 19 1 le_rfl hL1 (by omega)

theorem digitAt_spec (n L i : ℕ) (hn : n < 2 ^ 64) (hL : L ≤ 19) (hi : i < L) :
    (digitAt (UInt64.ofNat n) (UInt64.ofNat L) (UInt64.ofNat i)).toNat =
      n / 10 ^ (L - 1 - i) % 10 + 48 := by
  have hnn : (UInt64.ofNat n).toNat = n := ofNat_toNat _ hn
  have hLn : (UInt64.ofNat L).toNat = L := ofNat_toNat _ (by omega)
  have hin : (UInt64.ofNat i).toNat = i := ofNat_toNat _ (by omega)
  have he : (UInt64.ofNat L - 1 - UInt64.ofNat i).toNat = L - 1 - i := by
    rw [toNat_sub' _ _ (by rw [toNat_sub' _ _ (by rw [hLn]; simp; omega), hLn, hin]; simp; omega),
      toNat_sub' _ _ (by rw [hLn]; simp; omega), hLn, hin]; simp
  unfold digitAt
  have hp := pow10Word_spec (UInt64.ofNat L - 1 - UInt64.ofNat i) (by rw [he]; omega)
  rw [he] at hp
  have hq : n / 10 ^ (L - 1 - i) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  rw [toNat_add' _ _ (by rw [UInt64.toNat_mod, UInt64.toNat_div, hp, hnn]; simp; omega),
    UInt64.toNat_mod, UInt64.toNat_div, hp, hnn]
  rfl

#print axioms digitsOf_eq
#print axioms dlen_nd
#print axioms decValue_digitsOf
#print axioms numDigits_spec
#print axioms digitAt_spec

end Library.Numerics.Decimal.PrintFloat.PrintFloatDigits
