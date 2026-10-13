import Verified.Examples.ParseFloatScan
import Verified.Examples.UscaleDiv

/-!
The significand's digits as the parsers read them.  The digits of a significand are the list
`L = i ++ f` of its integer and fraction digits, and the parsers read digit `k` of `L` at position
`dpos i0 ni k` of the string, past the point after the `ni` integer digits (`Reads`).  Over such a
list, `leadingZeros` counts the leading zeros, `anyNonzero` tests a range for a nonzero digit,
`chunkVal` and `hexVal` read up to 9 decimal or 15 hexadecimal digits into a word, and `digitsVal`
reads the kept digits into limbs.  `decValue_split` and its relatives give the value of a list of
digits from the values of its parts, which relates the kept digits and the sticky flag to the value
of `L`.
-/

namespace Verified.Examples.ParseFloatDigits
open ParseFloat Uscale UscaleTheorem StrconvGrammar StrconvDecode ParseFloatRound ParseFloatScan

/-! ### Values of digit lists -/

theorem decValue_append (l₁ l₂ : List UInt8) :
    decValue (l₁ ++ l₂) = decValue l₁ * 10 ^ l₂.length + decValue l₂ := by
  induction l₂ using List.reverseRecOn with
  | nil => simp [decValue]
  | append_singleton l b ih =>
    rw [← List.append_assoc, decValue_snoc, ih, decValue_snoc, List.length_append,
      List.length_singleton, pow_succ]
    ring

theorem hexValue_snoc (l : List UInt8) (b : UInt8) :
    hexValue (l ++ [b]) = 16 * hexValue l + hexDigitValue b := by
  simp [hexValue, List.foldl_append]

theorem hexValue_append (l₁ l₂ : List UInt8) :
    hexValue (l₁ ++ l₂) = hexValue l₁ * 16 ^ l₂.length + hexValue l₂ := by
  induction l₂ using List.reverseRecOn with
  | nil => simp [hexValue]
  | append_singleton l b ih =>
    rw [← List.append_assoc, hexValue_snoc, ih, hexValue_snoc, List.length_append,
      List.length_singleton, pow_succ]
    ring

theorem digit_lt (b : UInt8) (h : isDigit b = true) : b.toNat - 0x30 < 10 := by
  revert b h; apply ParseFloatScan.byte_cases; decide +kernel

theorem hexDigit_lt (b : UInt8) (h : isHexDigit b = true) : hexDigitValue b < 16 := by
  revert b h; apply ParseFloatScan.byte_cases; decide +kernel

theorem digit_zero (b : UInt8) (h : isDigit b = true) : b.toNat - 0x30 = 0 ↔ b = 0x30 := by
  revert b h; apply ParseFloatScan.byte_cases; decide +kernel

theorem hexDigit_zero (b : UInt8) (h : isHexDigit b = true) : hexDigitValue b = 0 ↔ b = 0x30 := by
  revert b h; apply ParseFloatScan.byte_cases; decide +kernel

theorem decValue_lt (l : List UInt8) (h : ∀ b ∈ l, isDigit b = true) :
    decValue l < 10 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [decValue]
  | append_singleton l b ih =>
    rw [decValue_snoc, List.length_append, List.length_singleton, pow_succ]
    have h1 := ih (fun c hc => h c (List.mem_append_left _ hc))
    have h2 := digit_lt b (h b (by simp))
    simp; omega

theorem hexValue_lt (l : List UInt8) (h : ∀ b ∈ l, isHexDigit b = true) :
    hexValue l < 16 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [hexValue]
  | append_singleton l b ih =>
    rw [hexValue_snoc, List.length_append, List.length_singleton, pow_succ]
    have h1 := ih (fun c hc => h c (List.mem_append_left _ hc))
    have h2 := hexDigit_lt b (h b (by simp))
    simp; omega

/-- A string of digits has value 0 exactly when every digit is `0`. -/
theorem decValue_eq_zero (l : List UInt8) (h : ∀ b ∈ l, isDigit b = true) :
    decValue l = 0 ↔ ∀ b ∈ l, b = 0x30 := by
  induction l using List.reverseRecOn with
  | nil => simp [decValue]
  | append_singleton l b ih =>
    rw [decValue_snoc]
    have h1 := ih (fun c hc => h c (List.mem_append_left _ hc))
    have h2 := digit_zero b (h b (by simp))
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro hz c hc
      rcases hc with hc | hc
      · exact h1.mp (by omega) c hc
      · rw [hc]; exact h2.mp (by omega)
    · intro hall
      have := h1.mpr (fun c hc => hall c (Or.inl hc))
      have := h2.mpr (hall b (Or.inr rfl))
      omega

theorem hexValue_eq_zero (l : List UInt8) (h : ∀ b ∈ l, isHexDigit b = true) :
    hexValue l = 0 ↔ ∀ b ∈ l, b = 0x30 := by
  induction l using List.reverseRecOn with
  | nil => simp [hexValue]
  | append_singleton l b ih =>
    rw [hexValue_snoc]
    have h1 := ih (fun c hc => h c (List.mem_append_left _ hc))
    have h2 := hexDigit_zero b (h b (by simp))
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro hz c hc
      rcases hc with hc | hc
      · exact h1.mp (by omega) c hc
      · rw [hc]; exact h2.mp (by omega)
    · intro hall
      have := h1.mpr (fun c hc => hall c (Or.inl hc))
      have := h2.mpr (hall b (Or.inr rfl))
      omega

/-- A string of digits with a nonzero first digit has a value of at least `10 ^ (length - 1)`. -/
theorem decValue_ge (b : UInt8) (l : List UInt8) (h : ∀ c ∈ b :: l, isDigit c = true)
    (hb : b ≠ 0x30) : 10 ^ l.length ≤ decValue (b :: l) := by
  rw [show b :: l = [b] ++ l from rfl, decValue_append]
  have : 1 ≤ decValue [b] := by
    have hd := (digit_zero b (h b (by simp))).not.mpr hb
    simp [decValue]; omega
  calc 10 ^ l.length = 1 * 10 ^ l.length := (one_mul _).symm
    _ ≤ decValue [b] * 10 ^ l.length := Nat.mul_le_mul_right _ this
    _ ≤ _ := Nat.le_add_right _ _

theorem hexValue_ge (b : UInt8) (l : List UInt8) (h : ∀ c ∈ b :: l, isHexDigit c = true)
    (hb : b ≠ 0x30) : 16 ^ l.length ≤ hexValue (b :: l) := by
  rw [show b :: l = [b] ++ l from rfl, hexValue_append]
  have : 1 ≤ hexValue [b] := by
    have hd := (hexDigit_zero b (h b (by simp))).not.mpr hb
    simp [hexValue]; omega
  calc 16 ^ l.length = 1 * 16 ^ l.length := (one_mul _).symm
    _ ≤ hexValue [b] * 16 ^ l.length := Nat.mul_le_mul_right _ this
    _ ≤ _ := Nat.le_add_right _ _

/-- Leading zeros add nothing to the value. -/
theorem decValue_zeros (l : List UInt8) (z : ℕ) (h : ∀ b ∈ l.take z, b = 0x30) :
    decValue l = decValue (l.drop z) := by
  conv_lhs => rw [← List.take_append_drop z l]
  rw [decValue_append, (decValue_eq_zero _ (fun b hb => by rw [h b hb]; decide)).mpr h, zero_mul,
    zero_add]

theorem hexValue_zeros (l : List UInt8) (z : ℕ) (h : ∀ b ∈ l.take z, b = 0x30) :
    hexValue l = hexValue (l.drop z) := by
  conv_lhs => rw [← List.take_append_drop z l]
  rw [hexValue_append, (hexValue_eq_zero _ (fun b hb => by rw [h b hb]; decide)).mpr h, zero_mul,
    zero_add]

/-! ### Positions -/

/-- The position of significand digit `k`, past the point after `ni` integer digits. -/
def dpos (i0 ni k : ℕ) : ℕ := if k < ni then i0 + k else i0 + k + 1

/-- The digits `L` lie at their positions in `s`. -/
def Reads (s : List UInt8) (i0 ni : ℕ) (L : List UInt8) : Prop :=
  ∀ k, k < L.length → byteAt s (dpos i0 ni k) = byteAt L k

theorem digitPos_toNat (i0 ni k : ℕ) (h : i0 + k + 1 < 2 ^ 63) (hni : ni < 2 ^ 63) :
    (digitPos (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat k)).toNat = dpos i0 ni k := by
  have h0 : (UInt64.ofNat i0).toNat = i0 := ofNat_toNat _ (by omega)
  have hk : (UInt64.ofNat k).toNat = k := ofNat_toNat _ (by omega)
  have hn : (UInt64.ofNat ni).toNat = ni := ofNat_toNat _ (by omega)
  unfold digitPos dpos
  by_cases hc : k < ni
  · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hk, hn]; exact hc), if_pos hc,
      toNat_add' _ _ (by rw [h0, hk]; omega), h0, hk]
  · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hk, hn]; exact hc), if_neg hc,
      toNat_add' _ _ (by rw [toNat_add' _ _ (by rw [h0, hk]; omega), h0, hk]; simp; omega),
      toNat_add' _ _ (by rw [h0, hk]; omega), h0, hk]; rfl

/-- Digit `k` of `L` read through the array. -/
theorem read_digit (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 ni : ℕ) (L : List UInt8)
    (hL : Reads s i0 ni L) (hb : i0 + L.length + 1 ≤ s.length + 1) (hni : ni ≤ s.length)
    (k : ℕ) (hk : k < L.length) :
    limb (words s) (digitPos (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat k)) =
      (byteAt L k).toUInt64 := by
  rw [limb_words s _ hs, digitPos_toNat _ _ _ (by omega) (by omega), hL k hk]

/-! ### Counting and testing -/

theorem repeat_first (n : ℕ) (hn : n < 2 ^ 62) (fuel : UInt64) (hf : n ≤ fuel.toNat)
    (Pw : UInt64 → Bool) (m : ℕ) (hm : m ≤ n)
    (hlt : ∀ z, z < m → Pw (UInt64.ofNat z) = true) (hstop : m < n → Pw (UInt64.ofNat m) = false) :
    (LeanExe.repeatWhile fuel (0 : UInt64) (fun z => decide (z < UInt64.ofNat n) && Pw z)
      (fun z => z + 1)).toNat = m := by
  have hnn : (UInt64.ofNat n).toNat = n := ofNat_toNat _ (by omega)
  unfold LeanExe.repeatWhile
  have key : ∀ f j, j ≤ m → m - j ≤ f →
      (LeanExe.repeatWhile.go (fun z => decide (z < UInt64.ofNat n) && Pw z) (fun z => z + 1) f
        (UInt64.ofNat j)).toNat = m := by
    intro f
    induction f with
    | zero => intro j h1 h2; simp only [LeanExe.repeatWhile.go]; rw [ofNat_toNat _ (by omega)]; omega
    | succ k ih =>
      intro j h1 h2
      simp only [LeanExe.repeatWhile.go]
      have hjn : (UInt64.ofNat j).toNat = j := ofNat_toNat _ (by omega)
      by_cases hj : j < m
      · have hc : (decide (UInt64.ofNat j < UInt64.ofNat n) && Pw (UInt64.ofNat j)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by rw [UInt64.lt_iff_toNat_lt, hjn, hnn]; omega, hlt j hj⟩
        rw [if_pos hc]
        have hs : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
          apply UInt64.toNat_inj.mp
          rw [toNat_add' _ _ (by rw [hjn]; simp; omega), hjn, ofNat_toNat _ (by omega)]; rfl
        rw [hs]; exact ih (j + 1) (by omega) (by omega)
      · have hje : j = m := by omega
        subst hje
        have hc : (decide (UInt64.ofNat j < UInt64.ofNat n) && Pw (UInt64.ofNat j)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases hlt' : j < n
          · right; exact hstop hlt'
          · left; rw [UInt64.lt_iff_toNat_lt, hjn, hnn]; exact hlt'
        rw [if_neg (by simp [hc])]
        exact hjn
  exact key _ 0 (Nat.zero_le _) (by omega)

theorem leadingZeros_spec (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 ni : ℕ)
    (L : List UInt8) (hL : Reads s i0 ni L) (hb : i0 + L.length + 1 ≤ s.length + 1)
    (hni : ni ≤ s.length) :
    (leadingZeros (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat L.length)).toNat =
      (L.takeWhile (· == 0x30)).length := by
  unfold leadingZeros
  have hlen : (L.takeWhile (· == 0x30)).length ≤ L.length :=
    (List.takeWhile_prefix _).length_le
  apply repeat_first L.length (by omega) _ (by rw [ofNat_toNat _ (by omega)]) _ _ hlen
  · intro z hz
    rw [read_digit s hs i0 ni L hL hb hni z (by omega)]
    have := takeWhile_get (· == 0x30) L z hz
    simp only [beq_iff_eq] at this ⊢
    rw [this]; rfl
  · intro hz
    rw [read_digit s hs i0 ni L hL hb hni _ hz]
    have := takeWhile_stop (· == 0x30) L hz
    simp only [beq_eq_false_iff_ne, ne_eq] at this ⊢
    intro h; exact this (UInt8.toUInt64_inj.mp (h.trans rfl))

theorem anyNonzero_spec (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 ni : ℕ)
    (L : List UInt8) (hL : Reads s i0 ni L) (hb : i0 + L.length + 1 ≤ s.length + 1)
    (hni : ni ≤ s.length) (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L.length) :
    anyNonzero (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat a) (UInt64.ofNat b) =
      true ↔ ∃ k, a ≤ k ∧ k < b ∧ byteAt L k ≠ 0x30 := by
  have han : (UInt64.ofNat a).toNat = a := ofNat_toNat _ (by omega)
  have hbn : (UInt64.ofNat b).toNat = b := ofNat_toNat _ (by omega)
  have hba : (UInt64.ofNat b - UInt64.ofNat a).toNat = b - a := by
    rw [toNat_sub' _ _ (by rw [han, hbn]; exact hab), han, hbn]
  unfold anyNonzero
  have hloop := loop_inv (UInt64.ofNat b - UInt64.ofNat a) false
    (fun t x => x || limb (words s) (digitPos (UInt64.ofNat i0) (UInt64.ofNat ni)
      (UInt64.ofNat a + t)) != 0x30)
    (fun t x => (x = true ↔ ∃ k, a ≤ k ∧ k < a + t ∧ byteAt L k ≠ 0x30))
    (by simp only [Bool.false_eq_true, false_iff, not_exists, not_and]; intro k h1 h2; omega)
    (by
      intro t x ht hx
      rw [hba] at ht
      have htn : (UInt64.ofNat t).toNat = t := ofNat_toNat _ (by omega)
      have hat : UInt64.ofNat a + UInt64.ofNat t = UInt64.ofNat (a + t) := by
        apply UInt64.toNat_inj.mp
        rw [toNat_add' _ _ (by rw [han, htn]; omega), han, htn, ofNat_toNat _ (by omega)]
      rw [hat, read_digit s hs i0 ni L hL hb hni _ (by omega)]
      have hne : ((byteAt L (a + t)).toUInt64 != 0x30) = true ↔ byteAt L (a + t) ≠ 0x30 := by
        rw [bne_iff_ne]
        constructor
        · intro h h'; apply h; rw [h']; rfl
        · intro h h'; exact h (UInt8.toUInt64_inj.mp (h'.trans rfl))
      rw [Bool.or_eq_true, hx, hne]
      constructor
      · rintro (⟨k, h1, h2, h3⟩ | h)
        · exact ⟨k, h1, by omega, h3⟩
        · exact ⟨a + t, by omega, by omega, h⟩
      · rintro ⟨k, h1, h2, h3⟩
        by_cases hk : k < a + t
        · exact Or.inl ⟨k, h1, hk, h3⟩
        · right; rw [show a + t = k by omega]; exact h3)
  rw [hba] at hloop
  rw [Nat.add_sub_cancel' hab] at hloop
  exact hloop

theorem chunkVal_spec (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 ni : ℕ)
    (L : List UInt8) (hL : Reads s i0 ni L) (hb : i0 + L.length + 1 ≤ s.length + 1)
    (hni : ni ≤ s.length) (hd : ∀ c ∈ L, isDigit c = true) (k len : ℕ) (hlen : len ≤ 9)
    (hkl : k + len ≤ L.length) :
    (chunkVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat k)
      (UInt64.ofNat len)).toNat = decValue ((L.drop k).take len) := by
  have hkn : (UInt64.ofNat k).toNat = k := ofNat_toNat _ (by omega)
  have hln : (UInt64.ofNat len).toNat = len := ofNat_toNat _ (by omega)
  unfold chunkVal
  have hloop := loop_inv (UInt64.ofNat len) (0 : UInt64)
    (fun t acc => 10 * acc + (limb (words s) (digitPos (UInt64.ofNat i0) (UInt64.ofNat ni)
      (UInt64.ofNat k + t)) - 0x30))
    (fun t acc => t ≤ len → acc.toNat = decValue ((L.drop k).take t))
    (by intro _; simp [decValue])
    (by
      intro t acc ht hacc ht1
      rw [hln] at ht
      have htn : (UInt64.ofNat t).toNat = t := ofNat_toNat _ (by omega)
      have hkt : UInt64.ofNat k + UInt64.ofNat t = UInt64.ofNat (k + t) := by
        apply UInt64.toNat_inj.mp
        rw [toNat_add' _ _ (by rw [hkn, htn]; omega), hkn, htn, ofNat_toNat _ (by omega)]
      rw [hkt, read_digit s hs i0 ni L hL hb hni _ (by omega)]
      have hmem : byteAt L (k + t) ∈ L := byteAt_mem L _ (by omega)
      have hdig := hd _ hmem
      have hdv := digit_val _ hdig
      have hdl := digit_lt _ hdig
      have htake : (L.drop k).take (t + 1) = (L.drop k).take t ++ [byteAt L (k + t)] := by
        rw [List.take_succ, List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
        rw [byteAt_lt _ _ (show k + t < L.length by omega)]
        simp
      have hprev := hacc (by omega)
      have hbound : decValue ((L.drop k).take t) < 10 ^ t := by
        have := decValue_lt ((L.drop k).take t) (fun c hc =>
          hd c (List.mem_of_mem_drop (List.mem_of_mem_take hc)))
        rwa [List.length_take, List.length_drop, show min t (L.length - k) = t by omega] at this
      have h10 : 10 ^ t ≤ 10 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [htake, decValue_snoc, toNat_add' _ _ (by
        rw [toNat_mul' _ _ (by rw [hprev]; simp; omega), hdv, hprev]; simp; omega),
        toNat_mul' _ _ (by rw [hprev]; simp; omega), hdv, hprev]; rfl)
  rw [hln] at hloop
  exact hloop le_rfl

theorem hexVal_spec (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 ni : ℕ)
    (L : List UInt8) (hL : Reads s i0 ni L) (hb : i0 + L.length + 1 ≤ s.length + 1)
    (hni : ni ≤ s.length) (hd : ∀ c ∈ L, isHexDigit c = true) (k len : ℕ) (hlen : len ≤ 15)
    (hkl : k + len ≤ L.length) :
    (hexVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat k)
      (UInt64.ofNat len)).toNat = hexValue ((L.drop k).take len) := by
  have hkn : (UInt64.ofNat k).toNat = k := ofNat_toNat _ (by omega)
  have hln : (UInt64.ofNat len).toNat = len := ofNat_toNat _ (by omega)
  unfold hexVal
  have hloop := loop_inv (UInt64.ofNat len) (0 : UInt64)
    (fun t acc => 16 * acc + hexValW (limb (words s) (digitPos (UInt64.ofNat i0) (UInt64.ofNat ni)
      (UInt64.ofNat k + t))))
    (fun t acc => t ≤ len → acc.toNat = hexValue ((L.drop k).take t))
    (by intro _; simp [hexValue])
    (by
      intro t acc ht hacc ht1
      rw [hln] at ht
      have htn : (UInt64.ofNat t).toNat = t := ofNat_toNat _ (by omega)
      have hkt : UInt64.ofNat k + UInt64.ofNat t = UInt64.ofNat (k + t) := by
        apply UInt64.toNat_inj.mp
        rw [toNat_add' _ _ (by rw [hkn, htn]; omega), hkn, htn, ofNat_toNat _ (by omega)]
      rw [hkt, read_digit s hs i0 ni L hL hb hni _ (by omega)]
      have hmem : byteAt L (k + t) ∈ L := byteAt_mem L _ (by omega)
      have hdig := hd _ hmem
      have hdv := hexValW_byte _ hdig
      have hdl := hexDigit_lt _ hdig
      have htake : (L.drop k).take (t + 1) = (L.drop k).take t ++ [byteAt L (k + t)] := by
        rw [List.take_succ, List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
        rw [byteAt_lt _ _ (show k + t < L.length by omega)]
        simp
      have hprev := hacc (by omega)
      have hbound : hexValue ((L.drop k).take t) < 16 ^ t := by
        have := hexValue_lt ((L.drop k).take t) (fun c hc =>
          hd c (List.mem_of_mem_drop (List.mem_of_mem_take hc)))
        rwa [List.length_take, List.length_drop, show min t (L.length - k) = t by omega] at this
      have h16 : 16 ^ t ≤ 16 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [htake, hexValue_snoc, toNat_add' _ _ (by
        rw [toNat_mul' _ _ (by rw [hprev]; simp; omega), hdv, hprev]; simp; omega),
        toNat_mul' _ _ (by rw [hprev]; simp; omega), hdv, hprev]; rfl)
  rw [hln] at hloop
  exact hloop le_rfl

theorem digitsVal_spec (s : List UInt8) (hs : s.length < 2 ^ 32) (i0 ni : ℕ)
    (L : List UInt8) (hL : Reads s i0 ni L) (hb : i0 + L.length + 1 ≤ s.length + 1)
    (hni : ni ≤ s.length) (hd : ∀ c ∈ L, isDigit c = true) (z kept : ℕ)
    (hzk : z + kept ≤ L.length) :
    Limbs (digitsVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat z)
        (UInt64.ofNat kept)) ∧
      val (digitsVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat z)
        (UInt64.ofNat kept)) = decValue ((L.drop z).take kept) ∧
      (digitsVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat z)
        (UInt64.ofNat kept)).size = (kept + 8) / 9 := by
  have hzn : (UInt64.ofNat z).toNat = z := ofNat_toNat _ (by omega)
  have hkn : (UInt64.ofNat kept).toNat = kept := ofNat_toNat _ (by omega)
  have hcount : ((UInt64.ofNat kept + 8) / 9).toNat = (kept + 8) / 9 := by
    rw [UInt64.toNat_div, toNat_add' _ _ (by rw [hkn]; simp; omega), hkn]; rfl
  unfold digitsVal
  have hloop := loop_inv ((UInt64.ofNat kept + 8) / 9) (LeanExe.build 0 fun _ => (0 : UInt64))
    (fun c acc => mulSmall acc (pow10Word (min 9 (UInt64.ofNat kept - 9 * c)))
      (chunkVal (words s) (UInt64.ofNat i0) (UInt64.ofNat ni) (UInt64.ofNat z + 9 * c)
        (min 9 (UInt64.ofNat kept - 9 * c))))
    (fun c acc => Limbs acc ∧ val acc = decValue ((L.drop z).take (min (9 * c) kept)) ∧
      acc.size = c)
    ⟨limbs_empty, by rw [val_empty]; simp [decValue], size_empty⟩
    (by
      intro c acc hc hacc
      rw [hcount] at hc
      obtain ⟨a1, a2, a3⟩ := hacc
      have hcn : (UInt64.ofNat c).toNat = c := ofNat_toNat _ (by omega)
      have h9c : 9 * c < kept := by omega
      have hm9 : (9 * UInt64.ofNat c).toNat = 9 * c := by
        rw [toNat_mul' _ _ (by rw [hcn]; simp; omega), hcn]; rfl
      set ℓ := min 9 (kept - 9 * c) with hℓ
      have hℓw : (min 9 (UInt64.ofNat kept - 9 * UInt64.ofNat c)).toNat = ℓ := by
        rw [UInt64.toNat_min, toNat_sub' _ _ (by rw [hkn, hm9]; omega), hkn, hm9]; rfl
      have hℓ1 : 1 ≤ ℓ := by omega
      have hℓ9 : ℓ ≤ 9 := by omega
      have hzc : UInt64.ofNat z + 9 * UInt64.ofNat c = UInt64.ofNat (z + 9 * c) := by
        apply UInt64.toNat_inj.mp
        rw [toNat_add' _ _ (by rw [hzn, hm9]; omega), hzn, hm9, ofNat_toNat _ (by omega)]
      have hℓeq : min 9 (UInt64.ofNat kept - 9 * UInt64.ofNat c) = UInt64.ofNat ℓ := by
        apply UInt64.toNat_inj.mp; rw [hℓw, ofNat_toNat _ (by omega)]
      rw [hzc, hℓeq]
      have hchunk := chunkVal_spec s hs i0 ni L hL hb hni hd (z + 9 * c) ℓ hℓ9 (by omega)
      have hpw := pow10Word_spec (UInt64.ofNat ℓ) (by rw [ofNat_toNat _ (by omega)]; omega)
      rw [ofNat_toNat _ (by omega)] at hpw
      have hcb : decValue ((L.drop (z + 9 * c)).take ℓ) < 10 ^ 9 := by
        have := decValue_lt ((L.drop (z + 9 * c)).take ℓ) (fun c' hc' =>
          hd c' (List.mem_of_mem_drop (List.mem_of_mem_take hc')))
        rw [List.length_take, List.length_drop, show min ℓ (L.length - (z + 9 * c)) = ℓ by omega]
          at this
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hℓ9)
      obtain ⟨b1, b2, b3⟩ := mulSmall_spec acc _ _ a1 (by omega)
        (by rw [hpw]; exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hℓ9) (by norm_num))
        (by rw [hchunk]; omega)
      refine ⟨b1, ?_, by rw [b3, a3]⟩
      rw [b2, a2, hpw, hchunk, show min (9 * (c + 1)) kept = min (9 * c) kept + ℓ by omega,
        show min (9 * c) kept = 9 * c by omega, List.take_add, decValue_append, List.drop_drop]
      congr 2
      rw [List.length_take, List.length_drop, show min ℓ (L.length - (z + 9 * c)) = ℓ by omega])
  rw [hcount] at hloop
  obtain ⟨h1, h2, h3⟩ := hloop
  refine ⟨h1, ?_, h3⟩
  rw [h2, show min (9 * ((kept + 8) / 9)) kept = kept by omega]

#print axioms leadingZeros_spec
#print axioms anyNonzero_spec
#print axioms chunkVal_spec
#print axioms hexVal_spec
#print axioms digitsVal_spec

end Verified.Examples.ParseFloatDigits
