import Demos.RunningSum.MagnitudePrefix

namespace Demos.RunningSum.Magnitude

def rawPrefix (digits : Array UInt64) : Nat → Nat
  | 0 => 0
  | n + 1 => rawPrefix digits n + digits[n]!.toNat * 10 ^ n

theorem rawPrefix_eq (digits : Array UInt64) (n : Nat) (hn : n ≤ digits.size) :
    rawPrefix digits n = Nat.ofDigits 10 ((digits.toList.take n).map UInt64.toNat) := by
  induction n with
  | zero => simp [rawPrefix]
  | succ n ih =>
      rw [rawPrefix, ih (by omega)]
      rw [List.take_succ_eq_append_getElem (by simpa using (show n < digits.size by omega))]
      simp [List.map_append, Nat.ofDigits_append, Nat.ofDigits,
        Nat.min_eq_left (by omega : n ≤ digits.size), getElem!_pos digits n (by omega), mul_comm]

theorem rawPrefix_size (digits : Array UInt64) : rawPrefix digits digits.size = rawValue digits := by
  rw [rawPrefix_eq digits digits.size le_rfl]
  simp only [rawValue]
  rw [List.take_of_length_le (by simp)]

theorem rawPrefix_lt (digits : Array UInt64) (valid : RawDigits digits) (n : Nat)
    (hn : n ≤ digits.size) : rawPrefix digits n < 10 ^ n := by
  induction n with
  | zero => simp [rawPrefix]
  | succ n ih =>
      have previous := ih (by omega)
      have hd := valid n (by omega)
      have hp : 0 < 10 ^ n := by positivity
      simp only [rawPrefix, pow_succ]
      nlinarith

theorem rawValue_lt (digits : Array UInt64) (valid : RawDigits digits) :
    rawValue digits < 10 ^ digits.size := by
  rw [← rawPrefix_size]
  exact rawPrefix_lt digits valid digits.size le_rfl

def trimSize (digits : Array UInt64) : Nat → Nat
  | 0 => 0
  | n + 1 => if digits[n]! == 0 then trimSize digits n else n + 1

theorem trimSize_spec (digits : Array UInt64) (size : Nat) :
    trimSize digits size ≤ size ∧ rawPrefix digits (trimSize digits size) = rawPrefix digits size ∧
      (trimSize digits size = 0 ∨ digits[trimSize digits size - 1]! ≠ 0) := by
  induction size with
  | zero => simp [trimSize]
  | succ size ih =>
      simp only [trimSize]
      split_ifs with zero
      · have byte : digits[size]! = 0 := by simpa using zero
        exact ⟨by omega, by simpa [rawPrefix, byte] using ih.2.1, ih.2.2⟩
      · exact ⟨le_rfl, rfl, Or.inr (by simpa using zero)⟩

theorem trimSize_go (digits : Array UInt64) (fuel size : Nat)
    (enough : size ≤ fuel) (bound : size < UInt64.size) :
    LeanExe.repeatWhile.go
      (fun size => size > 0 && digits[(size - 1).toNat]! == 0) (fun size => size - 1)
      fuel (UInt64.ofNat size) = UInt64.ofNat (trimSize digits size) := by
  induction fuel generalizing size with
  | zero =>
      have zero : size = 0 := by omega
      simp [zero, LeanExe.repeatWhile.go, trimSize]
  | succ fuel ih =>
      cases size with
      | zero => simp [LeanExe.repeatWhile.go, trimSize]
      | succ size =>
          have sizeNat : (UInt64.ofNat (size + 1)).toNat = size + 1 :=
            UInt64.toNat_ofNat_of_lt' bound
          have previousNat : (UInt64.ofNat size).toNat = size :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have subtract : UInt64.ofNat (size + 1) - 1 = UInt64.ofNat size := by
            apply UInt64.toNat.inj
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
                change 1 ≤ (UInt64.ofNat (size + 1)).toNat
                rw [sizeNat]
                omega)),
              sizeNat, previousNat]
            simp
          simp only [LeanExe.repeatWhile.go, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero,
            sizeNat, Nat.zero_lt_succ, decide_true, Bool.true_and, subtract, previousNat, trimSize]
          split_ifs with zero
          · exact ih size (by omega) (by omega)
          · rfl

theorem trimSize_repeat (digits : Array UInt64) (bound : digits.size < UInt64.size) :
    LeanExe.repeatWhile digits.size.toUInt64 digits.size.toUInt64
      (fun size => size > 0 && digits[(size - 1).toNat]! == 0) (fun size => size - 1) =
      (trimSize digits digits.size).toUInt64 := by
  have sizeNat : digits.size.toUInt64.toNat = digits.size := UInt64.toNat_ofNat_of_lt' bound
  simpa only [LeanExe.repeatWhile, sizeNat] using trimSize_go digits digits.size digits.size le_rfl bound

def reverseAscii (digits : Array UInt64) (size : Nat) : Array UInt64 :=
  LeanExe.build size.toUInt64 fun i => digits[(size.toUInt64 - 1 - i).toNat]! + 48

def finishDigits (digits : Array UInt64) : Array UInt64 :=
  reverseAscii digits (trimSize digits digits.size)

theorem reverseAscii_size (digits : Array UInt64) (size : Nat) (bound : size < UInt64.size) :
    (reverseAscii digits size).size = size := by
  rw [reverseAscii, LeanExe.IR.build_size]
  exact UInt64.toNat_ofNat_of_lt' bound

theorem reverseAscii_byte (digits : Array UInt64) (size i : Nat)
    (bound : size < UInt64.size) (hi : i < size) :
    (reverseAscii digits size)[i]! = digits[size - 1 - i]! + 48 := by
  unfold reverseAscii
  rw [LeanExe.IR.build_get (by simpa only [UInt64.toNat_ofNat_of_lt' bound] using hi)]
  rw [word_index size i bound hi]

theorem ascii_add (byte : UInt64) (bound : byte.toNat < 10) :
    (byte + 48).toNat = byte.toNat + 48 := by
  rw [UInt64.toNat_add]
  change (byte.toNat + 48) % 18446744073709551616 = byte.toNat + 48
  exact Nat.mod_eq_of_lt (by omega)

theorem reverseAscii_valid (digits : Array UInt64) (valid : RawDigits digits) (size : Nat)
    (hs : size ≤ digits.size) (bound : size < UInt64.size) : DecimalDigits (reverseAscii digits size) := by
  intro i hi
  rw [reverseAscii_size digits size bound] at hi
  rw [reverseAscii_byte digits size i bound hi, ascii_add _ (valid _ (by omega))]
  have := valid (size - 1 - i) (by omega)
  omega

theorem reverseAscii_digit (digits : Array UInt64) (valid : RawDigits digits) (size i : Nat)
    (hs : size ≤ digits.size) (bound : size < UInt64.size) (hi : i < size) :
    digit (reverseAscii digits size) i = digits[i]!.toNat := by
  rw [digit, reverseAscii_size digits size bound, ite_eq_left hi,
    reverseAscii_byte digits size _ bound (by omega)]
  rw [show size - 1 - (size - 1 - i) = i by omega]
  simp only [digitValue, ascii_add _ (valid i (by omega))]
  omega

theorem reverseAscii_lowValue (digits : Array UInt64) (valid : RawDigits digits) (size n : Nat)
    (hs : size ≤ digits.size) (bound : size < UInt64.size) (hn : n ≤ size) :
    lowValue (reverseAscii digits size) n = rawPrefix digits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lowValue, rawPrefix, ih (by omega), reverseAscii_digit digits valid size n hs bound (by omega)]

theorem finishDigits_spec (digits : Array UInt64) (valid : RawDigits digits)
    (bound : digits.size < UInt64.size) :
    NormalDigits (finishDigits digits) ∧ magnitude (finishDigits digits) = rawValue digits ∧
      (finishDigits digits).size ≤ digits.size := by
  obtain ⟨size, value, last⟩ := trimSize_spec digits digits.size
  have trimmedBound : trimSize digits digits.size < UInt64.size := lt_of_le_of_lt size bound
  have resultSize : (finishDigits digits).size = trimSize digits digits.size :=
    reverseAscii_size digits _ trimmedBound
  refine ⟨⟨reverseAscii_valid digits valid _ size trimmedBound, ?_⟩, ?_, by omega⟩
  · rw [resultSize]
    rcases last with zero | nonzero
    · exact Or.inl zero
    · by_cases empty : trimSize digits digits.size = 0
      · exact Or.inl empty
      · right
        change (reverseAscii digits (trimSize digits digits.size))[0]!.toNat ≠ 48
        rw [reverseAscii_byte digits _ 0 trimmedBound (by omega), Nat.sub_zero]
        rw [ascii_add _ (valid _ (by omega))]
        have byte : digits[trimSize digits digits.size - 1]!.toNat ≠ 0 := by
          exact fun same => nonzero (UInt64.toNat.inj same)
        omega
  · rw [← lowValue_size, resultSize]
    change lowValue (reverseAscii digits (trimSize digits digits.size)) (trimSize digits digits.size) = _
    rw [reverseAscii_lowValue digits valid _ _ size trimmedBound le_rfl, value, rawPrefix_size]

end Demos.RunningSum.Magnitude
