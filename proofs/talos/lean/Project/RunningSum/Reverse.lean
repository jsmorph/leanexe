import Project.RunningSum.Normalize

namespace Project.RunningSum

def Canonical (bytes : ByteArray) : Prop :=
  AsciiDigits bytes ∧ (bytes.size = 0 ∨ 48 < bytes[0]!.toNat)

theorem rawPrefix_lt (bytes : ByteArray) (h : RawDigits bytes) (n : Nat)
    (hn : n ≤ bytes.size) : rawPrefix bytes n < 10 ^ n := by
  induction n with
  | zero => simp [rawPrefix]
  | succ n ih =>
    have hp := ih (by omega)
    have hd := h n (by omega)
    have hpow : 0 < 10 ^ n := by positivity
    simp only [rawPrefix, pow_succ]
    nlinarith

theorem rawValue_lt (bytes : ByteArray) (h : RawDigits bytes) :
    rawValue bytes < 10 ^ bytes.size := by
  rw [← rawPrefix_size]
  exact rawPrefix_lt bytes h bytes.size (by omega)

def reversePrefix (bytes : ByteArray) (size n : Nat) : ByteArray :=
  (List.range n).foldl (fun result i => result.push (bytes[size - 1 - i]! + 48)) ByteArray.empty

theorem reversePrefix_succ (bytes : ByteArray) (size n : Nat) :
    reversePrefix bytes size (n + 1) =
      (reversePrefix bytes size n).push (bytes[size - 1 - n]! + 48) := by
  simp [reversePrefix, List.range_succ]

@[simp] theorem reversePrefix_size (bytes : ByteArray) (size n : Nat) :
    (reversePrefix bytes size n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [reversePrefix_succ, ByteArray.size_push, ih]

theorem reversePrefix_byte (bytes : ByteArray) (size n i : Nat) (hi : i < n) :
    (reversePrefix bytes size n)[i]! = bytes[size - 1 - i]! + 48 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [reversePrefix_succ, ByteArray.getElem!_push, reversePrefix_size]
    split_ifs with heq
    · simp [heq]
    · exact ih (by omega)

@[simp] theorem reverseAscii_size (bytes : ByteArray) (size : Nat) :
    (reverseAscii bytes size).size = size := reversePrefix_size bytes size size

theorem reverseAscii_byte (bytes : ByteArray) (size i : Nat) (hi : i < size) :
    (reverseAscii bytes size)[i]! = bytes[size - 1 - i]! + 48 :=
  reversePrefix_byte bytes size size i hi

theorem ascii_add (byte : UInt8) (h : byte.toNat < 10) :
    (byte + 48).toNat = byte.toNat + 48 := by
  simp only [UInt8.toNat_add, UInt8.toNat_ofNat]
  norm_num
  omega

theorem reverseAscii_valid (bytes : ByteArray) (h : RawDigits bytes) (size : Nat)
    (hs : size ≤ bytes.size) : AsciiDigits (reverseAscii bytes size) := by
  intro i hi
  simp only [reverseAscii_size] at hi
  rw [reverseAscii_byte bytes size i hi, ascii_add _ (h _ (by omega))]
  have := h (size - 1 - i) (by omega)
  omega

theorem reverseAscii_digit (bytes : ByteArray) (h : RawDigits bytes) (size i : Nat)
    (hs : size ≤ bytes.size) (hi : i < size) :
    digit (reverseAscii bytes size) i = bytes[i]!.toNat := by
  rw [digit, reverseAscii_size, ite_eq_left hi, reverseAscii_byte bytes size _ (by omega)]
  rw [show size - 1 - (size - 1 - i) = i by omega, ascii_add _ (h i (by omega))]
  omega

theorem reverseAscii_lowValue (bytes : ByteArray) (h : RawDigits bytes) (size n : Nat)
    (hs : size ≤ bytes.size) (hn : n ≤ size) :
    lowValue (reverseAscii bytes size) n = rawPrefix bytes n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lowValue, rawPrefix, ih (by omega), reverseAscii_digit bytes h size n hs (by omega)]

theorem finishDigits_spec (bytes : ByteArray) (h : RawDigits bytes) :
    Canonical (finishDigits bytes) ∧ magnitude (finishDigits bytes) = rawValue bytes := by
  obtain ⟨hsize, hvalue, hlast⟩ := trimSize_spec bytes bytes.size
  refine ⟨⟨reverseAscii_valid bytes h _ hsize, ?_⟩, ?_⟩
  · simp only [finishDigits, reverseAscii_size]
    rcases hlast with hzero | hnonzero
    · exact Or.inl hzero
    · by_cases hs : trimSize bytes bytes.size = 0
      · exact Or.inl hs
      · right
        rw [reverseAscii_byte bytes _ 0 (by omega), Nat.sub_zero]
        have hb := h (trimSize bytes bytes.size - 1) (by omega)
        rw [ascii_add _ hb]
        have hnat : bytes[trimSize bytes bytes.size - 1]!.toNat ≠ 0 := by
          exact fun he => hnonzero (UInt8.toNat.inj he)
        omega
  · simp only [magnitude, finishDigits, reverseAscii_size]
    rw [reverseAscii_lowValue bytes h _ _ hsize (by omega), hvalue, rawPrefix_size]

#print axioms finishDigits_spec

end Project.RunningSum
