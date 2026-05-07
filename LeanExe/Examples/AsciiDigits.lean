namespace LeanExe.Examples.AsciiDigits

def isAsciiDigit (b : UInt8) : Bool :=
  decide (48 <= b.toNat ∧ b.toNat <= 57)

def validate (input : ByteArray) : Bool :=
  input.toList.all isAsciiDigit

def byteAsNat (input : ByteArray) (index : Nat) : Nat :=
  (ByteArray.get! input index).toNat

def isAsciiDigitNat (n : Nat) : Bool :=
  n == 48 || n == 49 || n == 50 || n == 51 || n == 52 ||
    n == 53 || n == 54 || n == 55 || n == 56 || n == 57

def validateFuel : Nat → ByteArray → Nat → Bool
  | 0, _input, _index => false
  | fuel + 1, input, index =>
      if index == input.size || !(isAsciiDigitNat (byteAsNat input index)) then
        index == input.size
      else
        validateFuel fuel input (index + 1)

def validateGeneric (input : ByteArray) : Bool :=
  validateFuel (input.size + 1) input 0

def WellFormed (input : ByteArray) : Prop :=
  ∀ b, b ∈ input.toList → 48 <= b.toNat ∧ b.toNat <= 57

theorem isAsciiDigit_sound (b : UInt8) :
    isAsciiDigit b = true → 48 <= b.toNat ∧ b.toNat <= 57 := by
  unfold isAsciiDigit
  intro h
  exact of_decide_eq_true h

theorem isAsciiDigit_complete (b : UInt8) :
    48 <= b.toNat ∧ b.toNat <= 57 → isAsciiDigit b = true := by
  unfold isAsciiDigit
  intro h
  exact decide_eq_true h

theorem validate_sound (input : ByteArray) :
    validate input = true → WellFormed input := by
  intro h b hb
  exact isAsciiDigit_sound b ((List.all_eq_true.mp h) b hb)

theorem validate_complete (input : ByteArray) :
    WellFormed input → validate input = true := by
  intro h
  exact List.all_eq_true.mpr (fun b hb => isAsciiDigit_complete b (h b hb))

theorem validate_spec (input : ByteArray) :
    validate input = true ↔ WellFormed input :=
  ⟨validate_sound input, validate_complete input⟩

end LeanExe.Examples.AsciiDigits
