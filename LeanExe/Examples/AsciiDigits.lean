namespace LeanExe.Examples.AsciiDigits

def isAsciiDigit (b : UInt8) : Bool :=
  decide (48 <= b.toNat ∧ b.toNat <= 57)

def validate (input : ByteArray) : Bool :=
  input.toList.all isAsciiDigit

def byteAsNat (input : ByteArray) (index : Nat) : Nat :=
  (ByteArray.get! input index).toNat

def isAsciiDigitNat (n : Nat) : Bool :=
  if 48 <= n then
    if n <= 57 then
      true
    else
      false
  else
    false

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

def validateExpected (bytes : List UInt8) : UInt64 :=
  if bytes.all isAsciiDigit then 1 else 0

def ValidateSpec (runsTo : List UInt8 → UInt64 → Prop) : Prop :=
  ∀ bytes : List UInt8, runsTo bytes (validateExpected bytes)

def leanRunsTo (bytes : List UInt8) (output : UInt64) : Prop :=
  (if validateGeneric ⟨⟨bytes⟩⟩ then (1 : UInt64) else 0) = output

theorem isAsciiDigitNat_toNat (b : UInt8) :
    isAsciiDigitNat b.toNat = isAsciiDigit b := by
  unfold isAsciiDigitNat isAsciiDigit
  by_cases h48 : 48 ≤ b.toNat
  · by_cases h57 : b.toNat ≤ 57
    · simp [h48, h57]
    · simp [h48, h57]
  · simp [h48]

theorem validateFuel_eq (bytes : List UInt8) :
    ∀ (fuel index : Nat), index ≤ bytes.length → bytes.length - index < fuel →
      validateFuel fuel ⟨⟨bytes⟩⟩ index = (bytes.drop index).all isAsciiDigit := by
  intro fuel
  induction fuel with
  | zero =>
      intro index hle hlt
      omega
  | succ fuel ih =>
      intro index hle hlt
      have hsize : (⟨⟨bytes⟩⟩ : ByteArray).size = bytes.length := rfl
      by_cases hend : index = bytes.length
      · subst hend
        simp [validateFuel, hsize, List.drop_length]
      · have hlt' : index < bytes.length := Nat.lt_of_le_of_ne hle hend
        have hbyte : byteAsNat ⟨⟨bytes⟩⟩ index = (bytes[index]'hlt').toNat := by
          simp [byteAsNat, ByteArray.get!, hsize, List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem hlt']
        have hdrop : bytes.drop index = bytes[index]'hlt' :: bytes.drop (index + 1) :=
          List.drop_eq_getElem_cons hlt'
        by_cases hdigit : isAsciiDigit (bytes[index]'hlt') = true
        · have hnat : isAsciiDigitNat (byteAsNat ⟨⟨bytes⟩⟩ index) = true := by
            rw [hbyte, isAsciiDigitNat_toNat, hdigit]
          simp only [validateFuel, hsize, hnat, Bool.not_true, Bool.or_false,
            beq_iff_eq, hend, if_false]
          rw [ih (index + 1) hlt' (by omega), hdrop, List.all_cons, hdigit,
            Bool.true_and]
        · have hnat : isAsciiDigitNat (byteAsNat ⟨⟨bytes⟩⟩ index) = false := by
            rw [hbyte, isAsciiDigitNat_toNat]
            simpa using hdigit
          simp only [validateFuel, hsize, hnat, Bool.not_false, Bool.or_true, if_true]
          have hd0 : isAsciiDigit (bytes[index]'hlt') = false := by
            cases hval : isAsciiDigit (bytes[index]'hlt')
            · rfl
            · exact absurd hval hdigit
          rw [hdrop, List.all_cons, hd0, Bool.false_and]
          simp [hend]

theorem validateGeneric_eq_expected (bytes : List UInt8) :
    (if validateGeneric ⟨⟨bytes⟩⟩ then (1 : UInt64) else 0) = validateExpected bytes := by
  unfold validateGeneric validateExpected
  have hsize : (⟨⟨bytes⟩⟩ : ByteArray).size = bytes.length := rfl
  rw [hsize, validateFuel_eq bytes (bytes.length + 1) 0 (Nat.zero_le _) (by omega)]
  simp

theorem validateGeneric_correct : ValidateSpec leanRunsTo := by
  intro bytes
  exact validateGeneric_eq_expected bytes

end LeanExe.Examples.AsciiDigits
