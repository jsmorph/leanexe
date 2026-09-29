import Project.Encoding.Spec.Values
import Init.Omega
import Init.Data.UInt.Lemmas

namespace Wasm.Encoding

def unsignedFuel : Nat → Nat → Spec.Bytes
  | 0, _ => []
  | fuel + 1, value =>
      if value < 128 then [UInt8.ofNat value]
      else UInt8.ofNat (value % 128 + 128) :: unsignedFuel fuel (value / 128)

def unsigned (width value : Nat) : Spec.Bytes :=
  unsignedFuel ((width + 6) / 7) value

def signedFuel : Nat → Int → Spec.Bytes
  | 0, _ => []
  | fuel + 1, value =>
      if -64 ≤ value ∧ value < 64 then [UInt8.ofNat (value % 128).toNat]
      else UInt8.ofNat ((value % 128).toNat + 128) :: signedFuel fuel (value / 128)

def signed (width : Nat) (value : Int) : Spec.Bytes :=
  signedFuel ((width + 6) / 7) value

theorem unsignedFuel_correct (fuel width value : Nat)
    (positive : 0 < width) (room : width ≤ 7 * fuel)
    (fits : value < 2 ^ width) :
    Spec.Unsigned width (unsignedFuel fuel value) value := by
  induction fuel generalizing width value with
  | zero => omega
  | succ fuel ih =>
      simp only [unsignedFuel]
      by_cases small : value < 128
      · rw [ite_eq_left small]
        have byte : (UInt8.ofNat value).toNat = value := by
          simp only [UInt8.toNat_ofNat']
          omega
        simpa only [byte] using Spec.Unsigned.terminal width (UInt8.ofNat value)
          positive (by omega) (by omega)
      · rw [ite_eq_right small]
        have wide : 7 < width := by
          by_cases narrow : width ≤ 7
          · have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2) narrow
            omega
          · omega
        have power : 2 ^ width = 128 * 2 ^ (width - 7) := by
          calc
            2 ^ width = 2 ^ (7 + (width - 7)) := by congr 1; omega
            _ = 128 * 2 ^ (width - 7) := by rw [Nat.pow_add]
        have divided : value / 128 < 2 ^ (width - 7) := by
          rw [power] at fits
          omega
        have byte : (UInt8.ofNat (value % 128 + 128)).toNat = value % 128 + 128 := by
          simp only [UInt8.toNat_ofNat']
          omega
        have tail := ih (width - 7) (value / 128) (by omega) (by omega) divided
        have result := Spec.Unsigned.next (width - 7)
          (UInt8.ofNat (value % 128 + 128)) _ _ (by omega) (by omega) tail
        have same : value % 128 + 128 - 128 + 128 * (value / 128) = value := by omega
        simpa only [byte, same, show width - 7 + 7 = width by omega] using result

theorem unsigned_correct (width value : Nat)
    (positive : 0 < width) (fits : value < 2 ^ width) :
    Spec.Unsigned width (unsigned width value) value :=
  unsignedFuel_correct _ _ _ positive (by omega) fits

theorem signedPayload (value : Int) (small : -64 ≤ value ∧ value < 64) :
    Spec.signedDigit (UInt8.ofNat (value % 128).toNat) = value := by
  have payload : (value % 128).toNat < 128 := by omega
  have byte : (UInt8.ofNat (value % 128).toNat).toNat = (value % 128).toNat := by
    simp only [UInt8.toNat_ofNat']
    omega
  simp only [Spec.signedDigit, byte]
  split <;> omega

theorem signedFuel_correct (fuel width : Nat) (value : Int)
    (positive : 0 < width) (room : width ≤ 7 * fuel)
    (lower : -(2 ^ (width - 1) : Int) ≤ value)
    (upper : value < (2 ^ (width - 1) : Int)) :
    Spec.Signed width (signedFuel fuel value) value := by
  induction fuel generalizing width value with
  | zero => omega
  | succ fuel ih =>
      simp only [signedFuel]
      by_cases small : -64 ≤ value ∧ value < 64
      · rw [ite_eq_left small]
        have byte : (UInt8.ofNat (value % 128).toNat).toNat = (value % 128).toNat := by
          simp only [UInt8.toNat_ofNat']
          omega
        simpa only [signedPayload value small] using
          Spec.Signed.terminal width (UInt8.ofNat (value % 128).toNat) positive
            (by rw [byte]; omega)
            (by rw [signedPayload value small]; exact lower)
            (by rw [signedPayload value small]; exact upper)
      · rw [ite_eq_right small]
        have wide : 7 < width := by
          by_cases narrow : width ≤ 7
          · have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
              (by omega : width - 1 ≤ 6)
            have castPower : (2 ^ (width - 1) : Int) = (2 ^ (width - 1) : Nat) := by
              simp
            rw [castPower] at lower upper
            omega
          · omega
        have power : (2 ^ (width - 1) : Int) = 128 * 2 ^ (width - 7 - 1) := by
          rw [show width - 1 = 7 + (width - 7 - 1) by omega, Int.pow_add]
          rfl
        have dividedLower : -(2 ^ (width - 7 - 1) : Int) ≤ value / 128 := by
          rw [power] at lower
          omega
        have dividedUpper : value / 128 < (2 ^ (width - 7 - 1) : Int) := by
          rw [power] at upper
          omega
        have byte : (UInt8.ofNat ((value % 128).toNat + 128)).toNat =
            (value % 128).toNat + 128 := by
          simp only [UInt8.toNat_ofNat']
          omega
        have tail := ih (width - 7) (value / 128) (by omega) (by omega)
          dividedLower dividedUpper
        have result := Spec.Signed.next (width - 7)
          (UInt8.ofNat ((value % 128).toNat + 128)) _ _ (by omega) (by omega) tail
        have same : (((value % 128).toNat + 128 : Nat) : Int) - 128 +
            128 * (value / 128) = value := by omega
        simpa only [byte, same, show width - 7 + 7 = width by omega] using result

theorem signed_correct (width : Nat) (value : Int)
    (positive : 0 < width)
    (lower : -(2 ^ (width - 1) : Int) ≤ value)
    (upper : value < (2 ^ (width - 1) : Int)) :
    Spec.Signed width (signed width value) value :=
  signedFuel_correct _ _ _ positive (by omega) lower upper

end Wasm.Encoding
