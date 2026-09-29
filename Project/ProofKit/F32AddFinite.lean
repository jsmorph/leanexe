import Project.ProofKit.F32Normalize

namespace Project.ProofKit.F32AddFinite
open Float.Model Float.Model.UnpackedFloat F32Normalize

def scaled (s : Sign) (m : Nat) (e : Int) : Int :=
  s.apply ((m * 2 ^ (e + 149).toNat : Nat) : Int)

def roundedSigned (z : Int) : UInt32 :=
  if z = 0 then 0 else Wasm.IEEE32.roundScaledMagnitude (decide (z < 0)) z.natAbs

theorem pack_normalize_scaled (z : Int) (e : Int) (he : -149 ≤ e) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.normalize Format.binary32 z e .positive)) =
      roundedSigned (z * ((2 ^ (e + 149).toNat : Nat) : Int)) := by
  rw [pack_normalize z e .positive he]
  have hp : (0 : Int) < ((2 ^ (e + 149).toNat : Nat) : Int) := by positivity
  have hz : z * ((2 ^ (e + 149).toNat : Nat) : Int) = 0 ↔ z = 0 := by
    simp [mul_eq_zero]
  have hn : z * ((2 ^ (e + 149).toNat : Nat) : Int) < 0 ↔ z < 0 := by
    constructor <;> intro h <;> nlinarith
  simp only [roundedSigned, hz, hn, Int.natAbs_mul, Int.natAbs_natCast,
    F32Encoding.negative, Wasm.IEEE32.signMask, Bool.false_eq_true, ite_false]

theorem decrease_scaled (m : Nat) (e t : Int) (ht : -149 ≤ t) (he : t ≤ e) :
    (decreaseExponent m e t).1 * 2 ^ (t + 149).toNat = m * 2 ^ (e + 149).toNat := by
  have hk : (e - t).toNat + (t + 149).toNat = (e + 149).toNat := by omega
  simp only [decreaseExponent, Nat.shiftLeft_eq]
  rw [Nat.mul_assoc, ← pow_add, hk]

theorem sign_apply_mul (s : Sign) (m n : Nat) :
    s.apply (m : Int) * (n : Int) = s.apply ((m * n : Nat) : Int) := by
  cases s <;> simp [Sign.apply]

theorem signed_decrease_scaled (s : Sign) (m : Nat) (e t : Int)
    (ht : -149 ≤ t) (he : t ≤ e) :
    s.apply ((decreaseExponent m e t).1 : Int) * ((2 ^ (t + 149).toNat : Nat) : Int) =
      scaled s m e := by
  rw [sign_apply_mul, decrease_scaled m e t ht he]
  rfl

theorem pack_add_finite (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (he₁ : -149 ≤ e₁) (he₂ : -149 ≤ e₂) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.add Format.binary32 (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) =
      roundedSigned (scaled s₁ m₁ e₁ + scaled s₂ m₂ e₂) := by
  have ht : -149 ≤ min e₁ e₂ := by omega
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (UnpackedFloat.normalize Format.binary32
      (s₁.apply ((decreaseExponent m₁ e₁ (min e₁ e₂)).1 : Int) +
       s₂.apply ((decreaseExponent m₂ e₂ (min e₁ e₂)).1 : Int)) (min e₁ e₂) .positive)) = _
  rw [pack_normalize_scaled _ _ ht, add_mul,
    signed_decrease_scaled s₁ m₁ e₁ _ ht (min_le_left ..),
    signed_decrease_scaled s₂ m₂ e₂ _ ht (min_le_right ..)]

#print axioms pack_add_finite

end Project.ProofKit.F32AddFinite
