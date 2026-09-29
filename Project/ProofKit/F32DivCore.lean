import Project.ProofKit.F32RationalNormalize

namespace Project.ProofKit.F32DivCore
open Float.Model Float.Model.UnpackedFloat F32Encoding F32RationalNormalize

def coreExponent (m₁ m₂ : Nat) (e : Int) : Int :=
  min e (Format.binary32.targetExponent ((m₁.log2 : Int) - m₂.log2 + e))

theorem coreExponent_le (m₁ m₂ : Nat) (e : Int) : coreExponent m₁ m₂ e ≤ e := min_le_left _ _

theorem core_eq (m₁ m₂ : Nat) (e₁ e₂ : Int) :
    divCore Format.binary32 m₁ e₁ m₂ e₂ =
      let t := coreExponent m₁ m₂ (e₁ - e₂)
      let n := m₁ * 2 ^ (e₁ - e₂ - t).toNat
      (n / m₂, t, accuracyOfFraction (n % m₂) m₂) := by
  have h : totalExponent m₁ e₁ - totalExponent m₂ e₂ =
      (m₁.log2 : Int) - m₂.log2 + (e₁ - e₂) := by unfold totalExponent; omega
  simp only [divCore, h, coreExponent, Nat.shiftLeft_eq]

theorem core_ready (m₁ m₂ : Nat) (e : Int) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    let t := coreExponent m₁ m₂ e
    let q := m₁ * 2 ^ (e - t).toNat / m₂
    t ≤ Format.binary32.targetExponent (totalExponent q t) := by
  let t := coreExponent m₁ m₂ e
  let k := (e - t).toNat
  change t ≤ Format.binary32.targetExponent (totalExponent (m₁ * 2 ^ k / m₂) t)
  by_cases ht : t ≤ -149
  · simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  · have hte := coreExponent_le m₁ m₂ e
    have hk : m₂.log2 + 24 ≤ m₁.log2 + k := by
      dsimp [t, coreExponent] at ht hte
      simp only [Format.targetExponent, Format.mantissaBits, Format.minExponent] at ht
      dsimp [k, t, coreExponent]
      simp only [Format.targetExponent, Format.mantissaBits, Format.minExponent]
      omega
    have hl : 2 ^ m₁.log2 ≤ m₁ := Nat.log2_self_le (by omega)
    have hu : m₂ < 2 ^ (m₂.log2 + 1) := Nat.lt_log2_self
    have hp : 2 ^ (m₂.log2 + 24) ≤ 2 ^ (m₁.log2 + k) := Nat.pow_le_pow_right (by decide) hk
    have hn : 2 ^ 23 ≤ m₁ * 2 ^ k / m₂ := by
      apply (Nat.le_div_iff_mul_le hm₂).mpr
      have hmul := Nat.mul_le_mul_right (2 ^ k) hl
      have hden := Nat.mul_le_mul_left (2 ^ 23) (Nat.le_of_lt hu)
      rw [← pow_add] at hmul hden
      rw [show 23 + (m₂.log2 + 1) = m₂.log2 + 24 by omega] at hden
      omega
    have hq : m₁ * 2 ^ k / m₂ ≠ 0 := by omega
    have hlog : 23 ≤ (m₁ * 2 ^ k / m₂).log2 := (Nat.le_log2 hq).mpr hn
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega

theorem scaled_ratio (m₁ m₂ : Nat) (e₁ e₂ t : Int) (he₁ : -149 ≤ e₁) (he₂ : -149 ≤ e₂)
    (ht : t ≤ e₁ - e₂) :
    (m₁ * 2 ^ (e₁ - e₂ - t).toNat * 2 ^ (t + 149).toNat) *
        (m₂ * 2 ^ (e₂ + 149).toNat) =
      (m₁ * 2 ^ (e₁ + 149).toNat * 2 ^ 149) * (m₂ * 2 ^ (-149 - t).toNat) := by
  have hp : (e₁ - e₂ - t).toNat + (t + 149).toNat + (e₂ + 149).toNat =
      (e₁ + 149).toNat + 149 + (-149 - t).toNat := by omega
  calc
    _ = m₁ * m₂ * 2 ^ ((e₁ - e₂ - t).toNat + (t + 149).toNat + (e₂ + 149).toNat) := by
      simp only [pow_add]
      ring
    _ = _ := by rw [hp]; simp only [pow_add]; ring

theorem pack_div_finite (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (he₁ : -149 ≤ e₁) (he₂ : -149 ≤ e₂) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.div Format.binary32 (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) =
      Wasm.IEEE32.roundRationalMagnitude (negative (s₁ / s₂))
        (m₁ * 2 ^ (e₁ + 149).toNat * 2 ^ 149) (m₂ * 2 ^ (e₂ + 149).toNat) := by
  rw [UnpackedFloat.div, core_eq]
  dsimp only
  rw [pack_roundWithAccuracy _ _ _ _ hm₂ (core_ready m₁ m₂ (e₁ - e₂) hm₁ hm₂)]
  apply rational_congr _ _ _ _ _ (by positivity) (by positivity)
  exact scaled_ratio m₁ m₂ e₁ e₂ _ he₁ he₂ (coreExponent_le m₁ m₂ (e₁ - e₂))

#print axioms core_ready
#print axioms pack_div_finite

end Project.ProofKit.F32DivCore
