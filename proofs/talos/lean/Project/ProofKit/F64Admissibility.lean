import Project.ProofKit.F64InternalEnergy
import Project.ProofKit.F64Normalize

namespace Project.ProofKit.F64Admissibility
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Normalize
set_option exponentiation.threshold 4096

def maxWord (a b : UInt64) : UInt64 := if a < b then b else a

def topExponent (rho mx my energy : UInt64) : UInt64 :=
  maxWord (maxWord (exponentBits rho) (exponentBits mx))
    (maxWord (exponentBits my) (exponentBits energy))

theorem maxWord_toNat (a b : UInt64) : (maxWord a b).toNat = max a.toNat b.toNat := by
  unfold maxWord
  split
  · rename_i h
    exact (max_eq_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h))).symm
  · rename_i h
    have hle : b.toNat ≤ a.toNat := by rw [UInt64.lt_iff_toNat_lt] at h; omega
    exact (max_eq_left hle).symm

def normalizable (bits top : UInt64) : Bool :=
  absBits bits == 0 ||
    (decide ((0 : UInt64) < exponentBits bits) && decide (top < exponentBits bits + 1021))

def checked (rho mx my energy : UInt64) : Bool :=
  if positiveBits rho && finiteBits mx && finiteBits my && positiveBits energy then
    let top := topExponent rho mx my energy
    if normalizable rho top && normalizable mx top && normalizable my top && normalizable energy top then
      let result := F64InternalEnergy.residual
        (normalizedMagnitude rho top) (normalizedMagnitude mx top)
        (normalizedMagnitude my top) (normalizedMagnitude energy top)
      positiveBits result && decide ((0x3CE0000000000000 : UInt64) < result)
    else false
  else false

theorem finite_exponent_bound (bits : UInt64) (hf : Finite bits) :
    Wasm.IEEE64.exponent bits ≤ 2046 := by
  have hlt : Wasm.IEEE64.exponent bits < 2048 := Nat.mod_lt _ (by positivity)
  have hne : Wasm.IEEE64.exponent bits ≠ 2047 := by
    simpa only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne] using hf
  omega

theorem normalizable_spec (bits top : UInt64)
    (hf : Finite bits) (h : normalizable bits top = true) :
    absBits bits = 0 ∨
      (0 < Wasm.IEEE64.exponent bits ∧ top.toNat < Wasm.IEEE64.exponent bits + 1021) := by
  have hb := finite_exponent_bound bits hf
  have hadd : (exponentBits bits + 1021).toNat = Wasm.IEEE64.exponent bits + 1021 := by
    rw [UInt64.toNat_add, exponentBits_toNat]
    change (Wasm.IEEE64.exponent bits + 1021) % 2^64 = _
    omega
  simp only [normalizable, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true_iff,
    decide_eq_true_eq] at h
  rcases h with hz | ⟨he, ht⟩
  · exact Or.inl hz
  · right
    rw [UInt64.lt_iff_toNat_lt, exponentBits_toNat] at he
    rw [UInt64.lt_iff_toNat_lt, hadd] at ht
    exact ⟨he, ht⟩

theorem checked_sound (rho mx my energy : UInt64)
    (h : checked rho mx my energy = true) :
    Finite rho ∧ Finite mx ∧ Finite my ∧ Finite energy ∧
      0 < value rho ∧ 0 < value energy ∧
      0 < value rho * value energy - ((value mx)^2 + (value my)^2) / 2 := by
  unfold checked at h
  split at h
  · rename_i hi
    simp only [Bool.and_eq_true_iff] at hi
    obtain ⟨⟨⟨hr, hx⟩, hy⟩, he⟩ := hi
    have hr' := positiveBits_spec rho hr
    have he' := positiveBits_spec energy he
    have hx' := (finiteBits_iff mx).mp hx
    have hy' := (finiteBits_iff my).mp hy
    let top := topExponent rho mx my energy
    have ht_eq : top.toNat = max (max (Wasm.IEEE64.exponent rho) (Wasm.IEEE64.exponent mx))
        (max (Wasm.IEEE64.exponent my) (Wasm.IEEE64.exponent energy)) := by
      simp only [top, topExponent, maxWord_toNat, exponentBits_toNat]
    have ht : top.toNat ≤ 2046 := by
      rw [ht_eq]
      exact max_le (max_le (finite_exponent_bound rho hr'.1) (finite_exponent_bound mx hx'))
        (max_le (finite_exponent_bound my hy') (finite_exponent_bound energy he'.1))
    have l0 : Wasm.IEEE64.exponent rho ≤ top.toNat := by
      rw [ht_eq]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have l1 : Wasm.IEEE64.exponent mx ≤ top.toNat := by
      rw [ht_eq]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have l2 : Wasm.IEEE64.exponent my ≤ top.toNat := by
      rw [ht_eq]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have l3 : Wasm.IEEE64.exponent energy ≤ top.toNat := by
      rw [ht_eq]
      exact (le_max_right _ _).trans (le_max_right _ _)
    dsimp only at h
    split at h
    · rename_i hn
      simp only [Bool.and_eq_true_iff] at hn
      obtain ⟨⟨⟨nr, nx⟩, ny⟩, ne⟩ := hn
      have sr := normalizedMagnitude_spec rho top ht l0 (normalizable_spec rho top hr'.1 nr)
      have sx := normalizedMagnitude_spec mx top ht l1 (normalizable_spec mx top hx' nx)
      have sy := normalizedMagnitude_spec my top ht l2 (normalizable_spec my top hy' ny)
      have se := normalizedMagnitude_spec energy top ht l3 (normalizable_spec energy top he'.1 ne)
      have err := F64InternalEnergy.residual_error _ _ _ _ sr.1 sx.1 sy.1 se.1
        sr.2.1 sx.2.1 sy.2.1 se.2.1
      obtain ⟨hp, hmargin⟩ := Bool.and_eq_true_iff.mp h
      have hp' := positiveBits_spec _ hp
      have margin_pos : positiveBits 0x3CE0000000000000 = true := by decide
      have margin_value : value 0x3CE0000000000000 = 8 * arithmeticEpsilon := by
        change ((2^1025 : Nat) : ℝ) / (2 : ℝ)^1074 = 8 * (1 / (2 : ℝ)^52)
        norm_num
      let residual := F64InternalEnergy.residual
        (normalizedMagnitude rho top) (normalizedMagnitude mx top)
        (normalizedMagnitude my top) (normalizedMagnitude energy top)
      have margin := abs_value_lt 0x3CE0000000000000 residual (by
        rw [absBits_of_positive _ margin_pos, absBits_of_positive residual hp]
        exact of_decide_eq_true hmargin)
      rw [abs_of_pos (positiveBits_spec _ margin_pos).2, abs_of_pos hp'.2, margin_value] at margin
      have respos : 0 <
          value (normalizedMagnitude rho top) * value (normalizedMagnitude energy top) -
          ((value (normalizedMagnitude mx top))^2 + (value (normalizedMagnitude my top))^2) / 2 := by
        have hb := (abs_le.mp err.2).2
        have eps : 0 < arithmeticEpsilon := by norm_num [arithmeticEpsilon]
        linarith
      refine ⟨hr'.1, hx', hy', he'.1, hr'.2, he'.2, ?_⟩
      let a := (2 : ℝ)^top.toNat
      let b := (2 : ℝ)^1021
      have identity :
          (value (normalizedMagnitude rho top) * value (normalizedMagnitude energy top) -
          ((value (normalizedMagnitude mx top))^2 + (value (normalizedMagnitude my top))^2) / 2) * a^2 =
          (value rho * value energy - ((value mx)^2 + (value my)^2) / 2) * b^2 := by
        calc
          _ = (value (normalizedMagnitude rho top) * a) * (value (normalizedMagnitude energy top) * a) -
            ((value (normalizedMagnitude mx top) * a)^2 + (value (normalizedMagnitude my top) * a)^2) / 2 := by ring
          _ = (|value rho| * b) * (|value energy| * b) -
            ((|value mx| * b)^2 + (|value my| * b)^2) / 2 := by
              rw [sr.2.2, sx.2.2, sy.2.2, se.2.2]
          _ = _ := by rw [abs_of_pos hr'.2, abs_of_pos he'.2]; simp only [mul_pow, sq_abs]; ring
      have result : 0 < (value rho * value energy - ((value mx)^2 + (value my)^2) / 2) * b^2 := by
        rw [← identity]
        exact mul_pos respos (by dsimp [a]; positivity)
      exact (mul_pos_iff_of_pos_right (by dsimp [b]; positivity : 0 < b^2)).mp result
    · contradiction
  · contradiction

#print axioms checked_sound
end Project.ProofKit.F64Admissibility
