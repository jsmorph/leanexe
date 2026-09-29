import Project.ProofKit.F32SqrtRounding
import Project.ProofKit.F32Shift

namespace Project.ProofKit.F32SqrtCore
open Float.Model Float.Model.UnpackedFloat F32SqrtRounding

def coreExponent (m : Nat) (e : Int) : Int := ((m.log2 : Int) + e + 2) / 2 - 24

theorem coreExponent_bounds (m : Nat) (e : Int) (hl : m.log2 ≤ 23) (he : -149 ≤ e) :
    -149 ≤ coreExponent m e ∧ 2 * coreExponent m e ≤ e ∧
      46 ≤ m.log2 + (e - 2 * coreExponent m e).toNat ∧
      m.log2 + (e - 2 * coreExponent m e).toNat ≤ 47 := by
  unfold coreExponent
  omega

theorem core_eq (m : Nat) (e : Int) (hl : m.log2 ≤ 23) (he : -149 ≤ e) :
    sqrtCore Format.binary32 m e =
      let t := coreExponent m e
      let n := m * 2 ^ (e - 2 * t).toNat
      (n.sqrt, t, rootAccuracy n) := by
  have ht : min (e.ediv 2) (Format.binary32.targetExponent ((totalExponent m e + 1).ediv 2)) =
      coreExponent m e := by
    change min (e / 2) (Format.binary32.targetExponent ((totalExponent m e + 1) / 2)) = _
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent,
      coreExponent]
    omega
  simp only [sqrtCore, ht, Nat.shiftLeft_eq, rootAccuracy]

theorem root_log (m : Nat) (e : Int) (hm : m ≠ 0) (hl : m.log2 ≤ 23) (he : -149 ≤ e) :
    (m * 2 ^ (e - 2 * coreExponent m e).toNat).sqrt.log2 = 23 := by
  obtain ⟨_, _, hlo, hhi⟩ := coreExponent_bounds m e hl he
  let n := m * 2 ^ (e - 2 * coreExponent m e).toNat
  have hn : n ≠ 0 := by dsimp [n]; positivity
  have hlog : n.log2 = m.log2 + (e - 2 * coreExponent m e).toNat :=
    F32Shift.log2_mul_pow m _ hm
  have hnl : 2 ^ 46 ≤ n := (Nat.le_log2 hn).mp (by omega)
  have hnu : n < 2 ^ 48 := (Nat.log2_lt hn).mp (by omega)
  have hrl : 2 ^ 23 ≤ n.sqrt := Nat.le_sqrt.mpr (by norm_num at hnl ⊢; exact hnl)
  have hru : n.sqrt < 2 ^ 24 := Nat.sqrt_lt.mpr (by norm_num at hnu ⊢; exact hnu)
  exact (Nat.log2_eq_iff (show n.sqrt ≠ 0 by omega)).mpr ⟨hrl, hru⟩

theorem radicand_scaled (m : Nat) (e : Int) (hl : m.log2 ≤ 23) (he : -149 ≤ e) :
    (m * 2 ^ (e - 2 * coreExponent m e).toNat) * 2 ^ (2 * (coreExponent m e + 149).toNat) =
      (m * 2 ^ (e + 149).toNat) * 2 ^ 149 := by
  obtain ⟨ht, hte, _, _⟩ := coreExponent_bounds m e hl he
  rw [Nat.mul_assoc, ← pow_add, Nat.mul_assoc, ← pow_add]
  congr 2
  omega

theorem scaled_root_log (n k : Nat) (hn : n ≠ 0) (hl : n.sqrt.log2 = 23) :
    (n * 2 ^ (2 * k)).sqrt.log2 = 23 + k := by
  have hr : n.sqrt ≠ 0 := fun h => hn (Nat.sqrt_eq_zero.mp h)
  have ⟨hlo, hhi⟩ := (Nat.log2_eq_iff hr).mp hl
  have hlo' := Nat.le_sqrt.mp hlo
  have hhi' := Nat.sqrt_lt.mp hhi
  have hrl : 2 ^ (23 + k) ≤ (n * 2 ^ (2 * k)).sqrt := by
    apply Nat.le_sqrt.mpr
    have h := Nat.mul_le_mul_right (2 ^ (2 * k)) hlo'
    convert h using 1
    ring_nf
  have hru : (n * 2 ^ (2 * k)).sqrt < 2 ^ (23 + k + 1) := by
    apply Nat.sqrt_lt.mpr
    have h := Nat.mul_lt_mul_of_pos_right hhi' (by positivity : 0 < 2 ^ (2 * k))
    convert h using 1
    ring_nf
  exact (Nat.log2_eq_iff (by have := Nat.two_pow_pos (23 + k); omega)).mpr ⟨hrl, hru⟩

#print axioms root_log
#print axioms scaled_root_log

end Project.ProofKit.F32SqrtCore
