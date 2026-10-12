import Verified.Examples.FFT
import LeanExe.IR.Combinators
import Init.Data.Nat.Power2.Bitwise

namespace Verified.Examples.FFTBits

theorem isRadix2_iff (n : UInt64) :
    FFT.isRadix2 n = true ↔ ∃ p : Nat, n.toNat = 2 ^ p := by
  by_cases hn : n = 0
  · subst n
    simp only [FFT.isRadix2, bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
      UInt64.reduceToNat]
    change False ↔ Nat.isPowerOfTwo 0
    exact ⟨False.elim, Nat.not_isPowerOfTwo_zero⟩
  · have hn0 : n.toNat ≠ 0 := by
      intro h
      exact hn (UInt64.toNat_inj.mp (by simpa using h))
    have h1 : (1 : UInt64) ≤ n := UInt64.le_iff_toNat_le.mpr (by
      simp only [UInt64.reduceToNat]
      omega)
    have hand : n &&& (n - 1) = 0 ↔ n.toNat &&& (n.toNat - 1) = 0 := by
      rw [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ h1]
      simp only [UInt64.reduceToNat]
    simp only [FFT.isRadix2, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    rw [hand, Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hn0]
    exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

theorem isRadix2_iff_bounded (n : UInt64) (hn : n.toNat ≤ 2 ^ 32) :
    FFT.isRadix2 n = true ↔ ∃ p ≤ 32, n.toNat = 2 ^ p := by
  rw [isRadix2_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_, hp⟩
    by_contra h
    have hpow : (2 : Nat) ^ 32 < 2 ^ p := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  · rintro ⟨p, _, hp⟩
    exact ⟨p, hp⟩

theorem stageCount_toNat (n : UInt64) (p : Nat) (hn : n.toNat = 2 ^ p) (hp : p ≤ 32) :
    (FFT.stageCount n).toNat = p := by
  have h := LeanExe.IR.loop_induction (n := (64 : UInt64))
    (init := (n, (0 : UInt64)))
    (f := fun _ s => if s.1 > 1 then (s.1 / 2, s.2 + 1) else s)
    (P := fun k (s : UInt64 × UInt64) =>
      s.1.toNat = 2 ^ (p - min k p) ∧ s.2.toNat = min k p)
    (by simpa using hn)
    (by
      intro k s hk hs
      by_cases hkp : k < p
      · have hmin : min k p = k := Nat.min_eq_left (by omega)
        have hmin1 : min (k + 1) p = k + 1 := Nat.min_eq_left (by omega)
        have hgt : s.1 > 1 := UInt64.lt_iff_toNat_lt.mpr (by
          rw [hs.1, hmin]
          simp only [UInt64.reduceToNat]
          exact Nat.one_lt_two_pow (by omega))
        rw [ite_eq_left hgt]
        dsimp only
        constructor
        · rw [UInt64.toNat_div, hs.1, hmin, hmin1]
          simp only [UInt64.reduceToNat]
          rw [show p - k = (p - (k + 1)) + 1 by omega, pow_succ]
          exact Nat.mul_div_cancel _ (by omega)
        · rw [UInt64.toNat_add, hs.2, hmin, hmin1]
          simp only [UInt64.reduceToNat]
          apply Nat.mod_eq_of_lt
          norm_num
          omega
      · have hmin : min k p = p := Nat.min_eq_right (by omega)
        have hmin1 : min (k + 1) p = p := Nat.min_eq_right (by omega)
        have hsn : s.1.toNat = 1 := by
          rw [hs.1, hmin]
          simp
        have hnot : ¬s.1 > 1 := by
          rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hsn]
          simp only [UInt64.reduceToNat]
          omega
        rw [ite_eq_right hnot]
        simpa only [hmin, hmin1] using hs)
  have hmin : min (64 : UInt64).toNat p = p := Nat.min_eq_right (by
    simp only [UInt64.reduceToNat]
    omega)
  simpa only [FFT.stageCount, hmin] using h.2

def reverseNat (p j : Nat) : Nat :=
  Nat.fold p (fun k _ r => 2 * r + (j / 2 ^ k) % 2) 0

@[simp] theorem reverseNat_zero (j : Nat) : reverseNat 0 j = 0 := by rfl

theorem reverseNat_succ (p j : Nat) :
    reverseNat (p + 1) j = 2 * reverseNat p j + (j / 2 ^ p) % 2 := by
  simp only [reverseNat, Nat.fold_succ]

theorem reverseNat_succ_input (p j : Nat) :
    reverseNat (p + 1) j = (j % 2) * 2 ^ p + reverseNat p (j / 2) := by
  induction p with
  | zero => simp only [reverseNat_succ, reverseNat_zero, pow_zero, Nat.div_one,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero]
  | succ p ih =>
    rw [reverseNat_succ, ih, reverseNat_succ, Nat.div_div_eq_div_mul]
    rw [← pow_succ', pow_succ]
    ring

theorem reverseNat_even (p b : Nat) : reverseNat (p + 1) (2 * b) = reverseNat p b := by
  rw [reverseNat_succ_input]
  simp

theorem reverseNat_odd (p b : Nat) :
    reverseNat (p + 1) (2 * b + 1) = 2 ^ p + reverseNat p b := by
  have hm : (2 * b + 1) % 2 = 1 := by omega
  have hd : (2 * b + 1) / 2 = b := by omega
  rw [reverseNat_succ_input, hm, hd, Nat.one_mul]

theorem reverseNat_lt (p j : Nat) : reverseNat p j < 2 ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [reverseNat_succ, pow_succ]
    have hbit := Nat.mod_lt (j / 2 ^ p) (by omega : 0 < 2)
    omega

theorem reverseNat_testBit (p j i : Nat) (hi : i < p) :
    (reverseNat p j).testBit i = j.testBit (p - 1 - i) := by
  induction p generalizing i with
  | zero => omega
  | succ p ih =>
    have hbit := Nat.mod_lt (j / 2 ^ p) (by omega : 0 < 2)
    cases i with
    | zero =>
      have hm : (2 * reverseNat p j + (j / 2 ^ p) % 2) % 2 = (j / 2 ^ p) % 2 := by omega
      rw [reverseNat_succ, Nat.testBit_zero, hm]
      simpa only [Nat.add_sub_cancel, Nat.sub_zero] using
        (Nat.testBit_eq_decide_div_mod_eq (x := j) (i := p)).symm
    | succ i =>
      have hd : (2 * reverseNat p j + (j / 2 ^ p) % 2) / 2 = reverseNat p j := by omega
      rw [reverseNat_succ, Nat.testBit_succ, hd, ih i (by omega)]
      congr 1
      omega

theorem reverseNat_involutive (p j : Nat) (hj : j < 2 ^ p) :
    reverseNat p (reverseNat p j) = j := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < p
  · rw [reverseNat_testBit p _ i hi,
      reverseNat_testBit p j (p - 1 - i) (by omega)]
    congr 1
    omega
  · have hp : (2 : Nat) ^ p ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow ((reverseNat_lt p _).trans_le hp),
      Nat.testBit_lt_two_pow (hj.trans_le hp)]

theorem reverseBits_toNat (p j : UInt64) (hp : p.toNat ≤ 32) :
    (FFT.reverseBits p j).toNat = reverseNat p.toNat j.toNat := by
  have h := LeanExe.IR.loop_induction (n := p) (init := (j, (0 : UInt64)))
    (f := fun _ s => (s.1 / 2, 2 * s.2 + s.1 % 2))
    (P := fun k (s : UInt64 × UInt64) =>
      s.1.toNat = j.toNat / 2 ^ k ∧ s.2.toNat = reverseNat k j.toNat)
    (by simp)
    (by
      intro k s hk hs
      dsimp only
      constructor
      · rw [UInt64.toNat_div, hs.1]
        simp only [UInt64.reduceToNat]
        rw [Nat.div_div_eq_div_mul, ← pow_succ]
      · have hnew : 2 * reverseNat k j.toNat + (j.toNat / 2 ^ k) % 2 < 2 ^ (k + 1) := by
          rw [← reverseNat_succ]
          exact reverseNat_lt _ _
        have hpow : (2 : Nat) ^ (k + 1) ≤ 2 ^ 32 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hcap : (2 : Nat) ^ 32 < UInt64.size := by norm_num [UInt64.size]
        have hnew64 := hnew.trans_le hpow |>.trans hcap
        have hmul64 : 2 * reverseNat k j.toNat < UInt64.size := by omega
        rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, hs.1, hs.2]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt hmul64, Nat.mod_eq_of_lt hnew64, reverseNat_succ])
  simpa only [FFT.reverseBits] using h.2

theorem reverseBits_lt (p j : UInt64) (hp : p.toNat ≤ 32) :
    (FFT.reverseBits p j).toNat < 2 ^ p.toNat := by
  rw [reverseBits_toNat p j hp]
  exact reverseNat_lt _ _

theorem reverseBits_involutive (p j : UInt64) (hp : p.toNat ≤ 32)
    (hj : j.toNat < 2 ^ p.toNat) : FFT.reverseBits p (FFT.reverseBits p j) = j := by
  apply UInt64.toNat_inj.mp
  rw [reverseBits_toNat _ _ hp, reverseBits_toNat _ _ hp, reverseNat_involutive _ _ hj]

theorem reverseBits_injective (p : UInt64) (hp : p.toNat ≤ 32)
    (j k : UInt64) (hj : j.toNat < 2 ^ p.toNat) (hk : k.toNat < 2 ^ p.toNat)
    (heq : FFT.reverseBits p j = FFT.reverseBits p k) : j = k := by
  have h := congrArg (FFT.reverseBits p) heq
  rwa [reverseBits_involutive p j hp hj, reverseBits_involutive p k hp hk] at h

#print axioms isRadix2_iff
#print axioms stageCount_toNat
#print axioms reverseBits_toNat
#print axioms reverseBits_involutive

end Verified.Examples.FFTBits
