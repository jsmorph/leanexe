import Project.Compiler.SignedLebBits

namespace Project.Compiler.SignedLeb

theorem bit_mask (x : BitVec 64) (k : Nat) (bound : k < 64) :
    x &&& BitVec.ofNat 64 (2 ^ k) =
      if x.getLsbD k then BitVec.ofNat 64 (2 ^ k) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  cases bit : x.getLsbD k <;>
    simp only [bit, Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_and,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_zero, Nat.testBit_two_pow]
  all_goals
    by_cases same : i = k
    · subst i
      simp only [bit, bound, decide_true, Bool.false_and, Bool.true_and, Bool.and_true] <;> simp
    · simp [Ne.symm same]

theorem low_sign_bit (v : UInt64) :
    (v &&& 127) &&& 64 = if (v &&& 127).toNat < 64 then 0 else 64 := by
  apply UInt64.toBitVec_inj.mp
  change (v &&& 127).toBitVec &&& BitVec.ofNat 64 (2 ^ 6) = _
  rw [bit_mask _ 6 (by decide)]
  have low : (v &&& 127).toNat < 128 := by rw [low_bits]; simp; omega
  have bit : (v &&& 127).toBitVec.getLsbD 6 = decide (64 ≤ (v &&& 127).toNat) := by
    simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    congr 1
    apply propext
    change ((v &&& 127).toNat / 64 % 2 = 1) ↔ _
    omega
  rw [bit]
  by_cases small : (v &&& 127).toNat < 64
  · have neg : ¬ 64 ≤ (v &&& 127).toNat := by omega
    simp only [small, neg, decide_false, Bool.false_eq_true, ite_false, ite_true]
    rfl
  · have pos : 64 ≤ (v &&& 127).toNat := by omega
    simp only [small, pos, decide_true, ite_true, ite_false]
    rfl

theorem signed_eq_zero (v : UInt64) : v = 0 ↔ v.toBitVec.toInt = 0 := by
  constructor
  · intro h; subst v; rfl
  · intro h
    apply UInt64.toBitVec_inj.mp
    apply BitVec.toInt_inj.mp
    exact h

theorem signed_eq_neg_one (v : UInt64) :
    v = 18446744073709551615 ↔ v.toBitVec.toInt = -1 := by
  constructor
  · intro h; subst v; rfl
  · intro h
    apply UInt64.toBitVec_inj.mp
    apply BitVec.toInt_inj.mp
    exact h

theorem stop_correct (v : UInt64) :
    (((LeanExe.Wasm.Leb.sar7 v == 0 && (v &&& 127) &&& 64 == 0) ||
      (LeanExe.Wasm.Leb.sar7 v == 18446744073709551615 && (v &&& 127) &&& 64 == 64)) = true) ↔
      (-64 ≤ v.toBitVec.toInt ∧ v.toBitVec.toInt < 64) := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rw [signed_eq_zero (LeanExe.Wasm.Leb.sar7 v),
    signed_eq_neg_one (LeanExe.Wasm.Leb.sar7 v), sar7_signed, low_sign_bit]
  have payload := low_signed v
  split <;> simp only [show (0 : UInt64) ≠ 64 by decide,
    show (64 : UInt64) ≠ 0 by decide, and_false, false_and, or_false, false_or, eq_self, and_true, true_and] <;> omega

end Project.Compiler.SignedLeb
