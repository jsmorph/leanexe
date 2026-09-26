import LeanExe.Wasm.Leb
import Mathlib.Tactic

namespace Project.Compiler.SignedLeb

theorem mask_msb (x : BitVec 64) :
    x &&& 9223372036854775808#64 = 0 ↔ x.msb = false := by
  constructor
  · intro h
    have hm := congrArg BitVec.msb h
    have sign : (9223372036854775808#64).msb = true := by decide
    simpa [sign] using hm
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, BitVec.getLsbD_ofNat]
    have power : (9223372036854775808 : Nat) = 2 ^ 63 := rfl
    rw [power, Nat.testBit_two_pow]
    by_cases hi : i = 63
    · subst i
      simpa [BitVec.msb_eq_getLsbD_last] using h
    · simp [Ne.symm hi]

private theorem sign_fill (x : BitVec 64) (sign : x.msb = true) :
    (x >>> 7) ||| 18374686479671623680#64 = x.sshiftRight 7 := by
  have top : x.getLsbD 63 = true := by simpa [BitVec.msb_eq_getLsbD_last] using sign
  have topElem : x[63] = true := by simpa using top
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem]
  interval_cases i <;>
    simp [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_sshiftRight,
      BitVec.getLsbD_ofNat, BitVec.getElem_sshiftRight, top, topElem, sign]

theorem sar7_bits (v : UInt64) :
    (LeanExe.Wasm.Leb.sar7 v).toBitVec = v.toBitVec.sshiftRight 7 := by
  unfold LeanExe.Wasm.Leb.sar7
  split
  · rename_i h
    have hz : v &&& 9223372036854775808 = 0 := by simpa using h
    have bits : v.toBitVec &&& 9223372036854775808#64 = 0 := congrArg UInt64.toBitVec hz
    rw [BitVec.sshiftRight_eq_of_msb_false ((mask_msb _).mp bits)]
    rfl
  · rename_i h
    have hn : v &&& 9223372036854775808 ≠ 0 := by simpa using h
    have sign : v.toBitVec.msb = true := by
      cases hs : v.toBitVec.msb
      · exact False.elim (hn (UInt64.toBitVec_inj.mp ((mask_msb _).mpr hs)))
      · rfl
    change (v.toBitVec >>> 7) ||| 18374686479671623680#64 = _
    exact sign_fill _ sign

theorem sar7_signed (v : UInt64) :
    (LeanExe.Wasm.Leb.sar7 v).toBitVec.toInt = v.toBitVec.toInt / 128 := by
  rw [sar7_bits, BitVec.toInt_sshiftRight]
  simp [Int.shiftRight_eq_div_pow]

theorem low_bits (v : UInt64) : v &&& 127 = v % 128 := by
  apply UInt64.toNat.inj
  change v.toNat &&& 127 = v.toNat % 128
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 7

theorem low_signed (v : UInt64) :
    ((v &&& 127).toNat : Int) = v.toBitVec.toInt % 128 := by
  rw [low_bits]
  simp only [UInt64.toNat_mod, UInt64.reduceToNat, BitVec.toInt_eq_toNat_cond]
  have hn : v.toBitVec.toNat = v.toNat := rfl
  simp only [hn]
  split <;> omega

end Project.Compiler.SignedLeb
