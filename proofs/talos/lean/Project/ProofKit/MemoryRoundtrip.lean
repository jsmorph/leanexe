import Project.ProofKit.Memory

namespace Project.ProofKit.Memory
open Wasm

theorem read64_write64 (mem : Mem) (address : UInt32) (value : UInt64) :
    (mem.write64 address value).read64 address = value := by
  simp only [Mem.read64, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, reduceIte,
    Nat.reduceEqDiff]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_and, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  interval_cases bit <;> simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']

#print axioms read64_write64

end Project.ProofKit.Memory
