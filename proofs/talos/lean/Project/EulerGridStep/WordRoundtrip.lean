import Project.ProofKit.Array
import Mathlib.Tactic.IntervalCases

namespace Project.EulerGridStep.Execution
open Wasm
set_option maxHeartbeats 1000000

/-- Kernel-checked reconstruction of the eight stored bytes, without a native decision axiom. -/
theorem read64_write64_exact (mem : Mem) (address : UInt32) (value : UInt64) :
    (mem.write64 address value).read64 address = value := by
  simp only [Mem.read64, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, reduceIte, Nat.reduceEqDiff]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
    UInt64.toBitVec_ofNat]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index hIndex
  interval_cases index <;> simp

#print axioms read64_write64_exact
end Project.EulerGridStep.Execution
