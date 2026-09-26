import Project.ProofKit.QuantizedInt32
import Interpreter.Wasm.Semantics

namespace Project.ProofKit.SignedByte

theorem extend8_eq (value : UInt32) :
    LeanExe.Signed32.extend8Bits value =
      (Int32.ofInt (Wasm.signExtend (value.toNat % 256) 8)).toUInt32 := by
  apply UInt32.toNat.inj
  rw [QuantizedInt32.extend8_toNat]
  change _ = (BitVec.ofInt 32 (Wasm.signExtend (value.toNat % 256) 8)).toNat
  simp only [BitVec.toNat_ofInt, Wasm.signExtend]
  have hv : value.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  split_ifs <;> omega

#print axioms extend8_eq

end Project.ProofKit.SignedByte
