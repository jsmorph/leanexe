import Project.ProofKit.F32Normalize
import Project.ProofKit.QuantizedInt32

namespace Project.ProofKit.F32Convert
open Float.Model Float.Model.UnpackedFloat

theorem ofInt_eq (value : Int) :
    (Float32.Model.ofInt value).toBits = Wasm.IEEE32.fromInt value := by
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (UnpackedFloat.normalize Format.binary32 value 0 .positive)) = _
  rw [F32Normalize.pack_normalize value 0 .positive (by omega)]
  by_cases hz : value = 0
  · subst value
    decide
  · simp only [hz, ite_false, Wasm.IEEE32.fromInt]
    rfl

theorem ofInt32Bits_eq (value : UInt32) :
    LeanExe.Float32.ofInt32Bits value = Wasm.IEEE32.convertI32S value := by
  change (Float32.Model.ofInt (Int32.ofUInt32 value).toInt).toBits = _
  rw [ofInt_eq, ← QuantizedInt32.decode_toInt, QuantizedInt32.decode_talos]
  rfl

#print axioms ofInt_eq
#print axioms ofInt32Bits_eq

end Project.ProofKit.F32Convert
