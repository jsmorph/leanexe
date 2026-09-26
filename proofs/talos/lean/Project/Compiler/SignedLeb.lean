import Project.Compiler.SignedLebStop
import Project.Compiler.SignedLebTrace
import Project.Compiler.ByteLists

namespace Project.Compiler.SignedLeb

theorem native_payload (v : UInt64) :
    (v &&& 127).toNat = payload v.toBitVec.toInt := by
  have h := congrArg Int.toNat (low_signed v)
  simpa [payload] using h

theorem native_low_byte (v : UInt64) :
    (v &&& 127).toUInt8 = UInt8.ofNat (payload v.toBitVec.toInt) := by
  apply UInt8.toNat.inj
  simp only [UInt64.toNat_toUInt8, native_payload]
  rfl

theorem native_high_byte (v : UInt64) :
    ((v &&& 127) + 128).toUInt8 = UInt8.ofNat (payload v.toBitVec.toInt + 128) := by
  apply UInt8.toNat.inj
  have bound := payload_bound v.toBitVec.toInt
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_add, native_payload,
    UInt64.reduceToNat]
  change ((payload v.toBitVec.toInt + 128) % 2 ^ 64) % 256 =
    (payload v.toBitVec.toInt + 128) % 256
  omega

theorem native_bytes (fuel : Nat) (v : UInt64) (out : ByteArray) :
    (LeanExe.Wasm.Leb.s64lebFuel fuel v out).data.toList =
      out.data.toList ++ bytes fuel v.toBitVec.toInt := by
  induction fuel generalizing v out with
  | zero => simp [LeanExe.Wasm.Leb.s64lebFuel, bytes]
  | succ fuel ih =>
    simp only [LeanExe.Wasm.Leb.s64lebFuel, bytes]
    simp only [stop_correct]
    split
    · rename_i h
      simp only [h, ite_true, ByteArray.push, Array.toList_push, native_low_byte]
    · rename_i h
      simp only [h, ite_false, ih, ByteArray.push, Array.toList_push,
        native_high_byte, sar7_signed, List.append_assoc, List.singleton_append]

/-- The actual signed encoder satisfies the independent binary grammar for
every i64 bit pattern, with its two's-complement signed interpretation. -/
theorem s64 (v : UInt64) :
    Wasm.Binary.Grammar.S64 (LeanExe.Wasm.Leb.s64lebU64 v).toList v.toBitVec.toInt := by
  rw [byteArray_toList]
  simp only [LeanExe.Wasm.Leb.s64lebU64, native_bytes, ByteArray.empty,
    List.nil_append, Array.toList_empty]
  have h := trace 10 64 0 0 v.toBitVec.toInt (by decide) (by decide)
    (BitVec.le_toInt _) BitVec.toInt_lt
  refine ⟨h.length_le, h.continuationForm,
    Wasm.Binary.Leb.Proof.signedTerminalFitsFrom_zero h.terminalFitsFrom, ?_⟩
  rw [← Wasm.Binary.Leb.Proof.signedValueFrom_zero]
  simpa using h.valueFrom.symm

end Project.Compiler.SignedLeb
