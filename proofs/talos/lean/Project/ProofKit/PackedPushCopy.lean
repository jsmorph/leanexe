import Project.ProofKit.PackedCopy

namespace Project.ProofKit.PackedMemory
open Wasm

theorem ByteArrayAt.push {mem : Mem} {base : Nat} {bytes : ByteArray}
    (hBytes : ByteArrayAt mem base bytes) (address : UInt32) (value : UInt8)
    (hAddress : address.toNat = base + bytes.size)
    (hFit : base + bytes.size + 1 ≤ 4294967296)
    (hMemory : base + bytes.size + 1 ≤ mem.pages * 65536) :
    ByteArrayAt (mem.write8 address value) base (bytes.push value) := by
  refine ⟨by simpa only [ByteArray.size_push, Nat.add_assoc, Nat.reducePow] using hFit,
    by simpa only [ByteArray.size_push, Nat.add_assoc, Mem.write8] using hMemory, ?_⟩
  intro index hIndex
  rw [ByteArray.size_push] at hIndex
  by_cases hLast : index = bytes.size
  · subst index
    simp only [Mem.write8, hAddress, ite_true, ByteArray.getElem!_push_eq]
  · rw [ByteArray.getElem!_push_lt _ _ _ (by omega)]
    simp only [Mem.write8, hAddress, ite_eq_right (show base + index ≠ base + bytes.size by omega)]
    exact hBytes.2.2 index (by omega)

end Project.ProofKit.PackedMemory

namespace Project.ProofKit.PackedCopy
open Wasm PackedMemory Memory FixedArrayCopy

def pushProgram (sourceLocal targetLocal lengthLocal valueLocal counterLocal : Nat) : Wasm.Program :=
  program sourceLocal targetLocal lengthLocal counterLocal none ++
    addressCode targetLocal lengthLocal none ++ [.localGet valueLocal, .wrapI64, .store8 0]

theorem push_spec (sourceLocal targetLocal lengthLocal valueLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target value : UInt64) (bytes : ByteArray)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hSourceNe : sourceLocal ≠ counterLocal) (hTargetNe : targetLocal ≠ counterLocal)
    (hLengthNe : lengthLocal ≠ counterLocal) (hValueNe : valueLocal ≠ counterLocal)
    (hSource : frame.get sourceLocal = some (.i64 source))
    (hTarget : frame.get targetLocal = some (.i64 target))
    (hLength : frame.get lengthLocal = some (.i64 (UInt64.ofNat bytes.size)))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hBytes : ByteArrayAt initial.mem source.toNat bytes)
    (hFit : target.toNat + bytes.size + 1 ≤ 4294967296)
    (hMemory : target.toNat + bytes.size + 1 ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + bytes.size ≤ target.toNat ∨
      target.toNat + bytes.size ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      WritesRange initial final target.toNat (target.toNat + bytes.size + 1) →
      ByteArrayAt final.mem target.toNat (bytes.push value.toUInt8) →
      wp module_ rest Q final (counterFrame frame counterLocal bytes.size hCounter) env) :
    wp module_ (pushProgram sourceLocal targetLocal lengthLocal valueLocal counterLocal ++ rest)
      Q initial frame env := by
  simp only [pushProgram, List.append_assoc]
  apply program_spec sourceLocal targetLocal lengthLocal counterLocal none module_ env initial frame
    source target 0 bytes hCounter hValues hSourceNe hTargetNe hLengthNe (by simp)
    hSource hTarget hLength rfl hBytes (by omega) (by omega) (by simpa using hSeparate)
  intro middle hWrites hCopied
  have hTargetRead := (counterFrame_get_ne frame counterLocal bytes.size targetLocal hCounter hTargetNe).trans hTarget
  have hLengthRead := (counterFrame_get_ne frame counterLocal bytes.size lengthLocal hCounter hLengthNe).trans hLength
  have hValueRead := (counterFrame_get_ne frame counterLocal bytes.size valueLocal hCounter hValueNe).trans hValue
  have hAddress := address_toNat target 0 (bytes.size + 1) bytes.size (by omega) (by omega)
  simp only [Nat.add_zero] at hAddress
  have hBound : (address target 0 bytes.size).toNat + 1 ≤ middle.mem.pages * 65536 := by
    rw [hAddress, hWrites.2.1]
    exact hMemory
  have hByte : (UInt32.ofNat (value.toNat % 2^32)).toUInt8 = value.toUInt8 := by
    simp only [Nat.reducePow]
    rw [← Memory.toUInt32_eq_ofNat, UInt64.toUInt8_toUInt32]
  apply addressCode_spec targetLocal lengthLocal none module_ env middle
    (counterFrame frame counterLocal bytes.size hCounter) target 0 bytes.size [] rfl
    hTargetRead hLengthRead rfl
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, Frame.withValues_get,
    hValueRead, wp_wrapI64_cons, wp_store8_cons, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, Nat.not_lt.mpr hBound, ite_false, hByte]
  apply hNext
  · exact (hWrites.mono (by omega) (by omega)).trans
      (write8_range middle (address target 0 bytes.size) value.toUInt8 target.toNat
        (target.toNat + bytes.size + 1) (by rw [hAddress]; omega) (by rw [hAddress]; omega))
  · exact hCopied.push (address target 0 bytes.size) value.toUInt8 (by simpa using hAddress)
      hFit (by rw [hWrites.2.1]; exact hMemory)

#print axioms push_spec
end Project.ProofKit.PackedCopy
