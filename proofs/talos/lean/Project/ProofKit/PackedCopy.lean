import Project.ProofKit.PackedCopyAddress
import Project.ProofKit.PackedGenerateLoop

namespace Project.ProofKit.PackedCopy
open Wasm Project.ProofKit.PackedMemory Memory FixedArrayCopy

def body (sourceLocal targetLocal lengthLocal counterLocal : Nat) (offsetLocal : Option Nat) : Wasm.Program :=
  [.localGet counterLocal, .localGet lengthLocal, .geUI64, .br_if 1] ++
    addressCode targetLocal counterLocal offsetLocal ++ addressCode sourceLocal counterLocal none ++
    [.load8U 0, .store8 0, .localGet counterLocal, .constI64 1, .addI64, .localSet counterLocal, .br 0]

def program (sourceLocal targetLocal lengthLocal counterLocal : Nat) (offsetLocal : Option Nat) : Wasm.Program :=
  [.constI64 0, .localSet counterLocal,
    .block 0 0 [.loop 0 0 (body sourceLocal targetLocal lengthLocal counterLocal offsetLocal)]]

theorem write8_range (store : Store Unit) (pointer : UInt32) (value : UInt8) (start stop : Nat)
    (hStart : start ≤ pointer.toNat) (hStop : pointer.toNat < stop) :
    WritesRange store { store with mem := store.mem.write8 pointer value } start stop := by
  refine ⟨rfl, rfl, ?_⟩
  intro index hOutside
  simp only [Mem.write8, ite_eq_right (show index ≠ pointer.toNat by omega)]

theorem program_spec (sourceLocal targetLocal lengthLocal counterLocal : Nat) (offsetLocal : Option Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (offset : Nat) (bytes : ByteArray)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hSourceNe : sourceLocal ≠ counterLocal) (hTargetNe : targetLocal ≠ counterLocal)
    (hLengthNe : lengthLocal ≠ counterLocal) (hOffsetNe : ∀ index, offsetLocal = some index → index ≠ counterLocal)
    (hSource : frame.get sourceLocal = some (.i64 source))
    (hTarget : frame.get targetLocal = some (.i64 target))
    (hLength : frame.get lengthLocal = some (.i64 (UInt64.ofNat bytes.size)))
    (hOffset : CopyAddress.OffsetAt frame offsetLocal offset)
    (hBytes : ByteArrayAt initial.mem source.toNat bytes)
    (hFit : target.toNat + offset + bytes.size ≤ 4294967296)
    (hMemory : target.toNat + offset + bytes.size ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + bytes.size ≤ target.toNat + offset ∨
      target.toNat + offset + bytes.size ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      WritesRange initial final (target.toNat + offset) (target.toNat + offset + bytes.size) →
      ByteArrayAt final.mem (target.toNat + offset) bytes →
      wp module_ rest Q final (counterFrame frame counterLocal bytes.size hCounter) env) :
    wp module_ (program sourceLocal targetLocal lengthLocal counterLocal offsetLocal ++ rest) Q initial frame env := by
  let Inv : AssertionF Unit := fun current next => ∃ index, index ≤ bytes.size ∧
    next = counterFrame frame counterLocal index hCounter ∧
    WritesRange initial current (target.toNat + offset) (target.toNat + offset + bytes.size) ∧
    ∀ i, i < index → current.mem.bytes (target.toNat + offset + i) = bytes[i]!
  have hSize : bytes.size < UInt64.size := by change bytes.size < 18446744073709551616; omega
  simp only [program, List.cons_append, List.nil_append]
  apply initializeCounter_spec hCounter hValues
  apply wp_block_cons
  apply wp_loop_cons (Inv := Inv) (μ := PackedGenerateLoop.measure counterLocal bytes.size)
  · exact ⟨0, Nat.zero_le _, rfl, WritesRange.refl .., by omega⟩
  · rintro current next ⟨index, hIndex, rfl, hWrites, hCopied⟩
    have hIndex64 : index < UInt64.size := hIndex.trans_lt hSize
    have hIndexNat := UInt64.toNat_ofNat_of_lt' hIndex64
    have hLengthRead := (counterFrame_get_ne frame counterLocal index lengthLocal hCounter hLengthNe).trans hLength
    have hSourceRead := (counterFrame_get_ne frame counterLocal index sourceLocal hCounter hSourceNe).trans hSource
    have hTargetRead := (counterFrame_get_ne frame counterLocal index targetLocal hCounter hTargetNe).trans hTarget
    have hOffsetRead : CopyAddress.OffsetAt (counterFrame frame counterLocal index hCounter) offsetLocal offset := by
      cases offsetLocal with
      | none => exact hOffset
      | some local_ => exact (counterFrame_get_ne _ _ _ _ hCounter (hOffsetNe local_ rfl)).trans hOffset
    simp only [body, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, counterFrame_get_counter, counterFrame_values,
      hLengthRead, wp_geUI64_cons, wp_br_if_cons]
    by_cases hLast : index = bytes.size
    · subst index
      rw [ite_eq_left (show UInt64.ofNat bytes.size ≥ UInt64.ofNat bytes.size by simp)]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      exact hNext current hWrites ⟨hFit, by rw [hWrites.2.1]; exact hMemory, hCopied⟩
    · have hLess : index < bytes.size := by omega
      have hGuard : ¬ UInt64.ofNat bytes.size ≤ UInt64.ofNat index := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hSize, hIndexNat]
        omega
      rw [ite_eq_right hGuard]
      apply addressCode_spec targetLocal counterLocal offsetLocal module_ env current
        (counterFrame frame counterLocal index hCounter) target offset index [] rfl hTargetRead
        (counterFrame_get_counter ..) hOffsetRead
      apply addressCode_spec sourceLocal counterLocal none module_ env current
        { counterFrame frame counterLocal index hCounter with values := [.i32 (address target offset index)] }
        source 0 index [.i32 (address target offset index)] rfl hSourceRead (counterFrame_get_counter ..) rfl
      have hSourceAddress := address_toNat source 0 bytes.size index (by simpa using hBytes.1) hLess
      have hTargetAddress := address_toNat target offset bytes.size index hFit hLess
      have hSourceBound : (address source 0 index).toNat + 1 ≤ current.mem.pages * 65536 := by
        rw [hSourceAddress, hWrites.2.1]
        have := hBytes.2.1
        omega
      have hTargetBound : (address target offset index).toNat + 1 ≤ current.mem.pages * 65536 := by
        rw [hTargetAddress, hWrites.2.1]
        omega
      have hRead : current.mem.read8 (address source 0 index) = bytes[index]! := by
        rw [Mem.read8, hSourceAddress, Nat.add_zero]
        exact (hBytes.writesRange hWrites hSeparate).2.2 index hLess
      have hSucc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
      simp only [wp_load8U_cons, wp_store8_cons, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
        Nat.not_lt.mpr hSourceBound, Nat.not_lt.mpr hTargetBound, ite_false, hRead,
        UInt8.toUInt8_toUInt32, wp_localGet_cons, Frame.withValues_get, counterFrame_get_counter,
        wp_constI64_cons, wp_addI64_cons, hSucc, wp_localSet_cons, counterFrame_withValues_set?_counter,
        wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · refine ⟨index + 1, by omega, rfl, ?_, ?_⟩
        · exact hWrites.trans (write8_range _ _ _ _ _ (by rw [hTargetAddress]; omega)
            (by rw [hTargetAddress]; omega))
        · intro i hi
          by_cases hSame : i = index
          · subst i
            simp only [Mem.write8, hTargetAddress, ite_true]
          · simp only [Mem.write8, hTargetAddress, ite_eq_right (show target.toNat + offset + i ≠
                target.toNat + offset + index by omega)]
            exact hCopied i (by omega)
      · change PackedGenerateLoop.measure counterLocal bytes.size _
            (counterFrame frame counterLocal (index + 1) hCounter) <
          PackedGenerateLoop.measure counterLocal bytes.size current (counterFrame frame counterLocal index hCounter)
        simp only [PackedGenerateLoop.measure, counterFrame_get_counter,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega), hIndexNat]
        omega

#print axioms program_spec

end Project.ProofKit.PackedCopy
