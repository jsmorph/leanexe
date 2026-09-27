import Project.ProofKit.PackedCopy

namespace Project.ProofKit.PackedMemory
open Wasm

theorem ByteArrayAt.append {mem : Mem} {base : Nat} {left right : ByteArray}
    (hLeft : ByteArrayAt mem base left) (hRight : ByteArrayAt mem (base + left.size) right) :
    ByteArrayAt mem base (left ++ right) := by
  refine ⟨by simpa only [ByteArray.size_append, Nat.add_assoc] using hRight.1,
    by simpa only [ByteArray.size_append, Nat.add_assoc] using hRight.2.1, ?_⟩
  intro index hIndex
  by_cases hBefore : index < left.size
  · rw [getElem!_pos (left ++ right) index hIndex, ByteArray.getElem_append_left hBefore,
      ← getElem!_pos left index hBefore]
    exact hLeft.2.2 index hBefore
  · have hAfter : index - left.size < right.size := by rw [ByteArray.size_append] at hIndex; omega
    rw [getElem!_pos (left ++ right) index hIndex, ByteArray.getElem_append_right (by omega),
      ← getElem!_pos right (index - left.size) hAfter]
    have hAddress : base + index = base + left.size + (index - left.size) := by omega
    rw [hAddress]
    exact hRight.2.2 _ hAfter

end Project.ProofKit.PackedMemory

namespace Project.ProofKit.PackedCopy
open Wasm PackedMemory Memory FixedArrayCopy

theorem append_spec (leftLocal rightLocal targetLocal leftLengthLocal rightLengthLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (leftPtr rightPtr target : UInt64) (left right : ByteArray)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hLeftNe : leftLocal ≠ counterLocal) (hRightNe : rightLocal ≠ counterLocal)
    (hTargetNe : targetLocal ≠ counterLocal) (hLeftLengthNe : leftLengthLocal ≠ counterLocal)
    (hRightLengthNe : rightLengthLocal ≠ counterLocal)
    (hLeft : frame.get leftLocal = some (.i64 leftPtr))
    (hRight : frame.get rightLocal = some (.i64 rightPtr))
    (hTarget : frame.get targetLocal = some (.i64 target))
    (hLeftLength : frame.get leftLengthLocal = some (.i64 (UInt64.ofNat left.size)))
    (hRightLength : frame.get rightLengthLocal = some (.i64 (UInt64.ofNat right.size)))
    (hLeftBytes : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRightBytes : ByteArrayAt initial.mem rightPtr.toNat right)
    (hFit : target.toNat + (left.size + right.size) ≤ 4294967296)
    (hMemory : target.toNat + (left.size + right.size) ≤ initial.mem.pages * 65536)
    (hSeparateLeft : leftPtr.toNat + left.size ≤ target.toNat ∨
      target.toNat + (left.size + right.size) ≤ leftPtr.toNat)
    (hSeparateRight : rightPtr.toNat + right.size ≤ target.toNat ∨
      target.toNat + (left.size + right.size) ≤ rightPtr.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      WritesRange initial final target.toNat (target.toNat + (left.size + right.size)) →
      ByteArrayAt final.mem target.toNat (left ++ right) →
      wp module_ rest Q final (counterFrame frame counterLocal right.size hCounter) env) :
    wp module_ (program leftLocal targetLocal leftLengthLocal counterLocal none ++
      program rightLocal targetLocal rightLengthLocal counterLocal (some leftLengthLocal) ++ rest)
      Q initial frame env := by
  rw [List.append_assoc]
  apply program_spec leftLocal targetLocal leftLengthLocal counterLocal none module_ env initial frame
    leftPtr target 0 left hCounter hValues hLeftNe hTargetNe hLeftLengthNe (by simp)
    hLeft hTarget hLeftLength rfl hLeftBytes (by omega) (by omega) (by omega)
  intro middle hFirstWrites hCopiedLeft
  have hFirstRange : WritesRange initial middle target.toNat (target.toNat + (left.size + right.size)) :=
    hFirstWrites.mono (by omega) (by omega)
  have hCounterMiddle := (counterFrame_validIndex frame counterLocal left.size counterLocal hCounter).2 hCounter
  apply program_spec rightLocal targetLocal rightLengthLocal counterLocal (some leftLengthLocal)
    module_ env middle (counterFrame frame counterLocal left.size hCounter) rightPtr target left.size right
    hCounterMiddle rfl hRightNe hTargetNe hRightLengthNe (by intro index h; cases h; exact hLeftLengthNe)
    ((counterFrame_get_ne _ _ _ _ hCounter hRightNe).trans hRight)
    ((counterFrame_get_ne _ _ _ _ hCounter hTargetNe).trans hTarget)
    ((counterFrame_get_ne _ _ _ _ hCounter hRightLengthNe).trans hRightLength)
    ((counterFrame_get_ne _ _ _ _ hCounter hLeftLengthNe).trans hLeftLength)
    (hRightBytes.writesRange hFirstRange hSeparateRight) (by omega)
    (by rw [hFirstWrites.2.1]; omega) (by omega)
  intro final hSecondWrites hCopiedRight
  have hCopiedLeftFinal := hCopiedLeft.writesRange hSecondWrites (Or.inl (by omega))
  have hResult : ByteArrayAt final.mem target.toNat (left ++ right) := by
    exact hCopiedLeftFinal.append hCopiedRight
  have hDone := hNext final (hFirstRange.trans (hSecondWrites.mono (by omega) (by omega))) hResult
  simpa only [counterFrame_counterFrame] using hDone

#print axioms append_spec

end Project.ProofKit.PackedCopy
