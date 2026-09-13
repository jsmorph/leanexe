import Project.ProofKit.ArrayPrefix
import Project.ProofKit.OffsetArrayCopy

namespace Project.ProofKit.UInt64Array
open Wasm FixedArrayCopy

theorem appendCopy_spec (sourceLocal upperLocal targetLocal leftLocal rightLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source upper target : UInt64) (left right : Array UInt64)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hSourceNe : sourceLocal ≠ counterLocal) (hUpperNe : upperLocal ≠ counterLocal)
    (hTargetNe : targetLocal ≠ counterLocal) (hLeftNe : leftLocal ≠ counterLocal)
    (hRightNe : rightLocal ≠ counterLocal)
    (hSource : frame.get sourceLocal = some (.i64 source))
    (hUpper : frame.get upperLocal = some (.i64 upper))
    (hTarget : frame.get targetLocal = some (.i64 target))
    (hLeftCount : frame.get leftLocal = some (.i64 (UInt64.ofNat left.size)))
    (hRightCount : frame.get rightLocal = some (.i64 (UInt64.ofNat right.size)))
    (hLeft : At initial source left) (hRight : At initial upper right)
    (hTarget32 : target.toNat + 8 * (left.size + right.size + 1) ≤ 4294967296)
    (hTargetMemory : target.toNat + 8 * (left.size + right.size + 1) ≤ initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = UInt64.ofNat (left.size + right.size))
    (hSeparateLeft : source.toNat + 8 * (left.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (left.size + right.size + 1) ≤ source.toNat)
    (hSeparateRight : upper.toNat + 8 * (right.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (left.size + right.size + 1) ≤ upper.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesRange initial final target.toNat (target.toNat + 8 * (left.size + right.size + 1)) →
      At final source left → At final upper right → At final target (left ++ right) →
      wp module_ rest Q final (counterFrame frame counterLocal right.size hCounter) env) :
    wp module_ (prefixProgram sourceLocal targetLocal leftLocal counterLocal ++
      OffsetArrayCopy.program upperLocal targetLocal rightLocal counterLocal none (some leftLocal) ++ rest)
      Q initial frame env := by
  rw [List.append_assoc]
  apply prefixProgram_framed_spec sourceLocal targetLocal leftLocal counterLocal module_ env initial frame
    source target left.size (left.size + right.size) left.size hCounter hSourceNe hTargetNe hLeftNe
    hValues hSource hTarget hLeftCount (Nat.le_refl _) (by omega)
    hLeft.1 hTarget32 hLeft.2.1 hTargetMemory hSeparateLeft
  intro middle _ hMiddleHeader _ hFirstCopied hFirstWrites
  have hFirstRange : Memory.WritesRange initial middle target.toNat
      (target.toNat + 8 * (left.size + right.size + 1)) := hFirstWrites.mono (by omega) (by omega)
  have hRightMiddle := hRight.writesRange hFirstRange hSeparateRight
  have hMiddleCounter : (counterFrame frame counterLocal left.size hCounter).validIndex counterLocal := by
    simpa only [counterFrame_validIndex] using hCounter
  apply OffsetArrayCopy.program_spec upperLocal targetLocal rightLocal counterLocal none (some leftLocal)
    module_ env middle (counterFrame frame counterLocal left.size hCounter)
    upper target right.size (left.size + right.size) 0 left.size right.size hMiddleCounter
    hUpperNe hTargetNe hRightNe (by simp) (by simp [hLeftNe]) rfl
    ((counterFrame_get_ne _ _ _ _ hCounter hUpperNe).trans hUpper)
    ((counterFrame_get_ne _ _ _ _ hCounter hTargetNe).trans hTarget)
    ((counterFrame_get_ne _ _ _ _ hCounter hRightNe).trans hRightCount) rfl
    ((counterFrame_get_ne _ _ _ _ hCounter hLeftNe).trans hLeftCount)
    (by omega) (Nat.le_refl _) hRightMiddle.1 hTarget32 hRightMiddle.2.1
    (by rw [hFirstRange.2.1]; exact hTargetMemory) hSeparateRight
  intro final hSecondWrites hSecondCopied
  have hSecondRange : Memory.WritesRange middle final target.toNat
      (target.toNat + 8 * (left.size + right.size + 1)) := hSecondWrites.mono (by omega) (Nat.le_refl _)
  have hWrites := hFirstRange.trans hSecondRange
  have hTargetAddress : target.toUInt32.toNat = target.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have hFinalHeader : final.mem.read64 target.toUInt32 = UInt64.ofNat (left.size + right.size) :=
    (hSecondWrites.read64 target.toUInt32 (by rw [hTargetAddress]; omega)).trans
      (hMiddleHeader.trans hHeader)
  have hResult : At final target (left ++ right) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Array.size_append] using hTarget32
    · simpa only [Array.size_append, hWrites.2.1] using hTargetMemory
    · simpa only [Array.size_append] using hFinalHeader
    · intro i hi
      have hSize : i < left.size + right.size := by simpa only [Array.size_append] using hi
      by_cases hInLeft : i < left.size
      · rw [Array.getElem_append_left hInLeft]
        apply (hSecondWrites.read64 _ ?_).trans ((hFirstCopied i hInLeft).trans (hLeft.elementRead i hInLeft))
        left
        change (wordAddress target (i + 1)).toNat + 8 ≤ _
        rw [wordAddress_toNat hTarget32 (by omega)]
        omega
      · have hInRight : i - left.size < right.size := by omega
        rw [Array.getElem_append_right (by omega)]
        have hCopied := hSecondCopied (i - left.size) hInRight
        have hIndex : left.size + (i - left.size) = i := by omega
        simp only [Nat.zero_add, hIndex] at hCopied
        exact hCopied.trans (hRightMiddle.elementRead (i - left.size) hInRight)
  have hDone := hNext final hWrites (hLeft.writesRange hWrites hSeparateLeft)
    (hRight.writesRange hWrites hSeparateRight) hResult
  simpa only [counterFrame_counterFrame] using hDone

#print axioms appendCopy_spec

end Project.ProofKit.UInt64Array
