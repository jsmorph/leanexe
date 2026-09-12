import Project.EulerRiemann.InitialCopyPrefix
import Project.ProofKit.OffsetArrayCopy

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

theorem initial_append_suffix_eq :
    initialGrowBody.drop 128 =
      OffsetArrayCopy.program 49 55 54 56 none (some 53) ++ initialGrowBody.drop 131 := by
  rfl

theorem initial_append_copy_spec
    (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source upper target : UInt64) (left right : Array Traversal.Cell)
    (hCounter : frame.validIndex 56) (hValues : frame.values = [])
    (hSource : frame.get 48 = some (.i64 source))
    (hUpper : frame.get 49 = some (.i64 upper))
    (hTarget : frame.get 55 = some (.i64 target))
    (hLeftCount : frame.get 53 = some (.i64 (UInt64.ofNat (7 * left.size))))
    (hRightCount : frame.get 54 = some (.i64 (UInt64.ofNat (7 * right.size))))
    (hLeft : Memory.GridAt initial source left) (hRight : Memory.GridAt initial upper right)
    (hTarget32 : target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ 4294967296)
    (hTargetMemory : target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤
      initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = UInt64.ofNat (left.size + right.size))
    (hSeparateLeft : source.toNat + 8 * (7 * left.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ source.toNat)
    (hSeparateRight : upper.toNat + 8 * (7 * right.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ upper.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesGrid initial final target (left.size + right.size) →
      Memory.GridAt final source left → Memory.GridAt final upper right →
      Memory.GridAt final target (left ++ right) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final
        (FixedArrayCopy.counterFrame frame 56 (7 * right.size) hCounter) env) :
    wp module (initialGrowBody.drop 125 ++ rest) Q initial frame env := by
  apply initial_append_prefix_spec env initial frame source target left (left.size + right.size)
    hCounter hValues hSource hTarget hLeftCount hLeft (by omega) hTarget32 hTargetMemory
    hSeparateLeft
  intro middle hFirstWrites _ hMiddleHeader hFirstCopied
  have hRightMiddle := hFirstWrites.grid hRight hSeparateRight
  have hMiddleCounter :
      (FixedArrayCopy.counterFrame frame 56 (7 * left.size) hCounter).validIndex 56 := by
    simpa only [FixedArrayCopy.counterFrame_validIndex] using hCounter
  rw [initial_append_suffix_eq, List.append_assoc]
  apply OffsetArrayCopy.program_spec 49 55 54 56 none (some 53) module env middle
    (FixedArrayCopy.counterFrame frame 56 (7 * left.size) hCounter)
    upper target (7 * right.size) (7 * (left.size + right.size)) 0 (7 * left.size) (7 * right.size)
    hMiddleCounter (by decide) (by decide) (by decide) (by simp) (by simp)
    rfl
    ((FixedArrayCopy.counterFrame_get_ne frame 56 (7 * left.size) 49 hCounter (by decide)).trans hUpper)
    ((FixedArrayCopy.counterFrame_get_ne frame 56 (7 * left.size) 55 hCounter (by decide)).trans hTarget)
    ((FixedArrayCopy.counterFrame_get_ne frame 56 (7 * left.size) 54 hCounter (by decide)).trans hRightCount)
    rfl
    ((FixedArrayCopy.counterFrame_get_ne frame 56 (7 * left.size) 53 hCounter (by decide)).trans hLeftCount)
    (by omega) (by omega) hRightMiddle.1 hTarget32 hRightMiddle.2.1
    (by rw [hFirstWrites.2.1]; exact hTargetMemory) hSeparateRight
  intro final hSecondWrites hSecondCopied
  have hSecondGridWrites : Memory.WritesGrid middle final target (left.size + right.size) :=
    hSecondWrites.mono (by omega) (by omega)
  have hWrites := hFirstWrites.trans hSecondGridWrites
  have hTargetAddress : target.toUInt32.toNat = target.toNat := by
    rw [Project.ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have hFinalHeader : final.mem.read64 target.toUInt32 = UInt64.ofNat (left.size + right.size) :=
    (hSecondWrites.read64 target.toUInt32 (by rw [hTargetAddress]; omega)).trans
      (hMiddleHeader.trans hHeader)
  have hGrid : Memory.GridAt final target (left ++ right) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Array.size_append] using hTarget32
    · simpa only [Array.size_append, hWrites.2.1] using hTargetMemory
    · simpa only [Array.size_append] using hFinalHeader
    · intro i hi field hf
      have hSize : i < left.size + right.size := by simpa only [Array.size_append] using hi
      by_cases hInLeft : i < left.size
      · rw [Array.getElem_append_left hInLeft]
        apply (hSecondWrites.read64 _ ?_).trans (hFirstCopied i hInLeft field hf)
        left
        change (UInt64Array.wordAddress target (7 * i + field + 1)).toNat + 8 ≤ _
        rw [UInt64Array.wordAddress_toNat hTarget32 (by omega)]
        omega
      · have hInRight : i - left.size < right.size := by omega
        rw [Array.getElem_append_right (by omega)]
        have hCopied := hSecondCopied (7 * (i - left.size) + field) (by omega)
        have hIndex : 7 * left.size + (7 * (i - left.size) + field) = 7 * i + field := by omega
        simp only [Nat.zero_add, hIndex] at hCopied
        exact hCopied.trans (hRightMiddle.fieldRead (i - left.size) field hInRight hf)
  have hResult := hNext final hWrites (hWrites.grid hLeft hSeparateLeft)
    (hWrites.grid hRight hSeparateRight) hGrid
  simpa only [FixedArrayCopy.counterFrame_counterFrame] using hResult

#print axioms initial_append_suffix_eq
#print axioms initial_append_copy_spec

end Project.EulerRiemann.Execution
