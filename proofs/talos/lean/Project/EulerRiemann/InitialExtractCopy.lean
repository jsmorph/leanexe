import Project.EulerRiemann.InitialCopyPrefix
import Project.ProofKit.OffsetArrayCopy

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialExtractBody : Wasm.Program :=
  (Annotation.resolve func88 [{ instructionIndex := 8, field := .thenBranch }]).getD []

def initialDoneBody : Wasm.Program :=
  (Annotation.resolve func88
    [{ instructionIndex := 4, field := .block },
     { instructionIndex := 0, field := .loop },
     { instructionIndex := 14, field := .thenBranch }]).getD []

def initialExtractCopy : Wasm.Program := (initialExtractBody.drop 67).take 3

theorem initial_extract_copy_eq :
    initialExtractCopy = OffsetArrayCopy.program 48 56 55 57 (some 54) none := by
  rfl

theorem initial_extract_fuel_copy_eq :
    initialExtractBody.drop 67 = initialExtractCopy ++ initialExtractBody.drop 70 := by
  rfl

theorem initial_extract_done_copy_eq :
    initialDoneBody.drop 67 = initialExtractCopy ++ initialDoneBody.drop 70 := by
  rfl

theorem initial_extract_prefix_eq : initialDoneBody.take 70 = initialExtractBody.take 70 := by
  rfl

theorem initial_extract_copy_spec
    (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (grid : Array Traversal.Cell) (size : Nat)
    (hCounter : frame.validIndex 57) (hValues : frame.values = [])
    (hSource : frame.get 48 = some (.i64 source))
    (hTarget : frame.get 56 = some (.i64 target))
    (hOffset : frame.get 54 = some (.i64 0))
    (hCount : frame.get 55 = some (.i64 (UInt64.ofNat (7 * size))))
    (hGrid : Memory.GridAt initial source grid) (hSize : size ≤ grid.size)
    (hTarget32 : target.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hTargetMemory : target.toNat + 8 * (7 * size + 1) ≤ initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = UInt64.ofNat size)
    (hSeparate : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesGrid initial final target size → Memory.GridAt final source grid →
      Memory.GridAt final target (grid.extract 0 size) →
      wp module rest Q final (FixedArrayCopy.counterFrame frame 57 (7 * size) hCounter) env) :
    wp module (initialExtractCopy ++ rest) Q initial frame env := by
  rw [initial_extract_copy_eq]
  apply OffsetArrayCopy.program_spec 48 56 55 57 (some 54) none module env initial frame
    source target (7 * grid.size) (7 * size) 0 0 (7 * size) hCounter
    (by decide) (by decide) (by decide) (by simp) (by simp)
    hValues hSource hTarget hCount hOffset rfl
    (by omega) (by omega) hGrid.1 hTarget32 hGrid.2.1 hTargetMemory hSeparate
  intro final hWrites hCopied
  have hGridWrites : Memory.WritesGrid initial final target size :=
    hWrites.mono (by omega) (by omega)
  have hExtractSize : (grid.extract 0 size).size = size := by
    simp only [Array.size_extract, Nat.min_eq_left hSize, Nat.sub_zero]
  have hResult : Memory.GridAt final target (grid.extract 0 size) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hExtractSize] using hTarget32
    · simpa only [hExtractSize, hWrites.2.1] using hTargetMemory
    · rw [hExtractSize]
      apply (hWrites.read64 target.toUInt32 ?_).trans hHeader
      rw [Project.ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
      omega
    · intro i hi field hf
      have hIndex : i < size := by simpa only [hExtractSize] using hi
      simp only [Array.getElem_extract, Nat.zero_add]
      have hRead := hCopied (7 * i + field) (by omega)
      simp only [Nat.zero_add] at hRead
      exact hRead.trans (hGrid.fieldRead i field (by omega) hf)
  exact hNext final hGridWrites (hGridWrites.grid hGrid hSeparate) hResult

#print axioms initial_extract_copy_eq
#print axioms initial_extract_fuel_copy_eq
#print axioms initial_extract_done_copy_eq
#print axioms initial_extract_prefix_eq
#print axioms initial_extract_copy_spec

end Project.EulerRiemann.Execution
