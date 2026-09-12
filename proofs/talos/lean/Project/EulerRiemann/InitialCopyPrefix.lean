import Project.EulerRiemann.Program
import Project.EulerRiemann.MemoryOwnership
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayCopy

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialGrowBody : Wasm.Program :=
  (Annotation.resolve func88
    [{ instructionIndex := 4, field := .block },
     { instructionIndex := 0, field := .loop },
     { instructionIndex := 14, field := .elseBranch }]).getD []

theorem initial_append_prefix_eq :
    initialGrowBody.drop 125 =
      FixedArrayCopy.prefixProgram 48 55 53 56 ++ initialGrowBody.drop 128 := by
  rfl

theorem initial_append_prefix_spec
    (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (grid : Array Traversal.Cell) (targetSize : Nat)
    (hCounter : frame.validIndex 56) (hValues : frame.values = [])
    (hSource : frame.get 48 = some (.i64 source))
    (hTarget : frame.get 55 = some (.i64 target))
    (hCount : frame.get 53 = some (.i64 (UInt64.ofNat (7 * grid.size))))
    (hGrid : Memory.GridAt initial source grid) (hSize : grid.size ≤ targetSize)
    (hTarget32 : target.toNat + 8 * (7 * targetSize + 1) ≤ 4294967296)
    (hTargetMemory : target.toNat + 8 * (7 * targetSize + 1) ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * targetSize + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesGrid initial final target targetSize →
      Memory.GridAt final source grid →
      final.mem.read64 target.toUInt32 = initial.mem.read64 target.toUInt32 →
      (∀ (i : Nat) (hi : i < grid.size) (field : Nat), field < 7 →
        final.mem.read64 (target + UInt64.ofNat (8 * (7 * i + field + 1))).toUInt32 =
          (Memory.cellWords grid[i]).getD field 0) →
      wp module (initialGrowBody.drop 128 ++ rest) Q final
        (FixedArrayCopy.counterFrame frame 56 (7 * grid.size) hCounter) env) :
    wp module (initialGrowBody.drop 125 ++ rest) Q initial frame env := by
  rw [initial_append_prefix_eq, List.append_assoc]
  apply FixedArrayCopy.prefixProgram_framed_spec 48 55 53 56 module env initial frame
    source target (7 * grid.size) (7 * targetSize) (7 * grid.size)
    hCounter (by decide) (by decide) (by decide) hValues hSource hTarget hCount
    (Nat.le_refl _) (by omega) hGrid.1 hTarget32 hGrid.2.1 hTargetMemory hSeparate
  intro final _ hHeader _ hCopied hWrites
  have hGridWrites : Memory.WritesGrid initial final target targetSize :=
    hWrites.mono (by omega) (by omega)
  apply hNext final hGridWrites (hGridWrites.grid hGrid hSeparate) hHeader
  intro i hi field hf
  exact (hCopied (7 * i + field) (by omega)).trans (hGrid.fieldRead i field hi hf)

#print axioms initial_append_prefix_eq
#print axioms initial_append_prefix_spec

end Project.EulerRiemann.Execution
