import Project.EulerRiemann.FrozenOutputShape
import Project.ProofKit.ArrayAppend

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit

def outputAppendCopyProgram (header : Bool) : Wasm.Program :=
  (func99.drop (if header then 343 else 167)).take 6

theorem output_append_copy_shape (header : Bool) : outputAppendCopyProgram header =
    FixedArrayCopy.prefixProgram 36 43 41 44 ++
      OffsetArrayCopy.program 37 43 42 44 none (some 41) := by
  cases header <;> rfl

theorem output_append_copy_spec (header : Bool) (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (source upper target : UInt64)
    (left right : Array UInt64) (hCounter : frame.validIndex 44) (hValues : frame.values = [])
    (hSource : frame.get 36 = some (.i64 source))
    (hUpper : frame.get 37 = some (.i64 upper))
    (hTarget : frame.get 43 = some (.i64 target))
    (hLeftCount : frame.get 41 = some (.i64 (UInt64.ofNat left.size)))
    (hRightCount : frame.get 42 = some (.i64 (UInt64.ofNat right.size)))
    (hLeft : UInt64Array.At initial source left) (hRight : UInt64Array.At initial upper right)
    (hTarget32 : target.toNat + 8 * (left.size + right.size + 1) ≤ 4294967296)
    (hTargetMemory : target.toNat + 8 * (left.size + right.size + 1) ≤ initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = UInt64.ofNat (left.size + right.size))
    (hSeparateLeft : source.toNat + 8 * (left.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (left.size + right.size + 1) ≤ source.toNat)
    (hSeparateRight : upper.toNat + 8 * (right.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (left.size + right.size + 1) ≤ upper.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      ProofKit.Memory.WritesRange initial final target.toNat
        (target.toNat + 8 * (left.size + right.size + 1)) →
      UInt64Array.At final source left → UInt64Array.At final upper right →
      UInt64Array.At final target (left ++ right) →
      wp module rest Q final (FixedArrayCopy.counterFrame frame 44 right.size hCounter) env) :
    wp module (outputAppendCopyProgram header ++ rest) Q initial frame env := by
  rw [output_append_copy_shape]
  exact UInt64Array.appendCopy_spec 36 37 43 41 42 44 module env initial frame source upper target left right
    hCounter hValues (by decide) (by decide) (by decide) (by decide) (by decide)
    hSource hUpper hTarget hLeftCount hRightCount hLeft hRight hTarget32 hTargetMemory
    hHeader hSeparateLeft hSeparateRight Q rest hNext

#print axioms output_append_copy_shape
#print axioms output_append_copy_spec

end Project.EulerRiemann.Frozen.Execution
