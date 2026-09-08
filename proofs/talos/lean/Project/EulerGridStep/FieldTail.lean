import Project.EulerGridStep.FieldShape
import Project.EulerGridStep.CopyUpdate

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def fieldStoreReturn : Wasm.Program :=
  [.localGet 14, .localGet 11, .constI64 1, .mulI64, .constI64 1, .addI64,
   .constI64 8, .mulI64, .addI64, .wrapI64, .localGet 16, .store64 0, .localGet 14]

theorem field_after_alloc_shape : fieldAcceptedBody.drop 39 =
    [.localGet 14, .wrapI64, .localGet 12, .store64 0] ++
      prefixProgram 10 14 13 15 ++ fieldStoreReturn := rfl

/-- The complete generated tail after allocation: initialize, copy, update and return. -/
theorem field_after_alloc_spec (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (source target : UInt64)
    (input : Array UInt64) (index : Nat) (value : UInt64)
    (hCounter : frame.validIndex 15) (hValues : frame.values = [])
    (hSource : frame.get 10 = some (.i64 source))
    (hTarget : frame.get 14 = some (.i64 target))
    (hIndex : frame.get 11 = some (.i64 (UInt64.ofNat index)))
    (hLength : frame.get 12 = some (.i64 (UInt64.ofNat input.size)))
    (hCount : frame.get 13 = some (.i64 (UInt64.ofNat input.size)))
    (hValue : frame.get 16 = some (.i64 value))
    (hInput : UInt64Array.At initial source input) (hi : index < input.size)
    (hFit32 : target.toNat + 8 * (input.size + 1) ≤ 4294967296)
    (hFitMemory : target.toNat + 8 * (input.size + 1) ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, FieldWriteState initial source target input index value final →
      wp m rest Q final
        { counterFrame frame 15 input.size hCounter with values := [.i64 target] } env) :
    wp m (fieldAcceptedBody.drop 39 ++ rest) Q initial frame env := by
  rw [field_after_alloc_shape]
  change wp m (copyUpdateProgram 10 ++ rest) Q initial frame env
  exact copy_update_spec 10 m env initial frame source target input index value
    hCounter hValues hSource hTarget hIndex hLength hCount hValue hInput hi
    hFit32 hFitMemory hSeparate Q rest hNext

#print axioms field_after_alloc_shape
#print axioms field_after_alloc_spec
end Project.EulerGridStep.Execution
