import Project.ProofKit.FixedArrayFold

namespace LeanExeGen.Knowledge.Proposal4f56fd45fe24D4f7d73b3648.Proposed

open Wasm Project.ProofKit

theorem singletonResultProgram_spec_to_fromFrame
    (accumulatorLocal resultLocal rootLocal destinationLocal returnLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (root value : UInt64)
    (hValues : frame.values = [])
    (hAccumulator : frame.get accumulatorLocal = some (.i64 value))
    (hResultLocal : frame.params.length ≤ resultLocal)
    (hResultValid : frame.validIndex resultLocal)
    (hRootLocal : frame.params.length ≤ rootLocal)
    (hRootValid : frame.validIndex rootLocal)
    (hRootNe : rootLocal ≠ resultLocal)
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hPayloadBound :
      (FixedArrayResult.payloadAddress root 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (hDestinationLower : frame.params.length ≤ destinationLocal)
    (hDestinationValid : frame.validIndex destinationLocal)
    (hReturnLower : frame.params.length ≤ returnLocal)
    (hReturnValid : frame.validIndex returnLocal)
    (Q : Assertion Unit)
    (hNext : Q (.Fallthrough
      (FixedArrayResult.writePayload st root 0 value)
      (FixedArrayResult.finishFrame
        (FixedArrayFold.resultFrame frame resultLocal value)
        destinationLocal returnLocal root))) :
    wp module_
      (FixedArrayFold.singletonResultProgram accumulatorLocal resultLocal
        rootLocal destinationLocal returnLocal)
      Q st frame env := by
  apply FixedArrayFold.singletonResultProgram_spec_to
  · exact hValues
  · exact hAccumulator
  · exact hResultLocal
  · exact hResultValid
  · exact FixedArrayFold.resultFrame_get_of_ne frame resultLocal rootLocal
      value (.i64 root) hResultLocal hRootLocal hRootValid hRootNe hRoot
  · exact FixedArrayFold.resultFrame_get_result frame resultLocal value
      hResultLocal hResultValid
  · exact hPayloadBound
  · simpa only [FixedArrayFold.resultFrame_params] using hDestinationLower
  · simpa only [Wasm.Locals.validIndex,
      FixedArrayFold.resultFrame_params,
      FixedArrayFold.resultFrame_locals_length] using hDestinationValid
  · simpa only [FixedArrayFold.resultFrame_params] using hReturnLower
  · simpa only [Wasm.Locals.validIndex,
      FixedArrayFold.resultFrame_params,
      FixedArrayFold.resultFrame_locals_length] using hReturnValid
  · exact hNext

end LeanExeGen.Knowledge.Proposal4f56fd45fe24D4f7d73b3648.Proposed
