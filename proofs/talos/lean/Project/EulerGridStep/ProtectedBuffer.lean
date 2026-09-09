import Project.EulerGridStep.LiveBuffers

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A separately owned buffer survives a complete field clone. -/
theorem FieldResult.preserves_buffer {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (h : FieldResult choice initial final source input index value)
    (buffer : LiveBuffer) (count : Nat) (hBuffer : buffer.At initial count)
    (hSeparate : ObjectsSeparate choice.root input.size buffer.root count) : buffer.At final count :=
  ⟨hBuffer.1, h.preserves_header buffer.root (fieldRequest count) count hBuffer.2.1 hSeparate,
    h.preserves_array buffer.root buffer.contents hBuffer.2.2 (by rw [hBuffer.1]; exact hSeparate)⟩

/-- A separately owned buffer survives an intermediate release. -/
theorem ReleaseResult.preserves_buffer {initial final : Store Unit} {root capacity next : UInt64}
    {input : Array UInt64} (h : ReleaseResult initial final root capacity next input)
    (buffer : LiveBuffer) (count : Nat) (hBuffer : buffer.At initial count)
    (hSeparate : ObjectsSeparate root input.size buffer.root count) : buffer.At final count :=
  ⟨hBuffer.1, h.preserves_header buffer.root (fieldRequest count) count hBuffer.2.1 hSeparate,
    h.preserves_array buffer.root buffer.contents hBuffer.2.2 (by rw [hBuffer.1]; exact hSeparate)⟩

#print axioms FieldResult.preserves_buffer
#print axioms ReleaseResult.preserves_buffer
end Project.EulerGridStep.Execution
