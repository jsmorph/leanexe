import Project.EulerGridStep.FreeChainExecution

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

structure LiveBuffer where
  root : UInt64
  contents : Array UInt64

def LiveBuffer.At (buffer : LiveBuffer) (current : Store Unit) (count : Nat) : Prop :=
  buffer.contents.size = count ∧
    OwnedHeader current buffer.root (fieldRequest count) ∧
    UInt64Array.At current buffer.root buffer.contents

def LiveBuffers (current : Store Unit) (count : Nat) (buffers : List LiveBuffer) : Prop :=
  ∀ buffer ∈ buffers, buffer.At current count

theorem liveBuffers_cons (current : Store Unit) (count : Nat) (buffer : LiveBuffer)
    (buffers : List LiveBuffer) (hBuffer : buffer.At current count)
    (hBuffers : LiveBuffers current count buffers) :
    LiveBuffers current count (buffer :: buffers) := by
  intro other hOther
  rcases List.mem_cons.mp hOther with rfl | hOther
  · exact hBuffer
  · exact hBuffers other hOther

theorem FieldResult.preserves_live_buffers {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value)
    (count : Nat) (buffers : List LiveBuffer) (hLive : LiveBuffers initial count buffers)
    (hSeparate : ∀ buffer ∈ buffers, ObjectsSeparate choice.root input.size buffer.root count) :
    LiveBuffers final count buffers := by
  intro buffer hBuffer
  rcases hLive buffer hBuffer with ⟨hSize, hHeader, hArray⟩
  exact ⟨hSize, hResult.preserves_header buffer.root (fieldRequest count) count hHeader
    (hSeparate buffer hBuffer),
    hResult.preserves_array buffer.root buffer.contents hArray
      (by rw [hSize]; exact hSeparate buffer hBuffer)⟩

theorem ReleaseResult.preserves_live_buffers {initial final : Store Unit} {root capacity next : UInt64}
    {input : Array UInt64} (hResult : ReleaseResult initial final root capacity next input)
    (count : Nat) (buffers : List LiveBuffer) (hLive : LiveBuffers initial count buffers)
    (hSeparate : ∀ buffer ∈ buffers, ObjectsSeparate root input.size buffer.root count) :
    LiveBuffers final count buffers := by
  intro buffer hBuffer
  rcases hLive buffer hBuffer with ⟨hSize, hHeader, hArray⟩
  exact ⟨hSize, hResult.preserves_header buffer.root (fieldRequest count) count hHeader
    (hSeparate buffer hBuffer),
    hResult.preserves_array buffer.root buffer.contents hArray
      (by rw [hSize]; exact hSeparate buffer hBuffer)⟩

/-- A uniformly sized clone extends the live-buffer list with the exact updated contents. -/
theorem FieldResult.add_live_buffer {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value)
    (hCapacity : choice.capacity input.size = fieldRequest input.size)
    (buffers : List LiveBuffer) (hLive : LiveBuffers initial input.size buffers)
    (hSeparate : ∀ buffer ∈ buffers, ObjectsSeparate choice.root input.size buffer.root input.size) :
    LiveBuffers final input.size
      (⟨choice.root, input.set! index value⟩ :: buffers) := by
  apply liveBuffers_cons final input.size _ buffers
  · exact ⟨by simp, by simpa only [hCapacity] using hResult.header, hResult.write.outputAt⟩
  · exact hResult.preserves_live_buffers input.size buffers hLive hSeparate

#print axioms liveBuffers_cons
#print axioms FieldResult.preserves_live_buffers
#print axioms ReleaseResult.preserves_live_buffers
#print axioms FieldResult.add_live_buffer
end Project.EulerGridStep.Execution
