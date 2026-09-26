import Project.EulerGridStep.RecyclingState

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

theorem liveBuffer_root_nonzero {current : Store Unit} {buffer : LiveBuffer} {count : Nat}
    (h : buffer.At current count) : buffer.root ≠ 0 := by
  intro hz
  have h48 := h.2.1.root48
  rw [hz] at h48
  contradiction

theorem recycling_stopped_of_buffers {current : Store Unit} {base index : Nat} {pointer root : UInt64}
    {input output : Array UInt64} {free : List UInt64} {a r f : UInt64}
    (h : BufferState current output.size [⟨root, output⟩] free a r f)
    (hSeparate : ObjectsSeparate root output.size (arenaRoot base output.size 0) output.size)
    (hStatus : output[0]! ≠ 0) :
    RecyclingState current base pointer input output index root := by
  have hLive := h.liveAt ⟨root, output⟩ (by simp)
  exact ⟨hLive.2.2, liveBuffer_root_nonzero hLive,
    fun _ => gridFinishReady_of_buffers h hSeparate, fun hs _ => False.elim (hStatus hs)⟩

theorem recycling_first_accepted_state {current : Store Unit} {base : Nat} {pointer : UInt64}
    {input output : Array UInt64} {a r f : UInt64}
    (hPositive : 0 < input.size / 3)
    (h : LaterArenaState current base (input.size / 3) 1 output a r f) :
    RecyclingState current base pointer input output 1 (arenaRoot base output.size 6) := by
  have hLive := h.buffers.liveAt ⟨arenaRoot base output.size 6, output⟩ (by simp)
  have hBudget := h.budget
  have hPages := h.buffers.pages
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hSeparate := arena_roots_separate_of_lt base output.size 6 0 (input.size / 3 + 6)
    (by omega) (by omega) (by decide) hBudget32
  refine ⟨hLive.2.2, liveBuffer_root_nonzero hLive, ?_, ?_⟩
  · intro _
    exact gridFinishReady_of_buffers h.buffers hSeparate
  · intro _ _
    exact Or.inr (Or.inl ⟨rfl, rfl, a, r, f, h⟩)

theorem recycling_initial_state {current : Store Unit} {base : Nat} {pointer : UInt64}
    {input output : Array UInt64} {a r f : UInt64}
    (h : GridLoopStorage current base (input.size / 3) 0 output a r f) :
    RecyclingState current base pointer input output 0 (arenaRoot base output.size 0) := by
  have hBuffers := h.buffers
  simp only [gridLoopRoot, gridLoopPool, ite_true] at hBuffers
  have hLive := hBuffers.liveAt ⟨arenaRoot base output.size 0, output⟩ (by simp)
  exact ⟨hLive.2.2, liveBuffer_root_nonzero hLive, fun hi => False.elim (by omega),
    fun _ _ => Or.inl ⟨rfl, rfl, a, r, f, h⟩⟩

#print axioms recycling_first_accepted_state
#print axioms recycling_stopped_of_buffers
#print axioms recycling_initial_state
end Project.EulerGridStep.Execution
