import Project.EulerGridStep.GridLoopStorage
import Project.EulerGridStep.RecycledPool

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- The final initial-buffer release needs only these observable heap facts. -/
structure GridFinishReady (current : Store Unit) (root initialRoot : UInt64) (output : Array UInt64) : Prop where
  outputAt : UInt64Array.At current root output
  separate : ObjectsSeparate root output.size initialRoot output.size
  counters : ∃ head releases frees : UInt64,
    current.globals.globals[1]? = some (.i64 head) ∧
    current.globals.globals[4]? = some (.i64 releases) ∧
    current.globals.globals[5]? = some (.i64 frees)

theorem gridFinishReady_of_buffers {current : Store Unit} {root initialRoot : UInt64}
    {output : Array UInt64} {free : List UInt64} {a r f : UInt64}
    (h : BufferState current output.size [⟨root, output⟩] free a r f)
    (hSeparate : ObjectsSeparate root output.size initialRoot output.size) :
    GridFinishReady current root initialRoot output :=
  ⟨(h.liveAt ⟨root, output⟩ (by simp)).2.2, hSeparate,
    free.headD 0, r, f, h.freeHead, h.releases, h.frees⟩

theorem RecycledPool.finishReady {current : Store Unit} {roots : Nat → UInt64}
    {pointer initialRoot : UInt64} {input output : Array UInt64} {a r f : UInt64}
    (h : RecycledPool current roots pointer initialRoot input output a r f) :
    GridFinishReady current (roots 0) initialRoot output :=
  gridFinishReady_of_buffers h.buffers (h.initialSeparate 0 (by decide))

/-- Only the first two accepted calls may grow the arena. Later calls cycle through seven slots. -/
def RecyclingRunning (current : Store Unit) (base : Nat) (pointer : UInt64)
    (input output : Array UInt64) (index : Nat) (root : UInt64) : Prop :=
  (index = 0 ∧ root = arenaRoot base output.size 0 ∧
    ∃ a r f, GridLoopStorage current base (input.size / 3) 0 output a r f) ∨
  (index = 1 ∧ root = arenaRoot base output.size 6 ∧
    ∃ a r f, LaterArenaState current base (input.size / 3) 1 output a r f) ∨
  (∃ (roots : Nat → UInt64) (a r f : UInt64), root = roots 0 ∧
    RecycledPool current roots pointer (arenaRoot base output.size 0) input output a r f)

/-- The loop retains enough storage to continue while its header is accepted,
    and enough ownership to release the initial buffer whenever it stops. -/
structure RecyclingState (current : Store Unit) (base : Nat) (pointer : UInt64)
    (input output : Array UInt64) (index : Nat) (root : UInt64) : Prop where
  outputAt : UInt64Array.At current root output
  rootNonzero : root ≠ 0
  finish : 0 < index → GridFinishReady current root (arenaRoot base output.size 0) output
  running : output[0]! = 0 → index < input.size / 3 →
    RecyclingRunning current base pointer input output index root

theorem RecycledPool.recyclingState {current : Store Unit} {roots : Nat → UInt64}
    {pointer : UInt64} {base index : Nat} {input output : Array UInt64} {a r f : UInt64}
    (h : RecycledPool current roots pointer (arenaRoot base output.size 0) input output a r f) :
    RecyclingState current base pointer input output index (roots 0) := by
  have hLive := h.buffers.liveAt ⟨roots 0, output⟩ (by simp)
  refine ⟨hLive.2.2, ?_, fun _ => h.finishReady, fun _ _ => Or.inr (Or.inr ?_)⟩
  · intro hz
    have h48 := hLive.2.1.root48
    rw [hz] at h48
    contradiction
  · exact ⟨roots, a, r, f, rfl, h⟩

#print axioms gridFinishReady_of_buffers
#print axioms RecycledPool.finishReady
end Project.EulerGridStep.Execution
