import Project.TinyGpt2Checked.OutputGuard
import Project.ProofKit.BlockLoop

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.ProofKit ArrayPushLayout

structure OutputProgress (initial : Store Unit) (owner pointer empty : UInt64)
    (weights : Array UInt64) (x : Row) (start count : Nat)
    (store : Store Unit) (frame : Locals) : Prop where
  heap : OutputMemory.State start count store
  output : UInt64Array.At store (node start count).root (logitPrefix weights x count)
  locals : OutputLoopLocals owner pointer empty x (node start count).root count frame
  pages : store.mem.pages = initial.mem.pages
  bytes : ∀ address : Nat, address < start → store.mem.bytes address = initial.mem.bytes address
  store : store = { initial with mem := store.mem, globals := store.globals }

def outputRemaining (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 49 with
  | some (.i64 count) => 256 - count.toNat
  | _ => 0

theorem outputRemaining_eq (store : Store Unit) (frame : Locals) (count : Nat)
    (hCount : count ≤ 256) (hCounter : frame.get 49 = some (.i64 (UInt64.ofNat count))) :
    outputRemaining store frame = 256 - count := by
  simp only [outputRemaining, hCounter]
  rw [UInt64.toNat_ofNat_of_lt' (by change count < 18446744073709551616; omega)]

theorem output_loop_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (owner pointer empty : UInt64) (weights : Array UInt64) (x : Row) (start count : Nat)
    (hLocals : OutputLoopLocals owner pointer empty x (node start count).root count frame)
    (hEmpty : empty = (node start 0).root)
    (hState : OutputMemory.State start count initial)
    (hInput : UInt64Array.At initial (node start count).root (logitPrefix weights x count))
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (hWeightsBefore : pointer.toNat + 8 * (weights.size + 1) ≤ start)
    (hCount : count ≤ 256)
    (hFit : top start 256 < 4294967296)
    (hMemory : top start 256 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (finalFrame : Locals),
      OutputProgress initial owner pointer empty weights x start 256 final finalFrame →
      wp module rest Q final finalFrame env) :
    wp module ([.block 0 0 [.loop 0 0 outputBody]] ++ rest) Q initial frame env := by
  let progress := OutputProgress initial owner pointer empty weights x start
  let Inv : AssertionF Unit := fun store frame => ∃ count : Nat, count ≤ 256 ∧ progress count store frame
  let Done : AssertionF Unit := progress 256
  refine BlockLoop.program_spec module env initial frame outputBody Inv Done outputRemaining
    ?_ ?_ ?_ ?_ Q rest ?_
  · rintro _ _ ⟨_, _, h⟩
    exact h.locals.values
  · intro _ _ h
    exact h.locals.values
  · exact ⟨count, hCount, hState, hInput, hLocals, rfl, fun _ _ => rfl, rfl⟩
  · intro current currentFrame hInv
    obtain ⟨index, hIndex, hProgress⟩ := hInv
    apply output_guard_spec env current currentFrame owner pointer empty (node start index).root x index
      hProgress.locals hIndex
    · intro hEnd
      subst index
      exact hProgress
    · intro hContinue
      have hCurrentWeights : UInt64Array.At current pointer weights := by
        apply hWeights.frame hProgress.pages.ge
        intro address _ hAddress
        exact hProgress.bytes address (hAddress.trans_le hWeightsBefore)
      have hCurrentCap : current.memoryCap module 0 = initial.memoryCap module 0 := by
        rw [hProgress.store]
        rfl
      apply output_iteration_spec env current currentFrame owner pointer empty weights x start index
        hProgress.locals hEmpty hProgress.heap hProgress.output hCurrentWeights hSize hContinue
        ((top_mono start (show index + 1 ≤ 256 by omega)).trans_lt hFit)
        (by rw [hProgress.pages]; exact (top_mono start (by omega)).trans hMemory)
        (by rw [hProgress.pages]; exact hPages)
        (by rw [hProgress.pages, hCurrentCap]; exact hCap)
      intro final finalFrame hHeap hOutput hFinalLocals hFinalPages hBytes hStore
      change (∃ count : Nat, count ≤ 256 ∧ progress count final finalFrame) ∧
        outputRemaining final finalFrame < outputRemaining current currentFrame
      refine ⟨⟨index + 1, by omega, hHeap, hOutput, hFinalLocals,
        hFinalPages.trans hProgress.pages,
        fun address hAddress => (hBytes address hAddress).trans (hProgress.bytes address hAddress), ?_⟩, ?_⟩
      · rw [hStore, hProgress.store]
      · rw [outputRemaining_eq final finalFrame (index + 1) (by omega) hFinalLocals.counter,
          outputRemaining_eq current currentFrame index hIndex hProgress.locals.counter]
        omega
  · exact hNext

#print axioms output_loop_spec
end Project.TinyGpt2Checked.Spec
