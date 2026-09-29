import Project.TalosPrelude
import Project.Pipeline.Runtime

namespace Project.Pipeline

open Wasm

/-- Entry `entry` of `m` computes `f` bit for bit.  From any store that satisfies
the allocator invariant, holds the input words `xs` at `input`, and has room for
`need xs` bytes, the call terminates and returns a pointer to a new array object
holding `f xs`, owned by the caller.  The input is unchanged, the allocator
invariant holds again, `top` advances by at most `need xs` bytes, and memory
grows only as far as the new `top` requires. -/
def Implements (m : Module) (entry : Nat) (f : Array UInt64 → Array UInt64)
    (need : Array UInt64 → Nat) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (input : UInt64)
    (xs : Array UInt64),
    heap.At store → heap.Borrowed store input xs → heap.Room store m (need xs) →
    TerminatesWith env m entry store [.i64 input] fun final values =>
      ∃ (output : UInt64) (heap' : Heap),
        values = [.i64 output] ∧ heap'.At final ∧ heap'.Owned final output (f xs) ∧
        heap'.Borrowed final input xs ∧ heap'.top.toNat ≤ heap.top.toNat + need xs ∧
        final.mem.pages ≤ max store.mem.pages ((heap.top.toNat + need xs + 65535) / 65536)

/-- For every input satisfying `P`, under the premises of `Implements`, the call
returns a new owned array `ys` with `Q xs ys`. -/
def Satisfies (m : Module) (entry : Nat) (need : Array UInt64 → Nat)
    (P : Array UInt64 → Prop) (Q : Array UInt64 → Array UInt64 → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (input : UInt64)
    (xs : Array UInt64),
    P xs → heap.At store → heap.Borrowed store input xs → heap.Room store m (need xs) →
    TerminatesWith env m entry store [.i64 input] fun final values =>
      ∃ (output : UInt64) (heap' : Heap) (ys : Array UInt64),
        values = [.i64 output] ∧ heap'.At final ∧ heap'.Owned final output ys ∧ Q xs ys

theorem Implements.transfer {m : Module} {entry : Nat} {need : Array UInt64 → Nat}
    {f : Array UInt64 → Array UInt64} {P : Array UInt64 → Prop}
    {Q : Array UInt64 → Array UInt64 → Prop}
    (h : Implements m entry f need) (hf : ∀ xs, P xs → Q xs (f xs)) :
    Satisfies m entry need P Q := by
  intro env store heap input xs hP hHeap hInput hRoom
  obtain ⟨N, hN⟩ := h env store heap input xs hHeap hInput hRoom
  refine ⟨N, fun fuel hFuel => ?_⟩
  obtain ⟨values, final, hRun, output, heap', hValues, hAt, hOwned, -⟩ := hN fuel hFuel
  exact ⟨values, final, hRun, output, heap', f xs, hValues, hAt, hOwned, hf xs hP⟩

end Project.Pipeline
