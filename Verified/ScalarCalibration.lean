import Verified.Instantiate
import LeanExe.Pipeline.Implements

namespace Wasm

def Result.withStore (store : Store α) : Result α → Result α
  | .Success values _ => .Success values store
  | .Trap _ message => .Trap store message
  | .Invalid message => .Invalid message
  | .OutOfFuel => .OutOfFuel
  | .Thrown tag values _ => .Thrown tag values store

def EntryUniform (m : Module) (entry : Nat) : Prop :=
  ∀ (fuel : Nat) (host : HostEnv Unit) (store reference : Store Unit) (args : List Value),
    run fuel m entry store args host =
      (run fuel m entry reference args host).withStore store

end Wasm

namespace Verified

open Wasm LeanExe.Pipeline

def scalarReferenceStore : Store Unit := (compile Prog.nil).initialStore

def scalarReferenceHeap : Heap := initialHeap []

theorem scalarReference_at : scalarReferenceHeap.At scalarReferenceStore :=
  (compileWith_initialStore Prog.nil [] [] (by decide) rfl).1

theorem scalarReference_cap (m : Module) : scalarReferenceStore.memoryCap m 0 ≤ 65535 := by
  change 65535 ≤ 65535
  exact Nat.le_refl _

theorem implementsPure_of_uniform {α β : Type} [Scalar α] [Scalar β] {aborts : Bool}
    {m : Module} {entry : Nat} {f : α → β}
    (h : ImplementsA aborts m entry f (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (hUniform : EntryUniform m entry) : ImplementsPureA aborts m entry f := by
  intro host store x
  have hArgs : Represent.borrowed scalarReferenceHeap scalarReferenceStore (Scalar.values x) x := rfl
  have hSeparate : Separate scalarReferenceStore
      (Represent.moves scalarReferenceStore (Scalar.values x) x)
      (Represent.reads scalarReferenceStore (Scalar.values x) x) := Separate.nil
  obtain ⟨N, hN⟩ := h host scalarReferenceStore scalarReferenceHeap (Scalar.values x) x
    scalarReference_at trivial hArgs hSeparate (scalarReference_cap m)
  refine ⟨N, fun fuel hFuel => ?_⟩
  have hRun := hUniform fuel host store scalarReferenceStore (Scalar.values x).reverse
  rcases hN fuel hFuel with ⟨values, final, hFinal, heap, hAt, hOwned, _⟩ | hTrap
  · left
    refine ⟨values, store, ?_, rfl, hOwned⟩
    rw [hRun, hFinal]
    rfl
  · right
    cases aborts with
    | false => exact False.elim hTrap
    | true =>
      obtain ⟨final, hFinal⟩ := hTrap
      exact ⟨store, by rw [hRun, hFinal]; rfl⟩

#print axioms scalarReference_at
#print axioms implementsPure_of_uniform

end Verified
