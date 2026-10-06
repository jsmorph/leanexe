import Project.Smalltalk.BootBudget
import Project.Smalltalk.ObjectConstruction
import Project.Smalltalk.ActivationConstruction

namespace Project.Smalltalk.BootConstruction
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.ConstructionValues Project.Smalltalk.BindingPreservation

structure Effect (p s t : Array UInt64) (cap : Nat) : Prop where
  heap : Heap.Valid t cap
  typed : PointerTypes.Valid t cap
  activation : Handle cap (read t 2)
  tag : field t (read t 2) 0 = 5
  methodId : field t (read t 2) 2 = read p 3
  entryPC : field t (read t 2) 3 = methodAt p (read p 3) 4
  caller : field t (read t 2) 4 = 0
  lex : field t (read t 2) 5 = 0
  stack : field t (read t 2) 7 = 0
  scratch : read t 19 = 0
  count : (read t 9).toNat + BootBudget.count p = (read s 9).toNat
  receiver : ∃ receiver, Handle cap receiver ∧ field t receiver 0 = 4 ∧
    field t receiver 2 = methodAt p (read p 3) 0 ∧
    field t receiver 4 = classAt p (methodAt p (read p 3) 0) 1 ∧
    Values t cap (field t receiver 3) (List.replicate (classAt p (methodAt p (read p 3) 0) 2).toNat 1) ∧
    Values t cap (field t (read t 2) 6) (receiver :: List.replicate (methodAt p (read p 3) 3).toNat 1)
  previous : Preserved s t cap
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read t r = read s r

theorem bootReady_eq (p s : Array UInt64) : bootReady p s =
    let t := newReady s (methodAt p (read p 3) 0)
      (classAt p (methodAt p (read p 3) 0) 1) (classAt p (methodAt p (read p 3) 0) 2)
    enterReady p t (read p 3) 0 (read t 10) 0 0 := rfl

theorem bootReady_effect {p s : Array UInt64} {cap : Nat}
    (program : programValid p = true) (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (budget : BootBudget.count p ≤ (read s 9).toNat) : Effect p s (bootReady p s) cap := by
  have objectBudget : (classAt p (methodAt p (read p 3) 0) 2).toNat + 1 ≤ (read s 9).toNat := by
    unfold BootBudget.count at budget
    omega
  let t := newReady s (methodAt p (read p 3) 0)
    (classAt p (methodAt p (read p 3) 0) 1) (classAt p (methodAt p (read p 3) 0) 2)
  have object : ObjectConstruction.Effect s t cap (methodAt p (read p 3) 0)
      (classAt p (methodAt p (read p 3) 0) 1) (classAt p (methodAt p (read p 3) 0) 2).toNat :=
    ObjectConstruction.newReady_effect valid typed objectBudget
  have allocated : field t (read t 10) 0 ≠ 0 := by rw [object.tag]; decide
  have receiverValue : HeapWrite.Value t cap (read t 10) := Or.inr ⟨object.handle, allocated⟩
  have inputs : Inputs t cap 0 (methodAt p (read p 3) 2) (read t 10) := by
    rw [ProgramBounds.entry_arity program]
    exact entry_inputs receiverValue
  have activationBudget : (methodAt p (read p 3) 2).toNat + (methodAt p (read p 3) 3).toNat + 1 ≤ (read t 9).toNat := by
    have count : (read t 9).toNat + (classAt p (methodAt p (read p 3) 0) 2).toNat + 1 = (read s 9).toNat := object.count
    unfold BootBudget.count at budget
    omega
  let result := enterReady p t (read p 3) 0 (read t 10) 0 0
  have act : ActivationConstruction.Effect p t result cap (read p 3) 0 (read t 10) 0 0 :=
    ActivationConstruction.enterReady_effect object.heap object.typed inputs (Or.inl rfl) (Or.inl rfl) activationBudget
  rw [bootReady_eq]
  change Effect p s result cap
  refine ⟨act.heap, act.typed, act.handle, act.tag, act.methodId, act.pc,
    act.caller, act.lex, act.stack, act.scratch, ?_, ?_, ?_, ?_⟩
  · have objectCount : (read t 9).toNat + (classAt p (methodAt p (read p 3) 0) 2).toNat + 1 = (read s 9).toNat := object.count
    have activationCount : (read result 9).toNat + (methodAt p (read p 3) 2).toNat + (methodAt p (read p 3) 3).toNat + 1 = (read t 9).toNat := act.count
    unfold BootBudget.count
    omega
  · refine ⟨read t 10, object.handle, ?_, ?_, ?_, ?_, ?_⟩
    · exact (act.previous _ object.handle allocated 0 (by decide)).trans object.tag
    · exact (act.previous _ object.handle allocated 2 (by decide)).trans object.classId
    · exact (act.previous _ object.handle allocated 4 (by decide)).trans object.metaId
    · rw [act.previous _ object.handle allocated 3 (by decide)]
      exact transfer object.fieldValues (fun h handle tag k bound => act.previous h handle (by rw [tag]; decide) k bound)
    · have slots := act.slots
      rw [ProgramBounds.entry_arity program] at slots
      change Values result cap (field result (read result 2) 6)
        (BindingLoop.slotValues t 0 1 (read t 10) 0 (1 + (methodAt p (read p 3) 3).toNat)) at slots
      rw [BootBudget.entry_values t (read t 10) _ (BootBudget.entry_method program).localsBound] at slots
      exact slots
  · intro h handle old k bound
    have now : field t h 0 ≠ 0 := by rw [object.previous h handle old 0 (by decide)]; exact old
    exact (act.previous h handle now k bound).trans (object.previous h handle old k bound)
  · intro r bound h2 h8 h9 h10 h13 h17 h19
    exact (act.registers r bound h2 h8 h9 h10 h13 h17 h19).trans (object.registers r bound h8 h9 h10 h13 h17 h19)

end Project.Smalltalk.BootConstruction
