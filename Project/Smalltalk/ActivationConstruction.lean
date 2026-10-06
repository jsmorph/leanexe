import Project.Smalltalk.ActivationAllocation

namespace Project.Smalltalk.ActivationConstruction
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.AllocationEffect
open Project.Smalltalk.ConstructionValues Project.Smalltalk.BindingPreservation

theorem enterReady_eq (p s : Array UInt64) (method args receiver caller lex : UInt64) :
    enterReady p s method args receiver caller lex =
      let t := (BindingLoop.binding s args (methodAt p method 2) (methodAt p method 3) receiver).2
      let q := allocate t 5 method (methodAt p method 4) caller lex (read t 19) 0
      write (write q 2 (read q 10)) 19 0 := by
  rw [BindingLoop.binding_eq_pair]
  rfl

structure Effect (p original t : Array UInt64) (cap : Nat) (method args receiver caller lex : UInt64) : Prop where
  heap : Heap.Valid t cap
  typed : PointerTypes.Valid t cap
  handle : Handle cap (read t 2)
  last : read t 10 = read t 2
  tag : field t (read t 2) 0 = 5
  methodId : field t (read t 2) 2 = method
  pc : field t (read t 2) 3 = methodAt p method 4
  caller : field t (read t 2) 4 = caller
  lex : field t (read t 2) 5 = lex
  slots : Values t cap (field t (read t 2) 6)
    (BindingLoop.slotValues original args (methodAt p method 2) receiver 0
      ((methodAt p method 2).toNat + (methodAt p method 3).toNat))
  stack : field t (read t 2) 7 = 0
  scratch : read t 19 = 0
  count : (read t 9).toNat + (methodAt p method 2).toNat + (methodAt p method 3).toNat + 1 = (read original 9).toNat
  previous : Preserved original t cap
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read t r = read original r

theorem enterReady_effect {p s : Array UInt64} {cap : Nat} {method args receiver caller lex : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (inputs : Inputs s cap args (methodAt p method 2) receiver)
    (callerType : Matches s cap 5 caller) (lexType : Matches s cap 5 lex)
    (budget : (methodAt p method 2).toNat + (methodAt p method 3).toNat + 1 ≤ (read s 9).toNat) :
    Effect p s (enterReady p s method args receiver caller lex) cap method args receiver caller lex := by
  let t := (BindingLoop.binding s args (methodAt p method 2) (methodAt p method 3) receiver).2
  have built := BindingLoop.binding_progress valid typed inputs budget
  have visits := BindingLoop.binding_index valid budget (args := args) (receiver := receiver)
  have before : (read t 9).toNat + (methodAt p method 2).toNat + (methodAt p method 3).toNat = (read s 9).toNat := by
    have count := built.count
    rw [visits] at count
    exact (Nat.add_assoc _ _ _).trans count
  have enough : (1 : UInt64) ≤ read t 9 := UInt64.le_iff_toNat_le.mpr (by change 1 ≤ (read t 9).toNat; omega)
  have values := BindingLoop.binding_values valid typed inputs budget
  have callerNow := matches_transfer built.previous (show (5 : UInt64) ≠ 0 by decide) callerType
  have lexNow := matches_transfer built.previous (show (5 : UInt64) ≠ 0 by decide) lexType
  let result := ActivationAllocation.publish (allocate t 5 method (methodAt p method 4) caller lex (read t 19) 0)
  have frame : ActivationAllocation.Effect t result cap method (methodAt p method 4) caller lex
      (BindingLoop.slotValues s args (methodAt p method 2) receiver 0
        ((methodAt p method 2).toNat + (methodAt p method 3).toNat)) :=
    ActivationAllocation.allocate_effect built.heap built.typed callerNow lexNow values enough
  rw [enterReady_eq]
  change Effect p s result cap method args receiver caller lex
  refine ⟨frame.heap, frame.typed, frame.handle, frame.last, frame.tag, frame.methodId,
    frame.entryPC, frame.callerLink, frame.lexicalLink, frame.slots, frame.stack, frame.scratch, ?_, ?_, ?_⟩
  · have after : (read result 9).toNat + 1 = (read t 9).toNat := frame.count
    omega
  · intro h handle allocated k bound
    have allocatedNow : field t h 0 ≠ 0 := by rw [built.previous h handle allocated 0 (by decide)]; exact allocated
    exact (frame.previous h handle allocatedNow k bound).trans (built.previous h handle allocated k bound)
  · intro r bound h2 h8 h9 h10 h13 h17 h19
    exact (frame.registers r bound h2 h8 h9 h10 h13 h17 h19).trans
      (built.registers r bound h8 h9 h10 h13 h17 h19)

end Project.Smalltalk.ActivationConstruction
