import Project.Smalltalk.BootConstruction
import Project.Smalltalk.BootDispatch
import Project.Smalltalk.TypedCollection
import Project.Smalltalk.PushReservation

namespace Project.Smalltalk.BootHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory

theorem bootValid_eq (p s : Array UInt64) :
    bootValid p s = if read (reserve s (BootBudget.need p)) 0 == 4 then reserve s (BootBudget.need p)
      else bootReady p (reserve s (BootBudget.need p)) := rfl

theorem bootValid_correct {p s : Array UInt64} {cap : Nat} (program : programValid p = true)
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4) :
    Heap.Valid (bootValid p s) cap ∧ PointerTypes.Valid (bootValid p s) cap ∧
      ((read (bootValid p s) 0 = 4 ∧ read (bootValid p s) 15 = 9) ∨
        (read (bootValid p s) 0 = read s 0 ∧
          BootConstruction.Effect p (reserve s (BootBudget.need p)) (bootValid p s) cap)) := by
  have reserved := Reservation.reserve_correct valid phase (BootBudget.need p)
  have reservedTyped := TypedCollection.reserve_typed valid typed phase (BootBudget.need p)
  rw [bootValid_eq]
  by_cases error : read (reserve s (BootBudget.need p)) 0 = 4
  · simp only [error, BEq.rfl, ite_true]
    exact ⟨reserved.1, reservedTyped, Or.inl ⟨True.intro, PushReservation.reserve_reason valid phase _ error⟩⟩
  · simp only [show (read (reserve s (BootBudget.need p)) 0 == 4) = false from beq_eq_false_iff_ne.mpr error,
      Bool.false_eq_true, ite_false]
    have room := UInt64.le_iff_toNat_le.mp (PushReservation.reserve_room valid phase (BootBudget.need p) error)
    rw [BootBudget.need_toNat program] at room
    have built := BootConstruction.bootReady_effect program reserved.1 reservedTyped room
    have samePhase : read (reserve s (BootBudget.need p)) 0 = read s 0 := by
      rcases reserved.2.2.2 with ready | failed
      · exact ready.1
      · exact False.elim (error failed.1)
    have after := built.registers 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨built.heap, built.typed, Or.inr ⟨after.trans samePhase, built⟩⟩

theorem boot_valid {p s : Array UInt64} {cap : Nat}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) :
    Heap.Valid (boot p s) cap ∧ PointerTypes.Valid (boot p s) cap := by
  cases branch : BootDispatch.rejected p s with
  | true =>
    rw [BootDispatch.boot_rejected p s branch]
    exact ⟨Heap.fail_valid valid 10, TypedCollection.fail_typed valid.1.1 typed 10⟩
  | false =>
    have conditions := BootDispatch.accepted branch
    rw [BootDispatch.boot_accepted p s branch]
    have checked := bootValid_correct conditions.1 valid typed (by rw [conditions.2.2]; decide)
    exact ⟨checked.1, checked.2.1⟩

theorem boot_init_valid (p : Array UInt64) (requested stress : UInt64) :
    Heap.Valid (boot p (init requested stress)) (InitializationBase.capacity requested).toNat ∧
      PointerTypes.Valid (boot p (init requested stress)) (InitializationBase.capacity requested).toNat :=
  boot_valid (InitializationFree.init_valid requested stress) (TypedCollection.init_typed requested stress)

theorem boot_init_correct {p : Array UInt64} (program : programValid p = true) (requested stress : UInt64) :
    Heap.Valid (boot p (init requested stress)) (InitializationBase.capacity requested).toNat ∧
      PointerTypes.Valid (boot p (init requested stress)) (InitializationBase.capacity requested).toNat ∧
      ((read (boot p (init requested stress)) 0 = 4 ∧ read (boot p (init requested stress)) 15 = 9) ∨
        (read (boot p (init requested stress)) 0 = 0 ∧
          BootConstruction.Effect p (reserve (init requested stress) (BootBudget.need p))
            (boot p (init requested stress)) (InitializationBase.capacity requested).toNat)) := by
  have current : read (init requested stress) 2 = 0 := by
    rw [InitializationGraph.init_register requested stress 2 (by decide)]
    simp
  have phase := InitializationFree.init_phase requested stress
  have good : BootDispatch.rejected p (init requested stress) = false := by
    simp only [BootDispatch.rejected, BootGuard.rejected, program, current, phase,
      Bool.not_true, bne_self_eq_false, Bool.false_or]
  rw [BootDispatch.boot_accepted p (init requested stress) good]
  have checked := bootValid_correct program (InitializationFree.init_valid requested stress)
    (TypedCollection.init_typed requested stress) (by rw [phase]; decide)
  rw [phase] at checked
  exact checked

end Project.Smalltalk.BootHeap
