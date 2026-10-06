import Project.Smalltalk.BindingPreservation

namespace Project.Smalltalk.ArgumentTransfer
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Traversal
open Project.Smalltalk.Reachability Project.Smalltalk.BindingPreservation

def Payload (s t : Array UInt64) : Prop :=
  ∀ h, Reachable s h → field s h 0 = 7 → ∀ k : UInt64, k.toNat < 8 → k ≠ 1 → field t h k = field s h k

theorem follow_transfer {s t : Array UInt64} {cap : Nat} {head : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap) (after : Shape t cap)
    (live : Live s head) (arguments : Matches s cap 7 head) (same : Payload s t) (n : Nat) :
    follow t 7 3 n head = follow s 7 3 n head := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [follow, ih]
    have matching := ArgumentLinks.follow_typed valid.1 typed arguments n
    rcases matching with zero | cell
    · rw [zero]; simp [hop, kind]
    · have tag : kind s (follow s 7 3 n head) = 7 := (kind_eq_field valid.1 cell.1).trans cell.2
      have followed := follow_live valid live (show (7 : UInt64) ≠ 0 by decide)
        (show (3 : UInt64).toNat < 8 by decide) (by simp [PointerField]) n
      have reached := live_reached followed (by decide) tag
      have tagAfter : kind t (follow s 7 3 n head) = 7 := by
        rw [kind_eq_field after cell.1, same _ reached cell.2 0 (by decide) (by decide), cell.2]
      simp only [hop, tag, tagAfter, ite_true]
      exact same _ reached cell.2 3 (by decide) (by decide)

theorem walk_transfer {s t : Array UInt64} {cap : Nat} {head : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap) (after : Shape t cap)
    (live : Live s head) (arguments : Matches s cap 7 head) (same : Payload s t) (count : UInt64) :
    walk t head count = walk s head count := by
  have capacity : read t 14 = read s 14 := UInt64.toNat_inj.mp (after.2.2.2.trans valid.1.2.2.2.symm)
  rw [walk_eq_follow, walk_eq_follow, capacity]
  exact follow_transfer valid typed after live arguments same _

theorem matches_transfer {s t : Array UInt64} {cap : Nat} {head : UInt64}
    (valid : Graph.Valid s cap) (live : Live s head) (arguments : Matches s cap 7 head)
    (same : Payload s t) : Matches t cap 7 head := by
  rcases arguments with zero | cell
  · exact Or.inl zero
  · have tag : kind s head = 7 := (kind_eq_field valid.1 cell.1).trans cell.2
    have reached := live_reached live (by decide) tag
    exact Or.inr ⟨cell.1, (same head reached cell.2 0 (by decide) (by decide)).trans cell.2⟩

theorem inputs_transfer {s t : Array UInt64} {cap : Nat} {args arity receiver : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap) (after : Shape t cap)
    (live : Live s args) (inputs : Inputs s cap args arity receiver) (same : Payload s t)
    (receiverValue : HeapWrite.Value t cap receiver) : Inputs t cap args arity receiver := by
  refine ⟨matches_transfer valid live inputs.argsTyped same, receiverValue, ?_⟩
  intro depth within
  rw [walk_transfer valid typed after live inputs.argsTyped same]
  have cell := inputs.arguments depth within
  have walked := walk_live valid live depth
  have tag : kind s (walk s args depth) = 7 := (kind_eq_field valid.1 cell.1).trans cell.2
  have reached := live_reached walked (by decide) tag
  exact ⟨cell.1, (same _ reached cell.2 0 (by decide) (by decide)).trans cell.2⟩

theorem slotValue_transfer {s t : Array UInt64} {cap : Nat} {args arity receiver : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap) (after : Shape t cap)
    (live : Live s args) (inputs : Inputs s cap args arity receiver) (same : Payload s t) (index : UInt64) :
    ArgumentBinding.slotValue t args arity receiver index = ArgumentBinding.slotValue s args arity receiver index := by
  unfold ArgumentBinding.slotValue
  by_cases zero : index = 0
  · simp only [zero, BEq.rfl, ite_true]
  · simp only [show (index == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
    by_cases argument : index < arity
    · simp only [argument, ite_true]
      rw [walk_transfer valid typed after live inputs.argsTyped same]
      have cell := BindingPreservation.selected_argument inputs zero argument
      have walked := walk_live valid live (arity - 1 - index)
      have tag : kind s (walk s args (arity - 1 - index)) = 7 := (kind_eq_field valid.1 cell.1).trans cell.2
      exact same _ (live_reached walked (by decide) tag) cell.2 2 (by decide) (by decide)
    · simp only [argument, ite_false]

end Project.Smalltalk.ArgumentTransfer
