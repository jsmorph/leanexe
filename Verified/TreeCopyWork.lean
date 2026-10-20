import LeanExe.Pipeline.ReleaseTree

namespace Verified

open LeanExe.Pipeline

mutual
def nodeCopySteps : Node → Nat
  | .null => 0
  | .record slots => 1 + slotsCopySteps slots

def slotsCopySteps : List Slot → Nat
  | [] => 0
  | .word _ :: rest => 1 + slotsCopySteps rest
  | .child value :: rest => 1 + nodeCopySteps value + slotsCopySteps rest
end

inductive CopyWork where
  | done
  | current (slots : List Slot) (parents : List (List Slot))

def CopyWork.steps : CopyWork → Nat
  | .done => 0
  | .current slots parents =>
    1 + slotsCopySteps slots + (parents.map fun rest => 1 + slotsCopySteps rest).sum

def CopyWork.allocations : CopyWork → Nat
  | .done => 0
  | .current slots parents => slotsRecords slots + (parents.map slotsRecords).sum

inductive CopyWork.Step : CopyWork → CopyWork → Prop where
  | word {word rest parents} : Step (.current (.word word :: rest) parents) (.current rest parents)
  | null {rest parents} : Step (.current (.child .null :: rest) parents) (.current rest parents)
  | descend {children rest parents} :
      Step (.current (.child (.record children) :: rest) parents) (.current children (rest :: parents))
  | ascend {rest parents} : Step (.current [] (rest :: parents)) (.current rest parents)
  | finish : Step (.current [] []) .done

theorem CopyWork.Step.steps {before after : CopyWork} (h : Step before after) :
    before.steps = after.steps + 1 := by
  cases h <;> simp only [CopyWork.steps, slotsCopySteps, nodeCopySteps, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil] <;> omega

theorem CopyWork.Step.decreases {before after : CopyWork} (h : Step before after) :
    after.steps < before.steps := by rw [h.steps]; omega

def CopyWork.allocates : CopyWork → Nat
  | .current (.child (.record _) :: _) _ => 1
  | _ => 0

theorem CopyWork.Step.allocations {before after : CopyWork} (h : Step before after) :
    before.allocations = after.allocations + before.allocates := by
  cases h <;> simp only [CopyWork.allocations, CopyWork.allocates, slotsRecords,
    Node.records, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] <;> omega

theorem CopyWork.Step.allocation_bound {before after : CopyWork} (h : Step before after)
    {top top' cost limit : Nat} (hTop : top' ≤ top + cost * before.allocates)
    (hBudget : top + cost * before.allocations ≤ limit) :
    top' + cost * after.allocations ≤ limit := by
  rw [h.allocations, Nat.mul_add] at hBudget
  omega

theorem CopyWork.next (slots : List Slot) (parents : List (List Slot)) :
    ∃ after, Step (.current slots parents) after := by
  cases slots with
  | nil =>
    cases parents with
    | nil => exact ⟨.done, .finish⟩
    | cons rest parents => exact ⟨.current rest parents, .ascend⟩
  | cons slot rest =>
    cases slot with
    | word word => exact ⟨.current rest parents, .word⟩
    | child value =>
      cases value with
      | null => exact ⟨.current rest parents, .null⟩
      | record children => exact ⟨.current children (rest :: parents), .descend⟩

inductive CopyWork.Run : CopyWork → CopyWork → Nat → Prop where
  | refl {work} : Run work work 0
  | cons {before middle after spent} (first : Step before middle) (rest : Run middle after spent) :
      Run before after (before.allocates + spent)

theorem CopyWork.Run.allocations {before after : CopyWork} {spent : Nat}
    (h : Run before after spent) : before.allocations = after.allocations + spent := by
  induction h with
  | refl => omega
  | cons first rest ih => have := first.allocations; omega

theorem CopyWork.terminates (before : CopyWork) : ∃ spent, Run before .done spent := by
  refine (measure CopyWork.steps).wf.induction
    (C := fun work => ∃ spent, Run work .done spent) before ?_
  intro work ih
  cases work with
  | done => exact ⟨0, .refl⟩
  | current slots parents =>
    obtain ⟨after, hStep⟩ := next slots parents
    obtain ⟨spent, hRun⟩ := ih after hStep.decreases
    exact ⟨(CopyWork.current slots parents).allocates + spent, .cons hStep hRun⟩

theorem CopyWork.terminates_allocations (before : CopyWork) :
    Run before .done before.allocations := by
  obtain ⟨spent, hRun⟩ := before.terminates
  have hSpent : before.allocations = spent := by simpa [CopyWork.allocations] using hRun.allocations
  rw [hSpent]
  exact hRun

#print axioms CopyWork.Step.decreases
#print axioms CopyWork.Step.allocations
#print axioms CopyWork.Step.allocation_bound
#print axioms CopyWork.terminates_allocations

end Verified
