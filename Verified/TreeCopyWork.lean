import LeanExe.Pipeline.ReleaseTree
import Verified.AllocCost

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

mutual
/-- The growth of `top` for the copies of the records of a node, `allocCost (8 * w)` for a record
of `w` slots. -/
def nodeCopyCost : Node → Nat
  | .null => 0
  | .record slots => allocCost (8 * slots.length) + slotsCopyCost slots

def slotsCopyCost : List Slot → Nat
  | [] => 0
  | .word _ :: rest => slotsCopyCost rest
  | .child value :: rest => nodeCopyCost value + slotsCopyCost rest
end

inductive CopyWork where
  | done
  | current (slots : List Slot) (parents : List (List Slot))

def CopyWork.steps : CopyWork → Nat
  | .done => 0
  | .current slots parents =>
    1 + slotsCopySteps slots + (parents.map fun rest => 1 + slotsCopySteps rest).sum

/-- The growth of `top` for the copies of the records that remain. -/
def CopyWork.cost : CopyWork → Nat
  | .done => 0
  | .current slots parents => slotsCopyCost slots + (parents.map slotsCopyCost).sum

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

/-- The growth of `top` for the step from `work`: the copy of a record child's record. -/
def CopyWork.charge : CopyWork → Nat
  | .current (.child (.record children) :: _) _ => allocCost (8 * children.length)
  | _ => 0

theorem CopyWork.Step.cost {before after : CopyWork} (h : Step before after) :
    before.cost = after.cost + before.charge := by
  cases h <;> simp only [CopyWork.cost, CopyWork.charge, slotsCopyCost, nodeCopyCost,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] <;> omega

theorem CopyWork.Step.cost_bound {before after : CopyWork} (h : Step before after)
    {top top' limit : Nat} (hTop : top' ≤ top + before.charge)
    (hBudget : top + before.cost ≤ limit) :
    top' + after.cost ≤ limit := by
  rw [h.cost] at hBudget
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
      Run before after (before.charge + spent)

theorem CopyWork.Run.cost {before after : CopyWork} {spent : Nat}
    (h : Run before after spent) : before.cost = after.cost + spent := by
  induction h with
  | refl => omega
  | cons first rest ih => have := first.cost; omega

theorem CopyWork.terminates (before : CopyWork) : ∃ spent, Run before .done spent := by
  refine (measure CopyWork.steps).wf.induction
    (C := fun work => ∃ spent, Run work .done spent) before ?_
  intro work ih
  cases work with
  | done => exact ⟨0, .refl⟩
  | current slots parents =>
    obtain ⟨after, hStep⟩ := next slots parents
    obtain ⟨spent, hRun⟩ := ih after hStep.decreases
    exact ⟨(CopyWork.current slots parents).charge + spent, .cons hStep hRun⟩

theorem CopyWork.terminates_cost (before : CopyWork) :
    Run before .done before.cost := by
  obtain ⟨spent, hRun⟩ := before.terminates
  have hSpent : before.cost = spent := by simpa [CopyWork.cost] using hRun.cost
  rw [hSpent]
  exact hRun

#print axioms CopyWork.Step.decreases
#print axioms CopyWork.Step.cost
#print axioms CopyWork.Step.cost_bound
#print axioms CopyWork.terminates_cost

end Verified
