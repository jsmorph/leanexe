import Project.Runtime.FreeList

namespace Project.ProofKit.FreeListCount
open Project.Runtime

def fittingCount (need : UInt64) : List FreeNode → Nat
  | [] => 0
  | node :: rest => (if need ≤ node.capacity then 1 else 0) + fittingCount need rest

theorem fittingCount_append (need : UInt64) (left right : List FreeNode) :
    fittingCount need (left ++ right) = fittingCount need left + fittingCount need right := by
  induction left with
  | nil => simp [fittingCount]
  | cons node rest ih => simp [fittingCount, ih, Nat.add_assoc]

theorem fittingCount_none (previous need : UInt64) (nodes : List FreeNode)
    (hNone : takeFirstFitFrom previous need nodes = none) : fittingCount need nodes = 0 := by
  have hTake : takeFirstFit need nodes = none := by
    rw [← takeFirstFitFrom_project previous need nodes, hNone]
    rfl
  have hSmall := (takeFirstFit_none_iff need nodes).mp hTake
  clear hNone hTake
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    have hNode := hSmall node List.mem_cons_self
    have hNot : ¬need ≤ node.capacity := by
      simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
      omega
    simp only [fittingCount, hNot, ite_false, Nat.zero_add]
    exact ih (fun current hCurrent => hSmall current (List.mem_cons_of_mem node hCurrent))

theorem fittingCount_some (previous need : UInt64) (nodes : List FreeNode)
    (choice : FreeChoice) (hTake : takeFirstFitFrom previous need nodes = some choice) :
    fittingCount need choice.remaining + 1 = fittingCount need nodes := by
  obtain ⟨skipped, tail, hNodes, _, _, hRemaining, _⟩ := takeFirstFitFrom_some_decompose hTake
  have hFit := takeFirstFitFrom_some_capacity hTake
  simp [hNodes, hRemaining, fittingCount_append, fittingCount, hFit, Nat.add_comm,
    Nat.add_left_comm]

#print axioms fittingCount_append
#print axioms fittingCount_none
#print axioms fittingCount_some

end Project.ProofKit.FreeListCount
