import Project.Drone.History

namespace Project.Drone.ParentBounds
open LeanExe.Examples.Drone

theorem predecessor_parent (r0 r1 : UInt64) (previous : Array UInt64) (target source : Nat)
    (h : source < stateCount) : (predecessor r0 r1 previous target source).parent.toNat < stateCount := by
  dsimp only [predecessor]
  split
  · change (UInt64.ofNat source).toNat < stateCount
    rw [UInt64.toNat_ofNat_of_lt' (by change source < 18446744073709551616; unfold stateCount at h; omega)]
    exact h
  · decide

theorem choose_parent (a b : Choice) (ha : a.parent.toNat < stateCount) (hb : b.parent.toNat < stateCount) :
    (choose a b).parent.toNat < stateCount := by
  unfold choose
  split <;> assumption

theorem scan_parent (count source : Nat) (r0 r1 : UInt64) (previous : Array UInt64)
    (target : Nat) (best : Choice) (hRange : source + count ≤ stateCount)
    (hBest : best.parent.toNat < stateCount) :
    (scanPredecessors count source r0 r1 previous target best).parent.toNat < stateCount := by
  induction count generalizing source best with
  | zero => exact hBest
  | succ count ih =>
    apply ih (source + 1) _ (by omega)
    exact choose_parent best _ hBest (predecessor_parent r0 r1 previous target source (by omega))

theorem best_parent (r0 r1 : UInt64) (previous : Array UInt64) (target : Nat) :
    (bestPredecessor stateCount r0 r1 previous target).parent.toNat < stateCount :=
  scan_parent _ _ _ _ _ _ _ (by omega) (by decide)

theorem advance_parent (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64) (state : Nat)
    (h : state < stateCount) : (advance r0 r1 last previous)[3 * state + 2]!.toNat < stateCount := by
  rw [Rows.advance_word _ _ _ _ state 2 h (by decide)]
  simp only [Rows.word, show ¬ (2 : Nat) = 0 by decide, show ¬ (2 : Nat) = 1 by decide, ↓reduceIte]
  unfold Rows.entry
  split
  · exact best_parent r0 r1 previous state
  · decide

theorem append_parent (count start : Nat) (layer history : Array UInt64)
    (hHistory : ∀ j, j < history.size → history[j]!.toNat < stateCount)
    (hLayer : ∀ j, j < count → layer[3 * (start + j) + 2]!.toNat < stateCount) :
    ∀ j, j < (appendParents count start layer history).size →
      (appendParents count start layer history)[j]!.toNat < stateCount := by
  intro j hj
  by_cases hOld : j < history.size
  · rw [History.appendParents_old _ _ _ _ j hOld]
    exact hHistory j hOld
  · have hOffset : j - history.size < count := by rw [History.appendParents_size] at hj; omega
    have hEq : history.size + (j - history.size) = j := by omega
    rw [← hEq, History.appendParents_new _ _ _ _ _ hOffset]
    exact hLayer _ hOffset

theorem buildHistory_parent (count index : Nat) (terrain previous history : Array UInt64)
    (hHistory : ∀ j, j < history.size → history[j]!.toNat < stateCount) :
    ∀ j, j < (buildHistory count index terrain previous history).size →
      (buildHistory count index terrain previous history)[j]!.toNat < stateCount := by
  induction count generalizing index previous history with
  | zero => exact hHistory
  | succ count ih =>
    apply ih
    apply append_parent _ _ _ _ hHistory
    intro j hj
    simpa only [Nat.zero_add] using advance_parent _ _ _ _ j hj

theorem computed_parent (terrain : Array UInt64) :
    ∀ j, j < (buildHistory (terrain.size - 1) 1 terrain initial #[]).size →
      (buildHistory (terrain.size - 1) 1 terrain initial #[])[j]!.toNat < stateCount :=
  buildHistory_parent _ _ _ _ _ (by simp)

#print axioms computed_parent
end Project.Drone.ParentBounds
