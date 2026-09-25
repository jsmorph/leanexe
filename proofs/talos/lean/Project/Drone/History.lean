import Project.Drone.Reconstruction

namespace Project.Drone.History
open LeanExe.Examples.Drone Planner

abbrev stops (terrain : Array UInt64) : Nat → Bool := fun i => i+1 == terrain.size
abbrev row (terrain : Array UInt64) (i : Nat) : Array UInt64 :=
  layers (floorAt terrain) (stops terrain) i

theorem validHeights_iff (count : Nat) (terrain : Array UInt64) :
    validHeights count terrain = true ↔ ∀ i, i < count → terrain[i]!.toNat ≤ 1000000 := by
  induction count with
  | zero => simp [validHeights]
  | succ count ih =>
    rw [validHeights]
    split
    · rename_i hh
      simp only [Bool.false_eq_true, false_iff]
      intro h
      have hc := h count (by omega)
      change (1000000:UInt64) < terrain[count]! at hh
      rw [UInt64.lt_iff_toNat_lt] at hh
      change 1000000 < terrain[count]!.toNat at hh
      omega
    · rename_i hh
      rw [ih]
      change ¬(1000000:UInt64) < terrain[count]! at hh
      rw [UInt64.lt_iff_toNat_lt] at hh
      change ¬1000000 < terrain[count]!.toNat at hh
      constructor
      · intro h i hi
        by_cases heq : i=count
        · subst i; omega
        · exact h i (by omega)
      · intro h i hi
        exact h i (by omega)

private theorem push_old (a : Array UInt64) (v : UInt64) (i : Nat) (hi : i < a.size) :
    (a.push v)[i]! = a[i]! := by
  rw [getElem!_pos (a.push v) i (by simp; omega), Array.getElem_push_lt hi, getElem!_pos a i hi]

private theorem push_new (a : Array UInt64) (v : UInt64) : (a.push v)[a.size]! = v := by
  simp [getElem!_pos]

theorem appendParents_size (count start : Nat) (layer history : Array UInt64) :
    (appendParents count start layer history).size = history.size+count := by
  induction count generalizing start history with
  | zero => simp [appendParents]
  | succ count ih => simp [appendParents, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem appendParents_old (count start : Nat) (layer history : Array UInt64)
    (i : Nat) (hi : i < history.size) :
    (appendParents count start layer history)[i]! = history[i]! := by
  induction count generalizing start history with
  | zero => rfl
  | succ count ih =>
    rw [appendParents, ih _ _ (by simp; omega), push_old _ _ _ hi]

theorem appendParents_new (count start : Nat) (layer history : Array UInt64)
    (i : Nat) (hi : i < count) :
    (appendParents count start layer history)[history.size+i]! = layer[3*(start+i)+2]! := by
  induction count generalizing start history i with
  | zero => omega
  | succ count ih =>
    rw [appendParents]
    by_cases hz : i=0
    · subst i
      simp only [Nat.add_zero]
      rw [appendParents_old _ _ _ _ _ (by simp), push_new]
    · have h := ih (start+1) (history.push layer[3*start+2]!) (i-1) (by omega)
      simp only [Array.size_push] at h
      have ha : history.size+1+(i-1) = history.size+i := by omega
      have hb : start+1+(i-1) = start+i := by omega
      simpa only [ha, hb] using h

def valid (terrain : Array UInt64) (count : Nat) (history : Array UInt64) : Prop :=
  history.size = count*stateCount ∧
  ∀ i state, 1 ≤ i → i ≤ count → state < stateCount →
    history[(i-1)*stateCount+state]! = (row terrain i)[3*state+2]!

theorem empty_valid (terrain : Array UInt64) : valid terrain 0 #[] := by
  constructor
  · rfl
  · intro i state hi0 hi1 hs
    omega

theorem append_valid (terrain : Array UInt64) (count : Nat) (history : Array UInt64)
    (h : valid terrain count history) :
    valid terrain (count+1) (appendParents stateCount 0 (row terrain (count+1)) history) := by
  refine ⟨?_, ?_⟩
  · rw [appendParents_size, h.1]
    dsimp [stateCount]
    omega
  · intro i state hi0 hi1 hs
    by_cases heq : i=count+1
    · subst i
      have hn := appendParents_new stateCount 0 (row terrain (count+1)) history state hs
      simpa only [h.1, Nat.add_sub_cancel, Nat.zero_add] using hn
    · have hindex : (i-1)*stateCount+state < history.size := by
        rw [h.1]; dsimp [stateCount] at *; omega
      rw [appendParents_old _ _ _ _ _ hindex]
      exact h.2 i state hi0 (by omega) hs

/-- The executable forward helper stores exactly the row solver's parents. -/
theorem buildHistory_valid (terrain : Array UInt64) (count done : Nat)
    (history : Array UInt64) (h : valid terrain done history) :
    valid terrain (done+count) (buildHistory count (done+1) terrain (row terrain done) history) := by
  induction count generalizing done history with
  | zero => simpa only [buildHistory, Nat.add_zero] using h
  | succ count ih =>
    have hnext := append_valid terrain done history h
    have hx := ih (done+1) (appendParents stateCount 0 (row terrain (done+1)) history) hnext
    have heq : done+1+count = done+(count+1) := by omega
    rw [heq] at hx
    simpa only [buildHistory, Nat.add_sub_cancel, row, layers, stops] using hx

theorem computed_history_valid (terrain : Array UInt64) :
    valid terrain (terrain.size-1) (buildHistory (terrain.size-1) 1 terrain initial #[]) := by
  simpa only [Nat.zero_add, row, layers] using buildHistory_valid terrain (terrain.size-1) 0 #[] (empty_valid terrain)

#print axioms validHeights_iff
#print axioms computed_history_valid
end Project.Drone.History
