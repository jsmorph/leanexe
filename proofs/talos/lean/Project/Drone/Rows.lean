import Project.Drone.Selection

namespace Project.Drone.Rows
open LeanExe.Examples.Drone Selection

def entry (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64) (target : Nat) : Choice :=
  if !last || target == 0 then bestPredecessor stateCount r0 r1 previous target else unreachable

def word (choice : Choice) (field : Nat) : UInt64 :=
  if field = 0 then choice.time else if field = 1 then choice.excess else choice.parent

def pack (row : Array UInt64) (choice : Choice) : Array UInt64 :=
  ((row.push choice.time).push choice.excess).push choice.parent

private theorem push_old (row : Array UInt64) (w : UInt64) (i : Nat) (hi : i < row.size) :
    (row.push w)[i]! = row[i]! := by
  rw [getElem!_pos (row.push w) i (by simp <;> omega), Array.getElem_push_lt hi, getElem!_pos row i hi]

private theorem push_new (row : Array UInt64) (w : UInt64) :
    (row.push w)[row.size]! = w := by
  simp [getElem!_pos]

theorem pack_size (row : Array UInt64) (choice : Choice) :
    (pack row choice).size = row.size+3 := by simp [pack]

theorem pack_old (row : Array UInt64) (choice : Choice) (i : Nat) (hi : i < row.size) :
    (pack row choice)[i]! = row[i]! := by
  unfold pack
  rw [push_old _ _ _ (by simp <;> omega), push_old _ _ _ (by simp <;> omega), push_old _ _ _ hi]

theorem pack_new (row : Array UInt64) (choice : Choice) (field : Nat) (hf : field < 3) :
    (pack row choice)[row.size+field]! = word choice field := by
  have h : field=0 ∨ field=1 ∨ field=2 := by omega
  rcases h with h|h|h <;> subst field
  · change (((row.push choice.time).push choice.excess).push choice.parent)[row.size]! = choice.time
    rw [push_old _ _ _ (by simp <;> omega), push_old _ _ _ (by simp <;> omega), push_new]
  · change (((row.push choice.time).push choice.excess).push choice.parent)[row.size+1]! = choice.excess
    rw [push_old _ _ _ (by simp <;> omega)]
    simpa only [Array.size_push] using push_new (row.push choice.time) choice.excess
  · change (((row.push choice.time).push choice.excess).push choice.parent)[row.size+2]! = choice.parent
    simpa only [Array.size_push, Nat.add_assoc] using
      push_new ((row.push choice.time).push choice.excess) choice.parent

/-- Later states never overwrite words already placed in a DP row. -/
theorem advanceLoop_old (count target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previous row : Array UInt64) (i : Nat) (hi : i < row.size) :
    (advanceLoop count target r0 r1 last previous row)[i]! = row[i]! := by
  induction count generalizing target row with
  | zero => rfl
  | succ count ih =>
    change (advanceLoop count (target+1) r0 r1 last previous (pack row (entry r0 r1 last previous target)))[i]! = _
    rw [ih _ _ (by rw [pack_size]; omega), pack_old row _ i hi]

/-- Every packed field is exactly the selected choice for that target state. -/
theorem advanceLoop_new (count start : Nat) (r0 r1 : UInt64) (last : Bool)
    (previous row : Array UInt64) (target field : Nat)
    (ht : target < count) (hf : field < 3) :
    (advanceLoop count start r0 r1 last previous row)[row.size+3*target+field]! =
      word (entry r0 r1 last previous (start+target)) field := by
  induction count generalizing start row target with
  | zero => omega
  | succ count ih =>
    change (advanceLoop count (start+1) r0 r1 last previous (pack row (entry r0 r1 last previous start)))[row.size+3*target+field]! = _
    by_cases hzero : target=0
    · subst target
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [advanceLoop_old count (start+1) r0 r1 last previous _ _ (by rw [pack_size]; omega)]
      exact pack_new row _ field hf
    · have h := ih (start+1) (pack row (entry r0 r1 last previous start)) (target-1) (by omega)
      rw [pack_size] at h
      have heq : row.size+3+3*(target-1)+field = row.size+3*target+field := by omega
      have heq' : start+1+(target-1) = start+target := by omega
      simpa only [heq, heq'] using h

theorem advance_word (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64)
    (target field : Nat) (ht : target < stateCount) (hf : field < 3) :
    (advance r0 r1 last previous)[3*target+field]! = word (entry r0 r1 last previous target) field := by
  simpa only [advance, Array.size_empty, Nat.zero_add] using
    advanceLoop_new stateCount 0 r0 r1 last previous #[] target field ht hf

#print axioms advance_word
end Project.Drone.Rows
