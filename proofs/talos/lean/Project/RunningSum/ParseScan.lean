import Project.RunningSum.Slices

namespace Project.RunningSum

open LeanExe.Examples.RunningSum (Decimal)

def parseBody (line : ByteArray) (i : Nat) (state : Option (Option Decimal) × Nat) :
    Id (ForInStep (Option (Option Decimal) × Nat)) :=
  if (line)[i]! < 48 || (line)[i]! > 57 then pure (.done (some none, state.2))
  else if i == state.2 && (line)[i]! == 48 then pure (.yield (none, state.2 + 1))
  else pure (.yield (none, state.2))

def parseScan (line : ByteArray) (cursor count first : Nat) : Option (Option Decimal) × Nat :=
  Id.run <| forIn (List.range' cursor count) (none, first) (parseBody line)

theorem parseScan_source (input : ByteArray) (cursor count first : Nat) :
    (forIn (List.range' cursor count) (none, first) (fun i (state : Option (Option Decimal) × Nat) =>
      if input[i]! < 48 || input[i]! > 57 then pure (ForInStep.done (some none, state.2))
      else if i == state.2 && input[i]! == 48 then pure (ForInStep.yield (none, state.2 + 1))
      else pure (ForInStep.yield (none, state.2))) : Id _) = parseScan input cursor count first := rfl

theorem parseScan_succ (line : ByteArray) (cursor count first : Nat) :
    parseScan line cursor (count + 1) first =
      if (line)[cursor]! < 48 || (line)[cursor]! > 57 then (some none, first)
      else parseScan line (cursor + 1) count
        (if cursor == first && (line)[cursor]! == 48 then first + 1 else first) := by
  simp only [parseScan, List.range'_succ, List.forIn_cons, parseBody]
  split_ifs <;> rfl

structure FirstAt (line : ByteArray) (start cursor first : Nat) : Prop where
  start_le : start ≤ first
  first_le : first ≤ cursor
  zero_before : ∀ i, start ≤ i → i < first → (line)[i]! = 48
  nonzero : first < cursor → (line)[first]! ≠ 48

theorem firstAt_step (line : ByteArray) (start cursor first : Nat)
    (h : FirstAt line start cursor first) :
    FirstAt line start (cursor + 1)
      (if cursor == first && (line)[cursor]! == 48 then first + 1 else first) := by
  split_ifs with hz
  · simp only [Bool.and_eq_true, beq_iff_eq] at hz
    refine ⟨Nat.le_trans h.start_le (Nat.le_succ _), by omega, ?_, by omega⟩
    intro i hi hif
    by_cases hlt : i < first
    · exact h.zero_before i hi hlt
    · have he : i = cursor := by omega
      simpa [he] using hz.2
  · refine ⟨h.start_le, by have := h.first_le; omega, h.zero_before, ?_⟩
    intro hlt
    by_cases hbefore : first < cursor
    · exact h.nonzero hbefore
    · have he : first = cursor := by have := h.first_le; omega
      intro hzero
      apply hz
      simp [← he, hzero]

theorem parseScan_valid (line : ByteArray) (start cursor count first : Nat)
    (h : FirstAt line start cursor first)
    (hd : ∀ i, cursor ≤ i → i < cursor + count →
      48 ≤ (line)[i]!.toNat ∧ (line)[i]!.toNat ≤ 57) :
    ∃ next, parseScan line cursor count first = (none, next) ∧
      FirstAt line start (cursor + count) next := by
  induction count generalizing cursor first with
  | zero => exact ⟨first, rfl, by simpa using h⟩
  | succ count ih =>
    have hbyte := hd cursor (by omega) (by omega)
    have hbad : (decide ((line)[cursor]! < 48) || decide ((line)[cursor]! > 57)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not,
        UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]
      norm_num
      omega
    rw [parseScan_succ, hbad]
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨next, he, hnext⟩ := ih (cursor + 1) _ (firstAt_step line start cursor first h)
      (by intro i hi hj; exact hd i (by omega) (by omega))
    exact ⟨next, he, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext⟩

end Project.RunningSum
