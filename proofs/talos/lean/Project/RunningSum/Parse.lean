import Project.RunningSum.ParseScan

namespace Project.RunningSum

open LeanExe.Examples.RunningSum (Decimal parse)

def lineEnd (line : ByteArray) : Nat :=
  if line.size > 0 && (line)[line.size - 1]! == 13 then line.size - 1 else line.size

def lineStart (line : ByteArray) : Nat :=
  if lineEnd line > 0 && ((line)[0]! == 43 || (line)[0]! == 45) then 1 else 0

def ValidLine (line : ByteArray) : Prop :=
  lineStart line < lineEnd line ∧ ∀ i, lineStart line ≤ i → i < lineEnd line →
    48 ≤ (line)[i]!.toNat ∧ (line)[i]!.toNat ≤ 57

def lineInteger (line : ByteArray) : Int :=
  let value := magnitude (line.extract (lineStart line) (lineEnd line))
  if (line)[0]! == 45 then -(value : Int) else value

theorem lineEnd_le (line : ByteArray) : lineEnd line ≤ line.size := by
  unfold lineEnd
  split_ifs <;> omega

theorem parse_eq (line : ByteArray) :
    parse line =
      if lineStart line == lineEnd line then none else
      let state := parseScan line (lineStart line) (lineEnd line - lineStart line) (lineStart line)
      match state.1 with
      | some value => value
      | none => some ⟨(line)[0]! == 45 && state.2 < lineEnd line, line.extract state.2 (lineEnd line)⟩ := by
  simp only [parse, lineStart, lineEnd, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one, parseScan,
    Id.run, bind, pure]
  unfold parseBody
  simp only [pure]
  congr 1
  split <;> simp_all

theorem parse_valid (line : ByteArray) (h : ValidLine line) :
    ∃ value, parse line = some value ∧ Canonical value.digits ∧ integer value = lineInteger line := by
  have hinit : FirstAt line (lineStart line) (lineStart line) (lineStart line) :=
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨first, hscan, hf⟩ := parseScan_valid line (lineStart line) (lineStart line)
    (lineEnd line - lineStart line) (lineStart line) hinit (by
      intro i hi hj
      exact h.2 i hi (by omega))
  have hend : lineStart line + (lineEnd line - lineStart line) = lineEnd line := by
    have := h.1
    omega
  rw [hend] at hf
  rw [parse_eq]
  have hne : (lineStart line == lineEnd line) = false := by
    simp only [beq_eq_false_iff_ne]
    have := h.1
    omega
  simp only [hne, Bool.false_eq_true, ite_false, hscan]
  refine ⟨_, rfl, ⟨?_, ?_⟩, ?_⟩
  · apply extract_valid line first (lineEnd line) (lineEnd_le line)
    intro i hi hj
    exact h.2 i (by have := hf.start_le; omega) hj
  · simp only [ByteArray.size_extract, Nat.min_eq_left (lineEnd_le line)]
    by_cases he : first = lineEnd line
    · left
      omega
    · right
      have hlt : first < lineEnd line := by have := hf.first_le; omega
      rw [extract_byte line first (lineEnd line) 0 (lineEnd_le line) (by omega), Nat.add_zero]
      have hd := h.2 first hf.start_le hlt
      have hnz := hf.nonzero hlt
      have hnz' : (line)[first]!.toNat ≠ 48 := fun he => hnz (UInt8.toNat.inj he)
      omega
  · have he := drop_leading_zeros line (lineStart line) first (lineEnd line)
      hf.start_le hf.first_le (lineEnd_le line) hf.zero_before
    simp only [integer, lineInteger]
    by_cases hlt : first < lineEnd line
    · simp only [hlt, decide_true, Bool.and_true, he]
    · have hz : first = lineEnd line := by have := hf.first_le; omega
      have hv : magnitude (line.extract first (lineEnd line)) = 0 := by
        simp [hz, magnitude, lowValue]
      rw [← he]
      simp [hv]

#print axioms parse_valid

end Project.RunningSum
