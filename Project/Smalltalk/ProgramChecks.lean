import Project.Smalltalk.ValidationLoop

namespace Project.Smalltalk.ProgramChecks
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

def shape (p : Array UInt64) : Bool :=
  let n := read p 0
  let m := read p 1
  let count := read p 2
  let entry := read p 3
  n > 0 && n ≤ 1048576 && m > 0 && m ≤ 1048576 &&
    count > 0 && count ≤ 1048576 && entry > 0 && entry ≤ m &&
    p.size.toUInt64 == 8 + 4 * n + 6 * m + 4 * count

def classCheck (p : Array UInt64) (c : UInt64) : Bool :=
  let parent := classAt p c 0
  let inherited := if parent == 0 then true else if parent < c then
    classAt p parent 2 ≤ classAt p c 2 else false
  parent < c && classAt p c 1 > 0 && classAt p c 1 ≤ read p 0 &&
    classAt p c 2 ≤ 1048576 && classAt p c 3 == 0 && inherited

def methodCheck (p : Array UInt64) (id : UInt64) : Bool :=
  methodAt p id 0 > 0 && methodAt p id 0 ≤ read p 0 && methodAt p id 2 > 0 &&
    methodAt p id 2 ≤ 1048576 && methodAt p id 3 ≤ 1048576 &&
    methodAt p id 4 < read p 2 && methodAt p id 5 ≤ 8

def tableCheck (p : Array UInt64) (i : UInt64) : Bool :=
  if i < read p 0 then classCheck p (i + 1) else methodCheck p (i - read p 0 + 1)

def canonicalClasses (p : Array UInt64) : Bool :=
  read p 4 > 0 && read p 4 ≤ read p 0 && read p 5 > 0 &&
    read p 5 ≤ read p 0 && read p 6 > 0 && read p 6 ≤ read p 0 &&
    read p 7 > 0 && read p 7 ≤ read p 0

def entryCheck (p : Array UInt64) : Bool := methodAt p (read p 3) 2 == 1 && methodAt p (read p 3) 1 != 0

theorem step_eq (p : Array UInt64) (i : UInt64) (ok : Bool) :
    (if i < read p 0 then
      let c := i + 1
      let parent := classAt p c 0
      let inherited := if parent == 0 then true else if parent < c then
        classAt p parent 2 ≤ classAt p c 2 else false
      ok && parent < c && classAt p c 1 > 0 && classAt p c 1 ≤ read p 0 &&
        classAt p c 2 ≤ 1048576 && classAt p c 3 == 0 && inherited
    else
      let id := i - read p 0 + 1
      ok && methodAt p id 0 > 0 && methodAt p id 0 ≤ read p 0 && methodAt p id 2 > 0 &&
        methodAt p id 2 ≤ 1048576 && methodAt p id 3 ≤ 1048576 &&
        methodAt p id 4 < read p 2 && methodAt p id 5 ≤ 8) = (ok && tableCheck p i) := by
  unfold tableCheck classCheck methodCheck
  split <;> simp only [Bool.and_assoc]

theorem programValid_eq {p : Array UInt64} (header : p.size.toUInt64 ≥ 8) :
    programValid p = (shape p && (if shape p then canonicalClasses p else false) &&
      LeanExe.loop (if shape p then read p 0 + read p 1 else 0) true
        (fun i ok => ok && tableCheck p i) && (if shape p then entryCheck p else false)) := by
  simp only [programValid, header, ite_true]
  simp only [shape, canonicalClasses, entryCheck, step_eq]
  rfl

theorem header_present {p : Array UInt64} (valid : programValid p = true) : p.size.toUInt64 ≥ 8 := by
  by_cases present : p.size.toUInt64 ≥ 8
  · exact present
  · simp [programValid, present, UInt64.lt_iff_toNat_lt] at valid

theorem checks {p : Array UInt64} (valid : programValid p = true) :
    shape p = true ∧ canonicalClasses p = true ∧
      (∀ i : UInt64, i < read p 0 + read p 1 → tableCheck p i = true) ∧ entryCheck p = true := by
  rw [programValid_eq (header_present valid)] at valid
  have pieces : shape p = true ∧ (if shape p then canonicalClasses p else false) = true ∧
      LeanExe.loop (if shape p then read p 0 + read p 1 else 0) true
        (fun i ok => ok && tableCheck p i) = true ∧ (if shape p then entryCheck p else false) = true := by
    simpa only [Bool.and_assoc, Bool.and_eq_true] using valid
  have shaped := pieces.1
  simp only [shaped, ite_true] at pieces
  exact ⟨shaped, pieces.2.1, (ValidationLoop.loop_checks _ _).mp pieces.2.2.1, pieces.2.2.2⟩

end Project.Smalltalk.ProgramChecks
