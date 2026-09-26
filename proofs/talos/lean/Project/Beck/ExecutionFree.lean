import Project.Beck.ExecutionFreeStep

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

theorem free_none (input : Input) (point : Point) (columns : Array UInt64)
    (absent : ∀ index < input.jobs, eligible point columns index = false) :
    freeColumn input point columns = input.jobs := by
  rw [FreeColumn.freeColumn_eq]
  have h : (List.range input.jobs).findSome? (FreeColumn.candidate point columns) = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro index member
    change (if eligible point columns index then some index else none) = none
    rw [absent index (List.mem_range.mp member)]
    rfl
  rw [h]
  rfl

theorem free_first (input : Input) (point : Point) (columns : Array UInt64) (index : Nat)
    (bounded : index < input.jobs)
    (absent : ∀ previous < index, eligible point columns previous = false)
    (present : eligible point columns index = true) :
    freeColumn input point columns = index := by
  rw [FreeColumn.freeColumn_eq]
  have missing : (List.range index).findSome? (FreeColumn.candidate point columns) = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro previous member
    change (if eligible point columns previous then some previous else none) = none
    rw [absent previous (List.mem_range.mp member)]
    rfl
  have found : (List.range (index + 1)).findSome? (FreeColumn.candidate point columns) = some index := by
    rw [List.range_succ, List.findSome?_append, missing]
    have good : FreeColumn.candidate point columns index = some index := by
      change (if eligible point columns index then some index else none) = some index
      rw [present]
      rfl
    simp [good]
  have initial : List.range (index + 1) <+: List.range input.jobs := by
    have take := List.take_prefix (index + 1) (List.range input.jobs)
    simpa only [List.take_range, Nat.min_eq_left (by omega : index + 1 ≤ input.jobs)] using take
  rw [initial.findSome?_eq_some found]
  rfl

def freeInv (initial : Store Unit) (input : Input) (point : Point) (columns : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index scratch,
    index ≤ input.jobs ∧ (∀ previous < index, eligible point columns previous = false) ∧
    frame = freeFrame input point inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer
      index false scratch

def freeDone (initial : Store Unit) (input : Input) (point : Point) (columns : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index found scratch,
    freeColumn input point columns = (if found then index else input.jobs) ∧
    frame = freeFrame input point inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer
      index found scratch

theorem freeLoop_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (columns : Array UInt64) (inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer : UInt64)
    (scratch : FreeScratch) (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (columnsArray : UInt64Array.At initial columnsPointer columns)
    (sizes : input.jobs ≤ point.numerators.size) (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ index found scratch, freeColumn input point columns = (if found then index else input.jobs) →
      wp «module» rest Q initial (freeFrame input point inputOwner inputPointer pointOwner pointPointer
        columnsOwner columnsPointer index found scratch) env) :
    wp «module» ([.block 0 0 [.loop 0 0 freeBody]] ++ rest) Q initial
      (freeFrame input point inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer
        0 false scratch) env := by
  have jobsFit : input.jobs < UInt64.size := lt_of_le_of_lt sizes pointArray.size_lt
  apply BlockLoop.program_spec «module» env initial _ freeBody
    (freeInv initial input point columns inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer)
    (freeDone initial input point columns inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer)
    (RangeFoldLoop.measure 39 input.jobs)
  · rintro store frame ⟨_, index, scratch, _, _, rfl⟩
    rfl
  · rintro store frame ⟨_, index, found, scratch, _, rfl⟩
    rfl
  · exact ⟨rfl, 0, scratch, by omega, by simp, rfl⟩
  · rintro store frame ⟨same, index, currentScratch, bounded, processed, rfl⟩
    subst store
    have indexFits : index < UInt64.size := lt_of_le_of_lt bounded jobsFit
    change wp «module» ([.localGet 39, .localGet 40, .geUI64, .br_if 1] ++ freeBody.drop 4)
      _ initial _ env
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, freeFrame,
      inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.length,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte, wp_geUI64_cons, wp_br_if_cons]
    by_cases last : index = input.jobs
    · subst index
      simp only [show input.jobs.toUInt64 ≤ input.jobs.toUInt64 from Nat.le_refl _, ↓reduceIte]
      change freeDone initial input point columns inputOwner inputPointer pointOwner pointPointer
        columnsOwner columnsPointer initial _
      exact ⟨rfl, _, false, currentScratch, free_none input point columns processed, rfl⟩
    · have less : index < input.jobs := by omega
      have guard : ¬input.jobs.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' jobsFit,
          UInt64.toNat_ofNat_of_lt' indexFits]
        omega
      simp only [ge_iff_le, guard, ↓reduceIte]
      apply freeStep_exact env initial input point columns inputOwner inputPointer pointOwner pointPointer
        columnsOwner columnsPointer index currentScratch pointArray columnsArray (lt_of_lt_of_le less sizes)
      · intro absent
        change freeInv initial input point columns inputOwner inputPointer pointOwner pointPointer
          columnsOwner columnsPointer initial _ ∧ _
        refine ⟨⟨rfl, index + 1, _, by omega, ?_, rfl⟩, ?_⟩
        · intro previous hp
          by_cases equal : previous = index
          · simpa [equal] using absent
          · exact processed previous (by omega)
        · simp only [RangeFoldLoop.measure, freeFrame, inputValues, pointValues,
            List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
            Locals.get, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte,
            UInt64.toNat_ofNat_of_lt' indexFits,
            UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
          omega
      · intro present
        change freeDone initial input point columns inputOwner inputPointer pointOwner pointPointer
          columnsOwner columnsPointer initial _
        exact ⟨rfl, index, true, _, free_first input point columns index less processed present, rfl⟩
  · rintro store frame ⟨rfl, index, found, finalScratch, correct, rfl⟩
    exact next index found finalScratch correct

set_option maxHeartbeats 600000 in
theorem freeColumn_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (columns : Array UInt64) (inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer : UInt64)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (columnsArray : UInt64Array.At initial columnsPointer columns)
    (sizes : input.jobs ≤ point.numerators.size) :
    TerminatesWith env «module» 28 initial
      ([.i64 columnsPointer, .i64 columnsOwner] ++ pointValues point pointOwner pointPointer ++
        inputValues input inputOwner inputPointer)
      (fun final values => final = initial ∧ values = [.i64 (freeColumn input point columns).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_
  change wp «module» func28 _ initial
    { params := (inputValues input inputOwner inputPointer).reverse ++
        (pointValues point pointOwner pointPointer).reverse ++ [.i64 columnsOwner, .i64 columnsPointer],
      locals := List.replicate 38 (.i64 0) } env
  simp only [func28]
  wp_fixed_frame [inputValues, pointValues]
  change wp «module» ([.block 0 0 [.loop 0 0 freeBody]] ++ func28.drop 13) _ initial
    (freeFrame input point inputOwner inputPointer pointOwner pointPointer columnsOwner columnsPointer
      0 false (fun _ => .i64 0)) env
  apply freeLoop_exact env initial input point columns inputOwner inputPointer pointOwner pointPointer
    columnsOwner columnsPointer _ pointArray columnsArray sizes
  intro index found scratch correct
  cases found <;>
    simp only [func28, List.drop, freeFrame, inputValues, pointValues, boolWord, Bool.false_eq_true, ↓reduceIte]
  all_goals
    repeat' ((try wp_fixed_frame [func28Def, correct]) <;> (refine wp_iff_cons rfl ?_; try simp))

#print axioms freeColumn_exact

end Project.Beck.Execution
