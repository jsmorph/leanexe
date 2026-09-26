import Project.Beck.ExecutionCountStep
import Project.ProofKit.BlockLoop
import Project.ProofKit.RangeFoldLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def countPrefix (input : Input) (point : Point) (category index : Nat) : Nat :=
  ∑ job ∈ Finset.range index, if counted input point category job then 1 else 0

theorem countPrefix_zero (input : Input) (point : Point) (category : Nat) :
    countPrefix input point category 0 = 0 := by simp [countPrefix]

theorem countPrefix_succ (input : Input) (point : Point) (category index : Nat) :
    countPrefix input point category (index + 1) =
      if counted input point category index then countPrefix input point category index + 1
      else countPrefix input point category index := by
  simp only [countPrefix, Finset.sum_range_succ]
  cases counted input point category index <;> simp

theorem countPrefix_le (input : Input) (point : Point) (category index : Nat) :
    countPrefix input point category index ≤ index := by
  induction index with
  | zero => simp [countPrefix_zero]
  | succ index ih =>
    rw [countPrefix_succ]
    split <;> omega

theorem countPrefix_total (input : Input) (point : Point) (category : Nat) :
    countPrefix input point category input.jobs = liveCount input point category := by
  rw [Counting.liveCount_sum, countPrefix, Finset.sum_range]
  rfl

def countInv (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index scratch, index ≤ input.jobs ∧
    frame = countFrame input point inputOwner inputPointer pointOwner pointPointer
      category index (countPrefix input point category index) scratch

def countDone (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ scratch,
    frame = countFrame input point inputOwner inputPointer pointOwner pointPointer
      category input.jobs (liveCount input point category) scratch

theorem countLoop_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat) (scratch : CountScratch)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (pointSize : input.jobs ≤ point.numerators.size)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (categoryBound : category < input.categories)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ scratch, wp «module» rest Q initial
      (countFrame input point inputOwner inputPointer pointOwner pointPointer category input.jobs
        (liveCount input point category) scratch) env) :
    wp «module» ([.block 0 0 [.loop 0 0 countBody]] ++ rest) Q initial
      (countFrame input point inputOwner inputPointer pointOwner pointPointer category 0 0 scratch) env := by
  have jobsFit : input.jobs < UInt64.size := lt_of_le_of_lt pointSize pointArray.size_lt
  apply BlockLoop.program_spec «module» env initial _ countBody
    (countInv initial input point inputOwner inputPointer pointOwner pointPointer category)
    (countDone initial input point inputOwner inputPointer pointOwner pointPointer category)
    (RangeFoldLoop.measure 27 input.jobs)
  · rintro store frame ⟨_, index, scratch, _, rfl⟩
    rfl
  · rintro store frame ⟨_, scratch, rfl⟩
    rfl
  · exact ⟨rfl, 0, scratch, by omega, by rw [countPrefix_zero]⟩
  · rintro store frame ⟨same, index, currentScratch, bounded, rfl⟩
    subst store
    have indexFit : index < UInt64.size := lt_of_le_of_lt bounded jobsFit
    change wp «module» ([.localGet 27, .localGet 28, .geUI64, .br_if 1] ++ countBody.drop 4)
      _ initial _ env
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, countFrame,
      inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.length,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte, wp_geUI64_cons, wp_br_if_cons]
    by_cases last : index = input.jobs
    · subst index
      simp only [show input.jobs.toUInt64 ≤ input.jobs.toUInt64 from Nat.le_refl _, ↓reduceIte]
      change countDone initial input point inputOwner inputPointer pointOwner pointPointer category initial _
      exact ⟨rfl, currentScratch, by rw [countPrefix_total]; rfl⟩
    · have less : index < input.jobs := by omega
      have guard : ¬input.jobs.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' jobsFit,
          UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [ge_iff_le, guard, ↓reduceIte]
      apply countStep_exact env initial input point inputOwner inputPointer pointOwner pointPointer category index
        (countPrefix input point category index) currentScratch pointArray inputArray pointSize inputSize
        jobs categories categoryBound less (countPrefix_le input point category index)
      change countInv initial input point inputOwner inputPointer pointOwner pointPointer category initial _ ∧ _
      refine ⟨⟨rfl, index + 1,
        countScratch input point pointOwner pointPointer category index (countPrefix input point category index)
          (frozen point index) (counted input point category index) currentScratch,
        by omega, ?_⟩, ?_⟩
      · rw [countPrefix_succ]
      · simp only [RangeFoldLoop.measure, countFrame, inputValues, pointValues,
          List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          Locals.get, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, ↓reduceIte,
          UInt64.toNat_ofNat_of_lt' indexFit,
          UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
        omega
  · rintro store frame ⟨rfl, finalScratch, rfl⟩
    exact next finalScratch

set_option maxHeartbeats 600000 in
theorem liveCount_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category : Nat)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (pointSize : input.jobs ≤ point.numerators.size)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (categoryBound : category < input.categories) :
    TerminatesWith env «module» 17 initial
      (.i64 category.toUInt64 :: pointValues point pointOwner pointPointer ++ inputValues input inputOwner inputPointer)
      (fun final values => final = initial ∧ values = [.i64 (liveCount input point category).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func17Def) rfl ?_
  change wp «module» func17 _ initial
    { params := (inputValues input inputOwner inputPointer).reverse ++
        (pointValues point pointOwner pointPointer).reverse ++ [.i64 category.toUInt64],
      locals := List.replicate 30 (.i64 0) } env
  simp only [func17]
  wp_fixed_frame [inputValues, pointValues]
  change wp «module» ([.block 0 0 [.loop 0 0 countBody]] ++ func17.drop 11) _ initial
    (countFrame input point inputOwner inputPointer pointOwner pointPointer category 0 0 (fun _ => .i64 0)) env
  apply countLoop_exact env initial input point inputOwner inputPointer pointOwner pointPointer category _
    pointArray inputArray pointSize inputSize jobs categories categoryBound
  intro scratch
  simp only [func17, List.drop, countFrame, inputValues, pointValues,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append]
  wp_fixed_frame [func17Def]
  simp

#print axioms liveCount_exact

end Project.Beck.Execution
