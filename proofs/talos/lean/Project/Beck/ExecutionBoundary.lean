import Project.Beck.ExecutionBoundaryStep
import Project.ProofKit.BlockLoop
import Project.ProofKit.RangeFoldLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def boundaryPrefix (point : Point) (direction : Array UInt64) (count : Nat) : Boundary.Step :=
  (List.range count).foldl (fun old job => Boundary.select (Boundary.candidate point direction job) old) (0, 0)

theorem boundaryPrefix_zero (point : Point) (direction : Array UInt64) : boundaryPrefix point direction 0 = (0, 0) := rfl

theorem boundaryPrefix_succ (point : Point) (direction : Array UInt64) (index : Nat) :
    boundaryPrefix point direction (index + 1) =
      Boundary.select (Boundary.candidate point direction index) (boundaryPrefix point direction index) := by
  simp [boundaryPrefix, List.range_succ, List.foldl_append]

def boundaryInv (initial : Store Unit) (input : Input) (point : Point) (direction : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ index scratch, index ≤ input.jobs ∧
    frame = boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
      index (boundaryPrefix point direction index) scratch

def boundaryDone (initial : Store Unit) (input : Input) (point : Point) (direction : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64) : AssertionF Unit :=
  fun store frame => store = initial ∧ ∃ scratch,
    frame = boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
      input.jobs (boundaryStep input point direction) scratch

set_option maxRecDepth 2048 in
theorem boundaryLoop_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (direction : Array UInt64) (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64)
    (scratch : BoundaryScratch) (pointAt : UInt64Array.At initial pointPointer point.numerators)
    (directionAt : UInt64Array.At initial directionPointer direction)
    (pointSize : input.jobs ≤ point.numerators.size) (directionSize : input.jobs ≤ direction.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ scratch, wp Project.Beck.«module» rest Q initial
      (boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
        input.jobs (boundaryStep input point direction) scratch) env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 boundaryBody]] ++ rest) Q initial
      (boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer 0 (0, 0) scratch) env := by
  have jobsFit := directionSize.trans_lt directionAt.size_lt
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ boundaryBody
    (boundaryInv initial input point direction inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer)
    (boundaryDone initial input point direction inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer)
    (RangeFoldLoop.measure 44 input.jobs)
  · rintro store frame ⟨_, index, scratch, _, rfl⟩; rfl
  · rintro store frame ⟨_, scratch, rfl⟩; rfl
  · exact ⟨rfl, 0, scratch, by omega, rfl⟩
  · rintro store frame ⟨same, index, currentScratch, bounded, rfl⟩
    subst store
    have indexFit := bounded.trans_lt jobsFit
    change wp Project.Beck.«module» ([.localGet 44, .localGet 45, .geUI64, .br_if 1] ++ boundaryBody.drop 4)
      _ initial _ env
    simp only [List.cons_append, List.nil_append, wp_localGet_cons, Locals.get, boundaryFrame,
      boundary_locals_expanded, boundaryLocal, boundaryParams, inputValues, pointValues,
      List.reverse_cons, List.reverse_nil, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, wp_geUI64_cons, wp_br_if_cons]
    by_cases last : index = input.jobs
    · subst index
      simp only [show input.jobs.toUInt64 ≤ input.jobs.toUInt64 from Nat.le_refl _, reduceIte]
      change boundaryDone initial input point direction inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer initial _
      exact ⟨rfl, currentScratch, by rw [Boundary.boundaryStep_eq]; rfl⟩
    · have inside : index < input.jobs := by omega
      have guard : ¬input.jobs.toUInt64 ≤ index.toUInt64 := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' jobsFit, UInt64.toNat_ofNat_of_lt' indexFit]
        omega
      simp only [ge_iff_le, guard, reduceIte]
      apply boundaryIteration_exact env initial input point direction inputOwner inputPointer pointOwner pointPointer
        directionOwner directionPointer index (boundaryPrefix point direction index) currentScratch pointAt directionAt
        (inside.trans_le pointSize) (inside.trans_le directionSize)
      intro finalScratch
      change boundaryInv initial input point direction inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer initial _ ∧ _
      refine ⟨⟨rfl, index + 1, finalScratch, by omega, by rw [boundaryPrefix_succ]⟩, ?_⟩
      simp only [RangeFoldLoop.measure, boundaryFrame, boundary_locals_expanded, boundaryLocal, boundaryParams,
        inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
        Locals.get, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte,
        UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' (show index + 1 < UInt64.size by omega)]
      omega
  · rintro store frame ⟨rfl, finalScratch, rfl⟩
    exact next finalScratch

set_option maxRecDepth 2048 in
theorem boundaryStep_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (direction : Array UInt64) (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64)
    (pointAt : UInt64Array.At initial pointPointer point.numerators)
    (directionAt : UInt64Array.At initial directionPointer direction)
    (pointSize : input.jobs ≤ point.numerators.size) (directionSize : input.jobs ≤ direction.size) :
    TerminatesWith env Project.Beck.«module» 32 initial
      (boundaryParams input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer).reverse
      (fun final values => final = initial ∧ values = [.i64 (boundaryStep input point direction).2, .i64 (boundaryStep input point direction).1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func32Def) rfl ?_
  change wp Project.Beck.«module» func32 _ initial
    { params := boundaryParams input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
      locals := List.replicate 43 (.i64 0) } env
  simp only [func32, boundaryParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append]
  wp_fixed_frame
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 boundaryBody]] ++ func32.drop 15) _ initial
    (boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer 0 (0, 0) (fun _ => .i64 0)) env
  apply boundaryLoop_exact env initial input point direction inputOwner inputPointer pointOwner pointPointer directionOwner
    directionPointer _ pointAt directionAt pointSize directionSize
  intro scratch
  simp only [func32, List.drop, boundaryFrame, boundary_locals_expanded, boundaryLocal, boundaryParams,
    inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
  wp_fixed_frame [func32Def]
  simp

#print axioms boundaryStep_exact

end Project.Beck.Execution
