import Project.Beck.ExecutionBoundaryFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem boundaryIteration_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (direction : Array UInt64) (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64)
    (index : Nat) (step : Boundary.Step) (scratch : BoundaryScratch)
    (pointAt : UInt64Array.At initial pointPointer point.numerators)
    (directionAt : UInt64Array.At initial directionPointer direction)
    (pointBound : index < point.numerators.size) (directionBound : index < direction.size)
    (Q : Assertion Unit)
    (next : ∀ scratch, Q (.Break 0 initial
      (boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
        (index + 1) (Boundary.select (Boundary.candidate point direction index) step) scratch))) :
    wp Project.Beck.«module» (boundaryBody.drop 4) Q initial
      (boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer index step scratch) env := by
  have fit : index + 1 < UInt64.size := by have := directionAt.size_lt; omega
  have guard : ¬UInt64.ofNat index + 1 < UInt64.ofNat index := CheckedNatAdd.guard_of_fits index 1 fit
  have increment : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := (UInt64.ofNat_add index 1).symm
  have incrementGuard : ¬UInt64.ofNat (index + 1) < UInt64.ofNat index := by rw [← increment]; exact guard
  have mag := magnitude_exact env initial direction[index]
  have gapCall := gap_exact env initial point.denominator point.numerators[index] direction[index]
  by_cases speed : magnitude direction[index] = 0 <;> by_cases empty : step.2 = 0 <;>
    by_cases better : gap point.denominator point.numerators[index] direction[index] * step.2 < step.1 * magnitude direction[index]
  all_goals
    simp only [boundaryBody, func32, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop,
      boundaryFrame, boundary_locals_expanded, boundaryLocal, boundaryParams, inputValues, pointValues,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    repeat' (first
      | (refine wp_call_tw (mag.append_args rfl rfl rfl _) ?_; rintro final values ⟨out, rfl, same, rfl⟩; subst final
         simp only [List.cons_append, List.nil_append, List.append_nil])
      | (refine wp_call_tw (gapCall.append_args rfl rfl rfl _) ?_; rintro final values ⟨out, rfl, same, rfl⟩; subst final
         simp only [List.cons_append, List.nil_append, List.append_nil])
      | (refine CheckedArrayGet.checkedGetCore_spec 47 48 Project.Beck.«module» env initial _ directionPointer
          direction index _ rfl rfl rfl directionAt directionBound _ _ ?_)
      | (refine CheckedArrayGet.checkedGetCore_spec 47 48 Project.Beck.«module» env initial _ pointPointer
          point.numerators index _ rfl rfl rfl pointAt pointBound _ _ ?_)
      | wp_fixed_frame_step
      | ((first
          | rw [wp_eqI64_cons] | rw [wp_eqz_cons] | rw [wp_neI64_cons]
          | rw [wp_ltUI64_cons] | rw [wp_addI64_cons] | rw [wp_mulI64_cons] | rw [wp_const_cons]
          | rw [wp_localTee_cons] | rw [wp_br_if_cons] | rw [wp_br_cons] | rw [wp_nil]) <;>
        simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
          List.take, List.drop, List.append_nil, Nat.toUInt64, speed, empty, better, guard, increment, incrementGuard,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    repeat' ((try wp_fixed_frame [guard, increment, incrementGuard]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [guard, increment, incrementGuard]
    apply boundaryFrame_post initial _ input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
      (index + 1) (Boundary.select (Boundary.candidate point direction index) step) Q next
    all_goals first | rfl | simp [Locals.get, Boundary.select, Boundary.candidate, speed, empty, better,
      getElem!_pos point.numerators index pointBound, getElem!_pos direction index directionBound]

#print axioms boundaryIteration_exact

end Project.Beck.Execution
