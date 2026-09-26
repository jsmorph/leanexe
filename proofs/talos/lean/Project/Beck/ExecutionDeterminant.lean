import Project.Beck.ExecutionDetOuterStep

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantCall_succ (env : HostEnv Unit) (order : Nat) (recursive : DeterminantCall env order) :
    DeterminantCall env (order + 1) := by
  intro initial heap width matrix rows columns matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    remaining pageLimit valid input matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget
  have fuelNonzero : (order + 1).toUInt64 ≠ 0 := by
    intro equal
    have := congrArg UInt64.toNat equal
    have bound := input.orderBound
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', UInt64.toNat_zero] at this
    omega
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_
  change wp Project.Beck.«module» func24 _ initial
    { params := determinantParams (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
        columnOwner columnPointer, locals := List.replicate 52 (.i64 0) } env
  simp only [func24, determinantParams]
  wp_fixed_frame
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 determinantOuter]] ++ func24.drop 9) _ initial
    (determinantOuterFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer false 0 (fun _ => .i64 0)) env
  let done : AssertionF Unit := fun store frame => ∃ finalHeap scratch,
    finalHeap.At store ∧ heap.Frame initial finalHeap store ∧
    OutputBudget store finalHeap remaining pageLimit Project.Beck.«module» ∧
    frame = determinantOuterFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer true (determinant (order + 1) width matrix rows columns) scratch
  let inv : AssertionF Unit := fun store frame =>
    (store = initial ∧ frame = determinantOuterFrame (order + 1).toUInt64 width.toUInt64 matrixOwner matrixPointer
      rowOwner rowPointer columnOwner columnPointer false 0 (fun _ => .i64 0)) ∨ done store frame
  let measure : Store Unit → Locals → Nat := fun _ frame => if frame.get 12 = some (.i64 0) then 1 else 0
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ determinantOuter inv done measure
  · rintro store frame (⟨_, rfl⟩ | ⟨finalHeap, scratch, _, _, _, rfl⟩) <;> rfl
  · rintro store frame ⟨finalHeap, scratch, _, _, _, rfl⟩; rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · rintro store frame (⟨same, rfl⟩ | ⟨finalHeap, scratch, finalValid, finalFrame, finalBudget, rfl⟩)
    · subst store
      change wp Project.Beck.«module»
        ([.localGet 0, .constI64 0, .eqI64, .eqz,
          .iff 0 1 [.localGet 12, .constI64 0, .eqI64] [.const 0] [] [.i32], .eqz, .br_if 1] ++
          determinantOuter.drop 7) _ initial _ env
      generalize bodyEq : determinantOuter.drop 7 = body
      simp only [List.cons_append, List.nil_append, determinantOuterFrame, determinant_locals_expanded,
        determinantOuterLocal, determinantParams, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, boolWord]
      wp_fixed_frame [fuelNonzero]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_left (by decide)]
      wp_fixed_frame [List.take, List.drop, List.append_nil]
      rw [← bodyEq]
      apply determinantOuterStep_exact env order recursive initial heap width matrix rows columns
        matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer (fun _ => .i64 0) remaining pageLimit valid
        input matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget
      intro final finalHeap finalValid finalFrame finalBudget finalScratch
      change inv final _ ∧ _
      refine ⟨Or.inr ⟨finalHeap, finalScratch, finalValid, finalFrame, finalBudget, rfl⟩, ?_⟩
      simp [measure, determinantOuterFrame, determinant_locals_expanded, determinantOuterLocal, determinantParams,
        Locals.get, boolWord]
    · change wp Project.Beck.«module»
        ([.localGet 0, .constI64 0, .eqI64, .eqz,
          .iff 0 1 [.localGet 12, .constI64 0, .eqI64] [.const 0] [] [.i32], .eqz, .br_if 1] ++
          determinantOuter.drop 7) _ store _ env
      generalize bodyEq : determinantOuter.drop 7 = body
      simp only [List.cons_append, List.nil_append, determinantOuterFrame, determinant_locals_expanded,
        determinantOuterLocal, determinantParams, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, boolWord]
      wp_fixed_frame [fuelNonzero]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_left (by decide)]
      wp_fixed_frame [List.take, List.drop, List.append_nil]
      exact ⟨finalHeap, scratch, finalValid, finalFrame, finalBudget, rfl⟩
  · rintro final frame ⟨finalHeap, scratch, finalValid, finalFrame, finalBudget, rfl⟩
    simp only [func24, List.drop, determinantOuterFrame, determinant_locals_expanded,
      determinantOuterLocal, determinantParams, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, boolWord]
    wp_fixed_frame
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_fixed_frame [List.take, List.drop, List.append_nil, func24Def]
    exact ⟨rfl, finalHeap, finalValid, finalFrame, finalBudget⟩

theorem determinant_exact (env : HostEnv Unit) (order : Nat) : DeterminantCall env order := by
  induction order with
  | zero => exact determinantCall_zero env
  | succ order ih => exact determinantCall_succ env order ih

#print axioms determinant_exact

end Project.Beck.Execution
