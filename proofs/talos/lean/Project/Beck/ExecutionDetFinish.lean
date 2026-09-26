import Project.Beck.ExecutionDetStage

namespace Project.Beck.Execution

open Wasm Project.ProofKit

def determinantFinishScratch (result : UInt64) (scratch : DeterminantReadScratch) : DeterminantReadScratch := fun k =>
  if k.val = 50 then .i64 result else scratch k

set_option maxRecDepth 2048 in
theorem determinant_finish_shape : determinantLoop.drop 70 =
    [.localGet 42, .localSet 58] ++ determinantRead ++ determinantLoop.drop 117 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantFinish_exact (env : HostEnv Unit) (initial : Store Unit)
    (fuel matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailPointer result : UInt64)
    (width index : Nat) (matrix rows columns : Array UInt64) (scratch : DeterminantReadScratch)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer rows)
    (columnsAt : UInt64Array.At initial columnPointer columns)
    (nonempty : 0 < rows.size) (inside : index < columns.size) (countBound : columns.size ≤ 6)
    (widthFit : width < UInt64.size)
    (addressBound : rows[0].toNat * width + columns[index].toNat < matrix.size)
    (r19 : scratch 11 = .i64 tailOwner) (r20 : scratch 12 = .i64 tailPointer)
    (r42 : scratch 34 = .i64 result) (r45 : scratch 37 = .i64 index.toUInt64)
    (r46 : scratch 38 = .i64 columns.size.toUInt64) (r47 : scratch 39 = .i64 1)
    (Q : Assertion Unit)
    (next : ∀ scratch, Q (.Break 0 initial
      (determinantLoopFrame fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        tailOwner tailPointer result (index + 1) columns.size scratch))) :
    wp Project.Beck.«module» (determinantLoop.drop 70) Q initial
      (determinantReadFrame fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        index scratch []) env := by
  have indexGuard : ¬UInt64.ofNat index + 1 < UInt64.ofNat index :=
    CheckedNatAdd.guard_of_fits index 1 (by change index + 1 < 18446744073709551616; omega)
  have increment : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) :=
    (UInt64.ofNat_add index 1).symm
  have incrementGuard : ¬UInt64.ofNat (index + 1) < index.toUInt64 := by
    rw [← increment]
    exact indexGuard
  rw [determinant_finish_shape]
  simp only [List.cons_append, List.nil_append, List.append_assoc,
    determinantReadFrame, determinantParams]
  wp_fixed_frame_step
  wp_fixed_frame_step
  rw [r42]
  suffices prepared : wp Project.Beck.«module» (determinantRead ++ determinantLoop.drop 117) Q initial
    (determinantReadFrame fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
      index (determinantFinishScratch result scratch) []) env by
    simpa only [determinantReadFrame, determinantParams, determinantFinishScratch,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, r42] using prepared
  apply determinantRead_exact env initial fuel matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    width index matrix rows columns _ [] matrixAt rowsAt columnsAt nonempty inside widthFit addressBound
  by_cases zero : matrix[rows[0].toNat * width + columns[index].toNat] = 0
  all_goals
    simp only [determinantLoop, determinantOuter, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, determinantReadFrame, determinantParams, determinantReadScratch, determinantFinishScratch,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, r19, r20, r42, r45, r46, r47]
    repeat' ((try wp_fixed_frame [zero, indexGuard, increment, incrementGuard, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [List.take, List.drop, List.append_nil, increment]
    apply determinantLoopFrame_post initial _ fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer
      columnOwner columnPointer tailOwner tailPointer result (index + 1) columns.size Q next
    all_goals rfl

theorem determinantFinish_of_gets (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (fuel matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer tailOwner tailPointer result : UInt64)
    (width index : Nat) (matrix rows columns : Array UInt64)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer rows)
    (columnsAt : UInt64Array.At initial columnPointer columns)
    (nonempty : 0 < rows.size) (inside : index < columns.size) (countBound : columns.size ≤ 6)
    (widthFit : width < UInt64.size)
    (addressBound : rows[0].toNat * width + columns[index].toNat < matrix.size)
    (params : frame.params = determinantParams fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer)
    (locals : frame.locals.length = 52) (values : frame.values = [])
    (r19 : frame.get 19 = some (.i64 tailOwner)) (r20 : frame.get 20 = some (.i64 tailPointer))
    (r22 : frame.get 22 = some (.i64 index.toUInt64)) (r42 : frame.get 42 = some (.i64 result))
    (r45 : frame.get 45 = some (.i64 index.toUInt64)) (r46 : frame.get 46 = some (.i64 columns.size.toUInt64))
    (r47 : frame.get 47 = some (.i64 1))
    (Q : Assertion Unit)
    (next : ∀ scratch, Q (.Break 0 initial
      (determinantLoopFrame fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        tailOwner tailPointer result (index + 1) columns.size scratch))) :
    wp Project.Beck.«module» (determinantLoop.drop 70) Q initial frame env := by
  have paramsLength : frame.params.length = 8 := by simp [params, determinantParams]
  have frameEq := determinantReadFrame_reconstruct frame fuel width.toUInt64 matrixOwner matrixPointer
    rowOwner rowPointer columnOwner columnPointer index params locals r22
  rw [frameEq, values]
  exact determinantFinish_exact env initial fuel matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    tailOwner tailPointer result width index matrix rows columns (fun k => frame.locals[k.val]!)
    matrixAt rowsAt columnsAt nonempty inside countBound widthFit addressBound
    (determinant_local_read frame 11 _ paramsLength locals (by decide) r19)
    (determinant_local_read frame 12 _ paramsLength locals (by decide) r20)
    (determinant_local_read frame 34 _ paramsLength locals (by decide) r42)
    (determinant_local_read frame 37 _ paramsLength locals (by decide) r45)
    (determinant_local_read frame 38 _ paramsLength locals (by decide) r46)
    (determinant_local_read frame 39 _ paramsLength locals (by decide) r47) Q next

#print axioms determinantFinish_exact

end Project.Beck.Execution
