import Project.Beck.ExecutionDetState

namespace Project.Beck.Execution

open Wasm Project.ProofKit

theorem determinant_locals_expanded (f : Fin 52 → Value) : List.ofFn f =
    [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9,
      f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19,
      f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29,
      f 30, f 31, f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39,
      f 40, f 41, f 42, f 43, f 44, f 45, f 46, f 47, f 48, f 49,
      f 50, f 51] := by rfl

def determinantLoopLocal (tailOwner tailPointer acc : UInt64) (index count : Nat)
    (scratch : DeterminantReadScratch) (k : Fin 52) : Value :=
  if k.val = 11 then .i64 tailOwner
  else if k.val = 12 then .i64 tailPointer
  else if k.val = 13 then .i64 acc
  else if k.val = 37 then .i64 index.toUInt64
  else if k.val = 38 then .i64 count.toUInt64
  else if k.val = 39 then .i64 1
  else scratch k

def determinantLoopFrame (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    tailOwner tailPointer acc : UInt64) (index count : Nat) (scratch : DeterminantReadScratch) : Locals :=
  { params := determinantParams fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    locals := List.ofFn (determinantLoopLocal tailOwner tailPointer acc index count scratch) }

theorem determinant_local_read (frame : Locals) (index : Nat) (value : Value)
    (params : frame.params.length = 8) (locals : frame.locals.length = 52)
    (inside : index < 52) (read : frame.get (index + 8) = some value) : frame.locals[index]! = value := by
  have indexBound : index < frame.locals.length := by omega
  have read' : frame.locals[index]? = some value := by
    simpa [Locals.get, params, locals, show ¬index + 8 < 8 by omega,
      show index + 8 < 8 + 52 by omega, Nat.add_sub_cancel] using read
  simpa only [getElem?_pos frame.locals index indexBound, getElem!_pos frame.locals index indexBound,
    Option.some.injEq] using read'

theorem determinantLoopFrame_reconstruct (frame : Locals)
    (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
      tailOwner tailPointer acc : UInt64) (index count : Nat)
    (params : frame.params = determinantParams fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer)
    (locals : frame.locals.length = 52) (values : frame.values = [])
    (tailOwnerRead : frame.get 19 = some (.i64 tailOwner))
    (tailPointerRead : frame.get 20 = some (.i64 tailPointer))
    (accRead : frame.get 21 = some (.i64 acc))
    (indexRead : frame.get 45 = some (.i64 index.toUInt64))
    (countRead : frame.get 46 = some (.i64 count.toUInt64))
    (stepRead : frame.get 47 = some (.i64 1)) :
    frame = determinantLoopFrame fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
      tailOwner tailPointer acc index count (fun k => frame.locals[k.val]!) := by
  have paramsLength : frame.params.length = 8 := by simp [params, determinantParams]
  have r19 := determinant_local_read frame 11 (.i64 tailOwner) paramsLength locals (by decide) tailOwnerRead
  have r20 := determinant_local_read frame 12 (.i64 tailPointer) paramsLength locals (by decide) tailPointerRead
  have r21 := determinant_local_read frame 13 (.i64 acc) paramsLength locals (by decide) accRead
  have r45 := determinant_local_read frame 37 (.i64 index.toUInt64) paramsLength locals (by decide) indexRead
  have r46 := determinant_local_read frame 38 (.i64 count.toUInt64) paramsLength locals (by decide) countRead
  have r47 := determinant_local_read frame 39 (.i64 1) paramsLength locals (by decide) stepRead
  apply Frame.ext frame _ params _ values
  change frame.locals = List.ofFn (determinantLoopLocal tailOwner tailPointer acc index count
    (fun k => frame.locals[k.val]!))
  apply List.ext_getElem
  · simp [locals]
  · intro i hi hj
    rw [List.getElem_ofFn]
    simp only [determinantLoopLocal]
    split_ifs with h11 h12 h13 h37 h38 h39
    · subst i; simpa only [getElem!_pos frame.locals 11 hi] using r19
    · subst i; simpa only [getElem!_pos frame.locals 12 hi] using r20
    · subst i; simpa only [getElem!_pos frame.locals 13 hi] using r21
    · subst i; simpa only [getElem!_pos frame.locals 37 hi] using r45
    · subst i; simpa only [getElem!_pos frame.locals 38 hi] using r46
    · subst i; simpa only [getElem!_pos frame.locals 39 hi] using r47
    · simp [getElem!_pos frame.locals i hi]

#print axioms determinantLoopFrame_reconstruct

end Project.Beck.Execution
