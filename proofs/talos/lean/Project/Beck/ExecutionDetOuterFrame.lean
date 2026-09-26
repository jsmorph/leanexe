import Project.Beck.ExecutionDetLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit

def determinantOuterLocal (done : Bool) (result : UInt64) (scratch : DeterminantReadScratch) (k : Fin 52) : Value :=
  if k.val = 3 then .i64 result else if k.val = 4 then .i64 (boolWord done) else scratch k

def determinantOuterFrame (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (done : Bool) (result : UInt64) (scratch : DeterminantReadScratch) : Locals :=
  { params := determinantParams fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    locals := List.ofFn (determinantOuterLocal done result scratch) }

theorem determinantOuterFrame_reconstruct (frame : Locals)
    (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (done : Bool) (result : UInt64)
    (params : frame.params = determinantParams fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer)
    (locals : frame.locals.length = 52) (values : frame.values = [])
    (r11 : frame.get 11 = some (.i64 result)) (r12 : frame.get 12 = some (.i64 (boolWord done))) :
    frame = determinantOuterFrame fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
      done result (fun k => frame.locals[k.val]!) := by
  have paramsLength : frame.params.length = 8 := by simp [params, determinantParams]
  have resultRead := determinant_local_read frame 3 (.i64 result) paramsLength locals (by decide) r11
  have doneRead := determinant_local_read frame 4 (.i64 (boolWord done)) paramsLength locals (by decide) r12
  apply Frame.ext frame _ params _ values
  change frame.locals = List.ofFn (determinantOuterLocal done result (fun k => frame.locals[k.val]!))
  apply List.ext_getElem
  · simp [locals]
  · intro i hi hj
    rw [List.getElem_ofFn]
    simp only [determinantOuterLocal]
    split_ifs with resultIndex doneIndex
    · subst i; simpa only [getElem!_pos frame.locals 3 hi] using resultRead
    · subst i; simpa only [getElem!_pos frame.locals 4 hi] using doneRead
    · simp [getElem!_pos frame.locals i hi]

theorem determinantOuterFrame_post (store : Store Unit) (frame : Locals)
    (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (done : Bool) (result : UInt64) (Q : Assertion Unit)
    (next : ∀ scratch, Q (.Break 0 store
      (determinantOuterFrame fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer done result scratch)))
    (params : frame.params = determinantParams fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer)
    (locals : frame.locals.length = 52) (values : frame.values = [])
    (r11 : frame.get 11 = some (.i64 result)) (r12 : frame.get 12 = some (.i64 (boolWord done))) :
    Q (.Break 0 store frame) := by
  rw [determinantOuterFrame_reconstruct frame fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner
    columnPointer done result params locals values r11 r12]
  exact next _

end Project.Beck.Execution
