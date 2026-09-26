import Project.Beck.ExecutionMatrixFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def matrixRowLocal (input : Input) (category index : Nat) (pointer initialOwner : UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) (k : Fin 87) : Value :=
  if h : k.val < 63 then matrixRowSaved input category index pointer saved ⟨k.val, h⟩
  else if h' : k.val < 78 then .i64 (tail ⟨k.val - 63, by omega⟩)
  else matrixRowAfter initialOwner after ⟨k.val - 78, by omega⟩

set_option maxRecDepth 2048 in
theorem matrixRowFrame_locals (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category index : Nat) (pointer initialOwner : UInt64) (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) :
    (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category index pointer initialOwner saved tail after).locals =
      List.ofFn (matrixRowLocal input category index pointer initialOwner saved tail after) := rfl

theorem matrix_local_read (frame : Locals) (index : Nat) (value : Value)
    (params : frame.params.length = 9) (locals : frame.locals.length = 87)
    (inside : index < 87) (read : frame.get (index + 9) = some value) : frame.locals[index]! = value := by
  have indexBound : index < frame.locals.length := by omega
  have read' : frame.locals[index]? = some value := by
    simpa [Locals.get, params, locals, show ¬index + 9 < 9 by omega,
      show index + 9 < 9 + 87 by omega, Nat.add_sub_cancel] using read
  simpa only [getElem?_pos frame.locals index indexBound, getElem!_pos frame.locals index indexBound,
    Option.some.injEq] using read'

set_option maxHeartbeats 1000000 in
theorem matrixRowFrame_reconstruct (frame : Locals) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category index : Nat)
    (pointer initialOwner : UInt64) (tail : MatrixTail)
    (params : frame.params = matrixParams input point inputOwner inputPointer pointOwner pointPointer)
    (locals : frame.locals.length = 87) (values : frame.values = [])
    (r14 : frame.get 14 = some (.i64 category.toUInt64))
    (r27 : frame.get 27 = some (.i64 pointer)) (r28 : frame.get 28 = some (.i64 pointer))
    (r69 : frame.get 69 = some (.i64 index.toUInt64))
    (r70 : frame.get 70 = some (.i64 input.jobs.toUInt64)) (r71 : frame.get 71 = some (.i64 1))
    (r91 : frame.get 91 = some (.i64 initialOwner))
    (tailReads : ∀ k : Fin 15, frame.get (k.val + 72) = some (.i64 (tail k))) :
    frame = matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category index pointer initialOwner
      (fun k => frame.locals[k.val]!) tail (fun k => frame.locals[k.val + 78]!) := by
  have paramsLength : frame.params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  have a := matrix_local_read frame 5 (.i64 category.toUInt64) paramsLength locals (by decide) r14
  have b := matrix_local_read frame 18 (.i64 pointer) paramsLength locals (by decide) r27
  have c := matrix_local_read frame 19 (.i64 pointer) paramsLength locals (by decide) r28
  have d := matrix_local_read frame 60 (.i64 index.toUInt64) paramsLength locals (by decide) r69
  have e := matrix_local_read frame 61 (.i64 input.jobs.toUInt64) paramsLength locals (by decide) r70
  have f := matrix_local_read frame 62 (.i64 1) paramsLength locals (by decide) r71
  have g := matrix_local_read frame 82 (.i64 initialOwner) paramsLength locals (by decide) r91
  apply Frame.ext frame _ params _ values
  rw [matrixRowFrame_locals]
  apply List.ext_getElem
  · simp [locals]
  · intro i hi hj
    rw [List.getElem_ofFn]
    simp only [matrixRowLocal]
    split_ifs with lower upper
    · by_cases h5 : i = 5
      · subst i; simpa only [matrixRowSaved, getElem!_pos frame.locals 5 hi] using a
      by_cases h18 : i = 18
      · subst i; simpa only [matrixRowSaved, getElem!_pos frame.locals 18 hi] using b
      by_cases h19 : i = 19
      · subst i; simpa only [matrixRowSaved, getElem!_pos frame.locals 19 hi] using c
      by_cases h60 : i = 60
      · subst i; simpa only [matrixRowSaved, getElem!_pos frame.locals 60 hi] using d
      by_cases h61 : i = 61
      · subst i; simpa only [matrixRowSaved, getElem!_pos frame.locals 61 hi] using e
      by_cases h62 : i = 62
      · subst i; simpa only [matrixRowSaved, getElem!_pos frame.locals 62 hi] using f
      simp [matrixRowSaved, h5, h18, h19, h60, h61, h62, getElem!_pos frame.locals i hi]
    · have read := tailReads ⟨i - 63, by omega⟩
      have address : i - 63 + 72 = i + 9 := by omega
      simp only [address] at read
      simpa only [getElem!_pos frame.locals i hi] using matrix_local_read frame i _ paramsLength locals (by omega) read
    · simp only [matrixRowAfter]
      split_ifs with owner
      · have equal : i = 82 := by omega
        subst i
        simpa only [getElem!_pos frame.locals 82 hi] using g
      · have address : i - 78 + 78 = i := by omega
        simp only [address, getElem!_pos frame.locals i hi]

#print axioms matrixRowFrame_reconstruct

end Project.Beck.Execution
