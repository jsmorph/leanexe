import Project.Beck.ExecutionRead
import Project.Beck.Boundary
import Project.ProofKit.CallRemainder
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

abbrev BoundaryScratch := Fin 43 → Value

def boundaryBody : Wasm.Program :=
  match (func32[14]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def boundaryParams (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64) : List Value :=
  (inputValues input inputOwner inputPointer).reverse ++ (pointValues point pointOwner pointPointer).reverse ++
    [.i64 directionOwner, .i64 directionPointer]

def boundaryLocal (jobs index : Nat) (step : Boundary.Step) (scratch : BoundaryScratch) (k : Fin 43) : Value :=
  if k.val = 2 then .i64 step.1
  else if k.val = 3 then .i64 step.2
  else if k.val = 33 then .i64 index.toUInt64
  else if k.val = 34 then .i64 jobs.toUInt64
  else if k.val = 35 then .i64 1
  else scratch k

def boundaryFrame (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64)
    (index : Nat) (step : Boundary.Step) (scratch : BoundaryScratch) : Locals :=
  { params := boundaryParams input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
    locals := List.ofFn (boundaryLocal input.jobs index step scratch) }

theorem boundary_locals_expanded (f : Fin 43 → Value) : List.ofFn f =
    [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9,
      f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18, f 19,
      f 20, f 21, f 22, f 23, f 24, f 25, f 26, f 27, f 28, f 29,
      f 30, f 31, f 32, f 33, f 34, f 35, f 36, f 37, f 38, f 39, f 40, f 41, f 42] := rfl

theorem boundary_local_read (frame : Locals) (index : Nat) (value : Value)
    (params : frame.params.length = 11) (locals : frame.locals.length = 43)
    (inside : index < 43) (read : frame.get (index + 11) = some value) : frame.locals[index]! = value := by
  have indexBound : index < frame.locals.length := by omega
  have read' : frame.locals[index]? = some value := by
    simpa [Locals.get, params, locals, show ¬index + 11 < 11 by omega,
      show index + 11 < 11 + 43 by omega, Nat.add_sub_cancel] using read
  simpa only [getElem?_pos frame.locals index indexBound, getElem!_pos frame.locals index indexBound,
    Option.some.injEq] using read'

theorem boundaryFrame_reconstruct (frame : Locals) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64)
    (index : Nat) (step : Boundary.Step)
    (params : frame.params = boundaryParams input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer)
    (locals : frame.locals.length = 43) (values : frame.values = [])
    (r13 : frame.get 13 = some (.i64 step.1)) (r14 : frame.get 14 = some (.i64 step.2))
    (r44 : frame.get 44 = some (.i64 index.toUInt64)) (r45 : frame.get 45 = some (.i64 input.jobs.toUInt64))
    (r46 : frame.get 46 = some (.i64 1)) :
    frame = boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer
      index step (fun k => frame.locals[k.val]!) := by
  have paramsLength : frame.params.length = 11 := by simp [params, boundaryParams, inputValues, pointValues]
  have a := boundary_local_read frame 2 (.i64 step.1) paramsLength locals (by decide) r13
  have b := boundary_local_read frame 3 (.i64 step.2) paramsLength locals (by decide) r14
  have c := boundary_local_read frame 33 (.i64 index.toUInt64) paramsLength locals (by decide) r44
  have d := boundary_local_read frame 34 (.i64 input.jobs.toUInt64) paramsLength locals (by decide) r45
  have e := boundary_local_read frame 35 (.i64 1) paramsLength locals (by decide) r46
  apply Frame.ext frame _ params _ values
  change frame.locals = List.ofFn (boundaryLocal input.jobs index step (fun k => frame.locals[k.val]!))
  apply List.ext_getElem
  · simp [locals]
  · intro i hi hj
    rw [List.getElem_ofFn]
    simp only [boundaryLocal]
    split_ifs with ha hb hc hd he
    · subst i; simpa only [getElem!_pos frame.locals 2 hi] using a
    · subst i; simpa only [getElem!_pos frame.locals 3 hi] using b
    · subst i; simpa only [getElem!_pos frame.locals 33 hi] using c
    · subst i; simpa only [getElem!_pos frame.locals 34 hi] using d
    · subst i; simpa only [getElem!_pos frame.locals 35 hi] using e
    · simp [getElem!_pos frame.locals i hi]

theorem boundaryFrame_post (store : Store Unit) (frame : Locals) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer : UInt64)
    (index : Nat) (step : Boundary.Step) (Q : Assertion Unit)
    (next : ∀ scratch, Q (.Break 0 store
      (boundaryFrame input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer index step scratch)))
    (params : frame.params = boundaryParams input point inputOwner inputPointer pointOwner pointPointer directionOwner directionPointer)
    (locals : frame.locals.length = 43) (values : frame.values = [])
    (r13 : frame.get 13 = some (.i64 step.1)) (r14 : frame.get 14 = some (.i64 step.2))
    (r44 : frame.get 44 = some (.i64 index.toUInt64)) (r45 : frame.get 45 = some (.i64 input.jobs.toUInt64))
    (r46 : frame.get 46 = some (.i64 1)) : Q (.Break 0 store frame) := by
  rw [boundaryFrame_reconstruct frame input point inputOwner inputPointer pointOwner pointPointer directionOwner
    directionPointer index step params locals values r13 r14 r44 r45 r46]
  exact next _

end Project.Beck.Execution
