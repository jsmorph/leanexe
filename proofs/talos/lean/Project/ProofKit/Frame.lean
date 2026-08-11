import Interpreter.Wasm.Locals

namespace Project.ProofKit.Frame

open Wasm

@[ext]
theorem ext (left right : Locals)
    (hParams : left.params = right.params)
    (hLocals : left.locals = right.locals)
    (hValues : left.values = right.values) : left = right := by
  cases left
  cases right
  simp_all

@[simp]
theorem withValues_params (frame : Locals) (values : List Value) :
    ({ frame with values := values } : Locals).params = frame.params := rfl

@[simp]
theorem withValues_locals (frame : Locals) (values : List Value) :
    ({ frame with values := values } : Locals).locals = frame.locals := rfl

@[simp]
theorem withValues_values (frame : Locals) (values : List Value) :
    ({ frame with values := values } : Locals).values = values := rfl

@[simp]
theorem withValues_get (frame : Locals) (values : List Value) (index : Nat) :
    ({ frame with values := values } : Locals).get index = frame.get index := rfl

theorem internal_getElem?_of_get
    (frame : Locals) (parameterCount localIndex : Nat) (value : Value)
    (hParams : frame.params.length = parameterCount)
    (hLocal : localIndex < frame.locals.length)
    (hGet : frame.get (parameterCount + localIndex) = some value) :
    frame.locals[localIndex]? = some value := by
  subst parameterCount
  simpa [Wasm.Locals.get, hLocal] using hGet

theorem internal_getElem_of_get
    (frame : Locals) (parameterCount localIndex : Nat) (value : Value)
    (hParams : frame.params.length = parameterCount)
    (hLocal : localIndex < frame.locals.length)
    (hGet : frame.get (parameterCount + localIndex) = some value) :
    frame.locals[localIndex]'hLocal = value := by
  have h := internal_getElem?_of_get frame parameterCount localIndex value
    hParams hLocal hGet
  rw [List.getElem?_eq_getElem hLocal] at h
  exact Option.some.inj h

end Project.ProofKit.Frame
