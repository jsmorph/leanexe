import Interpreter.Wasm.Locals
import Project.TalosCompat

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

theorem of_withValues {frame : Locals} {values : List Value} {P R : Locals → Prop}
    (hValues : frame.values = values)
    (hP : P { frame with values := [] })
    (hNext : ∀ next, P next → R { next with values := values }) : R frame := by
  have hFrame : ({ frame with values := values } : Locals) = frame :=
    ext _ _ rfl rfl hValues.symm
  simpa only [hFrame] using hNext { frame with values := [] } hP

theorem parameter_getElem_of_get (frame : Locals) (index : Nat) (value : Value)
    (hIndex : index < frame.params.length) (hGet : frame.get index = some value) :
    frame.params[index]'hIndex = value := by
  have h : frame.params[index]? = some value := by
    simpa [Locals.get, hIndex] using hGet
  rw [List.getElem?_eq_getElem hIndex] at h
  exact Option.some.inj h

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
