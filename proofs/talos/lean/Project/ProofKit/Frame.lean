import Interpreter.Wasm.Locals

namespace Project.ProofKit.Frame

open Wasm

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
