import Verified.Wasi

namespace Verified.Wasi.ReflectBinderCases

open LeanExe.Wasi

def boolInput (aborts : Bool) : Action Bool := pure aborts
def wordInput (aborts : UInt64) : Action UInt64 := pure aborts

verified_compile_wasi compiled := [boolInput, wordInput]

open Lean Meta in
run_elab do
  for (name, expected) in [(``compiled.boolInput.total, mkConst ``Bool),
      (``compiled.wordInput.total, mkConst ``UInt64)] do
    let .forallE _ domain _ _ := (← getConstInfo name).type
      | throwError "{name} omits its native parameter"
    unless ← isDefEq domain expected do
      throwError "{name} has first parameter type {domain}, expected {expected}"

end Verified.Wasi.ReflectBinderCases
