import LeanExe.Extract.ScalarFunc
namespace BooleanScopeBindingProbe

def word (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun n : Id UInt64 =>
     let g := fun b : Id Bool => (Id.run b) != (saved == y)
     g ((Id.run n) == saved) || g (x == 0)
   f x && f y).toUInt64 + y

def flag (x y : UInt64) : UInt64 :=
  (let saved := x == y
   let f := fun n : UInt64 => saved || n == y
   f x && f 0).toUInt64 + x

def wordId (x y : UInt64) : UInt64 :=
  (let saved : Id (Id UInt64) := pure (pure (x + y))
   let f := fun n : Id UInt64 => (Id.run n) == Id.run (Id.run saved)
   f x || f y).toUInt64 + y

def flagId (x y : UInt64) : UInt64 :=
  (let saved : Id (Id Bool) := pure (pure (x == y))
   let f := fun b : Id Bool => Id.run b || Id.run (Id.run saved)
   f (x == 0) && f (y == 0)).toUInt64 + x

def unused (x y : UInt64) : UInt64 :=
  (let _unused := x + y
   let f := fun n : UInt64 => n == y
   f x || f 0).toUInt64 + x

def nested (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let flag := saved == x
   let f := fun n : UInt64 => flag || n == saved
   f x && f y).toUInt64 + y

end BooleanScopeBindingProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanScopeBindingProbe.word, `BooleanScopeBindingProbe.flag,
      `BooleanScopeBindingProbe.wordId, `BooleanScopeBindingProbe.flagId,
      `BooleanScopeBindingProbe.unused, `BooleanScopeBindingProbe.nested] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
