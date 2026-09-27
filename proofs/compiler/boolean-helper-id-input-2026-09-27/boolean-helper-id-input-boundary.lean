import LeanExe.Extract.ScalarFunc
namespace IdHelperBoundary

def capture (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun n : UInt64 =>
     let g := fun b : Bool => b != (saved == y)
     g (n == saved) || g (x == 0)
   f x && f y).toUInt64 + y

def proposition (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : UInt64 => n == y; f x || f y) then x + 7 else y + 3

end IdHelperBoundary
run_elab do
  let env ← Lean.getEnv
  for name in [`IdHelperBoundary.capture, `IdHelperBoundary.proposition] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
