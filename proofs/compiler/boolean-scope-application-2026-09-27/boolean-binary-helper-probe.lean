import LeanExe.Extract.ScalarFunc
namespace BooleanBinaryHelperProbe

def direct (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a == b
  (f x y).toUInt64 + x

def repeated (x y : UInt64) : UInt64 :=
  (let f := fun a b : UInt64 => a == b
   f x y || f y 0).toUInt64 + y

def capture (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun a b : UInt64 => a + b == saved
   f x y && f y x).toUInt64 + x

def nested (x y : UInt64) : UInt64 :=
  (let f := fun a b : UInt64 =>
     let g := fun n : UInt64 => n == b
     g a || g x
   f x y && f y x).toUInt64 + y

def retained (x y : UInt64) : UInt64 :=
  (let f := fun (a b : UInt64) => (pure (a == b) : Id Bool)
   Id.run (f x y) || Id.run (f y 0)).toUInt64 + x

def unused (x y : UInt64) : UInt64 :=
  (let _f := fun a b : UInt64 => a == b
   x == y).toUInt64 + y

end BooleanBinaryHelperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanBinaryHelperProbe.direct, `BooleanBinaryHelperProbe.repeated,
      `BooleanBinaryHelperProbe.capture, `BooleanBinaryHelperProbe.nested,
      `BooleanBinaryHelperProbe.retained, `BooleanBinaryHelperProbe.unused] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
