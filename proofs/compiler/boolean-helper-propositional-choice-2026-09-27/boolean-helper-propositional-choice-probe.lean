import LeanExe.Extract.ScalarFunc
namespace BooleanHelperPropositionalChoiceProbe

def word (x y : UInt64) : UInt64 :=
  (if x < y then (let f := fun n : UInt64 => n == y; f x || f 0)
   else (let g := fun b : Bool => b || y == 0; g (x == 0))).toUInt64 + x

def relation (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) = (x == 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

def falsity (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = false then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

def compound (x y : UInt64) : UInt64 :=
  (if x < y ∧ (let f := fun n : UInt64 => n == y; f x || f 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

def negated (x y : UInt64) : UInt64 :=
  (if _h : ¬ x < y then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

def letGuard (x y : UInt64) : UInt64 :=
  (if (let k := y + 1; x < k) then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

end BooleanHelperPropositionalChoiceProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperPropositionalChoiceProbe.word, `BooleanHelperPropositionalChoiceProbe.relation,
      `BooleanHelperPropositionalChoiceProbe.falsity, `BooleanHelperPropositionalChoiceProbe.compound,
      `BooleanHelperPropositionalChoiceProbe.negated, `BooleanHelperPropositionalChoiceProbe.letGuard] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
