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

def negatedRepeated (x y : UInt64) : UInt64 :=
  (if _h : ¬ x < y then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

def letRepeated (x y : UInt64) : UInt64 :=
  (if (let k := y + 1; x < k) then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

end BooleanHelperPropositionalChoiceProbe
open LeanExe.Extract.Core
run_elab do
  let env ← Lean.getEnv
  let some info := env.find? `BooleanHelperPropositionalChoiceProbe.compound | throwError "missing"
  let some body := info.value? | throwError "missing body"
  let rec visit (e : Lean.Expr) : Lean.Elab.Term.TermElabM Unit := do
    let args := e.getAppArgs
    if e.getAppFn.isConstOf ``ite && args.size == 5 then
      let condition := args[1]!
      let evidence := args[2]!
      Lean.logInfo m!"condition: {repr condition}"
      Lean.logInfo m!"evidence: {repr evidence}"
      Lean.logInfo m!"guard: {(guardOperands? condition).isSome}; proposition: {(propositionGuard? condition evidence).isSome}; selection: {(booleanGuardedSelectionSyntax? e).isSome}"
      if let some guard := guardOperands? condition then
        Lean.logInfo m!"guard tree: {repr guard}"
        Lean.logInfo m!"decision: {guardDecision? guard evidence}"
    match e with
    | .app f a => visit f; visit a
    | .lam _ _ b _ => visit b
    | .letE _ _ a b _ => visit a; visit b
    | .mdata _ b => visit b
    | _ => pure ()
  visit body
