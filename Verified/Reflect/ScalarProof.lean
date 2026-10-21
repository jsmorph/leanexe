import Verified.Reflect.Definitions
import Verified.ScalarNumeric
import Verified.ScalarCalls
import Verified.ScalarControl

namespace Verified.Reflect

open Lean Meta Elab Term

partial def scalarCodeProof (m code : Lean.Expr) (callees : Nat → Option Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let program ← kernelWhnf code
  if program.isAppOfArity ``List.nil 1 then
    return some (← mkAppM ``Wasm.CodeUniform.nil #[m],
      ← mkAppM ``Wasm.CodeNoReturnCall.nil #[m])
  let (``List.cons, #[_, instruction, rest]) := program.getAppFnArgs
    | throwError "verified_compile: expected an instruction list, got {program}"
  let inst ← kernelWhnf instruction
  let name := inst.getAppFn.constName!
  let args := inst.getAppArgs
  let one ← if name == ``Wasm.Instruction.call then do
      let some index := natOf (← kernelWhnf args[0]!)
        | throwError "verified_compile: expected a constant call index"
      let some callee := callees index | return none
      pure (some (← mkAppM ``Wasm.OneUniform.call #[callee],
        ← mkAppM ``Wasm.OneNoReturnCall.call #[m, args[0]!]))
    else if name == ``Wasm.Instruction.block || name == ``Wasm.Instruction.loop then do
      let some (uniform, safe) ← scalarCodeProof m args[2]! callees | return none
      let uniformName := if name == ``Wasm.Instruction.block then
        ``Wasm.OneUniform.block else ``Wasm.OneUniform.loop
      let safeName := if name == ``Wasm.Instruction.block then
        ``Wasm.OneNoReturnCall.block else ``Wasm.OneNoReturnCall.loop
      let metadata := #[args[0]!, args[1]!, args[3]!, args[4]!]
      pure (some (← mkAppM uniformName (#[uniform] ++ metadata),
        ← mkAppM safeName (#[safe] ++ metadata)))
    else if name == ``Wasm.Instruction.iff then do
      let some (first, firstSafe) ← scalarCodeProof m args[2]! callees | return none
      let some (second, secondSafe) ← scalarCodeProof m args[3]! callees | return none
      let metadata := #[args[0]!, args[1]!, args[4]!, args[5]!]
      pure (some (← mkAppM ``Wasm.OneUniform.iff (#[first, second] ++ metadata),
        ← mkAppM ``Wasm.OneNoReturnCall.iff (#[firstSafe, secondSafe] ++ metadata)))
    else do
      let uniformName := ``Wasm.OneUniform ++ Name.mkSimple name.getString!
      let safeName := ``Wasm.OneNoReturnCall ++ Name.mkSimple name.getString!
      unless (← getEnv).contains uniformName && (← getEnv).contains safeName do return none
      pure (some (mkAppN (Lean.mkConst uniformName) (#[m] ++ args),
        mkAppN (Lean.mkConst safeName) (#[m] ++ args)))
  let some (first, firstSafe) := one | return none
  let some (next, nextSafe) ← scalarCodeProof m rest callees | return none
  return some (← mkAppM ``Wasm.CodeUniform.cons #[first, next],
    ← mkAppM ``Wasm.CodeNoReturnCall.cons #[firstSafe, nextSafe])

def scalarEntryProof (m : Lean.Expr) (index : Nat)
    (callees : Nat → Option Lean.Expr) : MetaM (Option Lean.Expr) := do
  let functions ← mkAppM ``Wasm.Module.funcs #[m]
  let lookup ← mkAppM ``GetElem?.getElem? #[functions, mkNatLit index]
  let someFunction ← kernelWhnf lookup
  let (``Option.some, #[_, function]) := someFunction.getAppFnArgs
    | throwError "verified_compile: missing scalar function {index}: {someFunction}"
  let body ← mkAppM ``Wasm.Function.body #[function]
  let some (uniform, safe) ← scalarCodeProof m body callees | return none
  let imports ← mkAppM ``Wasm.Module.imports #[m]
  let emptyImports := listExpr (Lean.mkConst ``Wasm.ImportDecl) []
  let hImports ← mkExpectedTypeHint (← mkEqRefl emptyImports) (← mkEq imports emptyImports)
  let hLookup ← mkExpectedTypeHint (← mkEqRefl someFunction) (← mkEq lookup someFunction)
  return some (← mkAppM ``Wasm.EntryUniform.of_code #[hImports, hLookup, uniform, safe])

def addScalarProof (base : Name) (r : Reflected) (index : Nat)
    (callees : Nat → Option Lean.Expr) : TermElabM (Option Lean.Expr) := do
  unless r.params.all (fun t => match t with | .elem _ => true | _ => false) &&
      (match r.result with | .elem _ => true | _ => false) do return none
  let m := Lean.mkConst (base ++ `module)
  let some proof ← scalarEntryProof m index callees | return none
  let name := base ++ Name.mkSimple r.name.getString!
  let claim ← mkAppM ``Wasm.EntryUniform #[m, mkNatLit index]
  addTheorem (name ++ `uniform) claim proof
  let uniform := Lean.mkConst (name ++ `uniform)
  let pureProof ← mkAppM ``implementsPure_of_uniform #[Lean.mkConst (name ++ `implements), uniform]
  addTheorem (name ++ `pure) (← inferType pureProof) pureProof
  return some uniform

end Verified.Reflect
