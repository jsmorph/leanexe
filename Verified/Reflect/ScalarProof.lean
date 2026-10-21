import Verified.Reflect.Definitions
import Verified.ScalarNumeric
import Verified.ScalarCalls
import Verified.ScalarControl

namespace Verified.Reflect

open Lean Meta Elab Term

partial def scalarCodeProof (m code : Lean.Expr) (callees : Nat → Option Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let mut rest := code
  let mut pieces : Array (Lean.Expr × Lean.Expr) := #[]
  while true do
    let program ← kernelWhnf rest
    if program.isAppOfArity ``List.nil 1 then break
    let (``List.cons, #[_, instruction, next]) := program.getAppFnArgs
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

    let first ← mkExpectedTypeHint first (← mkAppM ``Wasm.OneUniform #[m, instruction])
    let firstSafe ← mkExpectedTypeHint firstSafe (← mkAppM ``Wasm.OneNoReturnCall #[m, instruction])
    pieces := pieces.push (← mkAppM ``Wasm.CodeUniform.cons
      #[first, ← mkAppM ``Wasm.CodeUniform.nil #[m]],
      ← mkAppM ``Wasm.CodeNoReturnCall.cons
        #[firstSafe, ← mkAppM ``Wasm.CodeNoReturnCall.nil #[m]])
    rest := next
  if pieces.isEmpty then
    return some (← mkAppM ``Wasm.CodeUniform.nil #[m],
      ← mkAppM ``Wasm.CodeNoReturnCall.nil #[m])
  while pieces.size > 1 do
    let mut next : Array (Lean.Expr × Lean.Expr) := #[]
    for k in [:(pieces.size + 1) / 2] do
      let left := pieces[2 * k]!
      if 2 * k + 1 < pieces.size then
        let right := pieces[2 * k + 1]!
        next := next.push (← mkAppM ``Wasm.CodeUniform.append #[left.1, right.1],
          ← mkAppM ``Wasm.CodeNoReturnCall.append #[left.2, right.2])
      else next := next.push left
    pieces := next
  let (uniform, safe) := pieces[0]!
  return some (← mkExpectedTypeHint uniform (← mkAppM ``Wasm.CodeUniform #[m, code]),
    ← mkExpectedTypeHint safe (← mkAppM ``Wasm.CodeNoReturnCall #[m, code]))

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
  trace[Verified.reflect] "store proof {r.name}"
  let m := Lean.mkConst (base ++ `module)
  let some proof ← scalarEntryProof m index callees | return none
  let name := base ++ Name.mkSimple r.name.getString!
  let claim ← mkAppM ``Wasm.EntryUniform #[m, mkNatLit index]
  addTheorem (name ++ `uniform) claim proof
  let uniform := Lean.mkConst (name ++ `uniform)
  let pureProof ← mkAppM ``implementsPure_of_uniform #[Lean.mkConst (name ++ `implements), uniform]
  addTheorem (name ++ `pure) (← inferType pureProof) pureProof
  trace[Verified.reflect] "store proof checked {r.name}"
  return some uniform

end Verified.Reflect
