import Verified.Wasi.CodeAnalysis
import Verified.Reflect.Definitions

namespace Verified.Wasi

/-- Demands follow command liveness and owned normal returns.  Loop callbacks borrow outer
captures, so only count and initial-state evaluation can demand an outer argument's ownership. -/
def Command.demands : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → (Nat → Bool) → Nat → Bool
  | _, _, .unit, _, _ => false
  | _, _, .ret value, live, index => value.demands live true index
  | _, _, .bind (intermediate := intermediate) first next, live, index =>
    first.demands (fun i => live i || next.uses (i + intermediate.bindCount)) index ||
      next.demands (shift intermediate.bindCount live) (index + intermediate.bindCount)
  | _, _, .ite condition yes no, live, index =>
    condition.demands (fun i => live i || yes.uses i || no.uses i) false index ||
      yes.demands live index || no.demands live index
  | _, _, .call (signature := signature) _ args, live, index =>
    argsAny fun i =>
      if (signature.params.get i).scalar then
        (args i).demands (fun j => live j || argsAny fun other => (args other).uses j) false index
      else
        signature.mode i == .owned && (args i).varIndex? == some index && !live index &&
          !(argsAny fun other => other != i && !(signature.params.get other).scalar &&
            (args other).uses index)
  | _, _, .read capacity, live, index => capacity.demands live false index
  | _, _, .write _ _, _, _ => false
  | _, _, .exit code, live, index => code.demands live false index
  | _, _, .loop count initial test step, live, index =>
    let all := fun i => live i || test.uses (i + 2) || step.uses (i + 2)
    count.demands (fun i => all i || initial.uses i) false index ||
      initial.demands all true index

def Command.paramChoice {params : List Ty} {result : ResultTy}
    (body : Command pureSigs effectSigs params result) : List Mode :=
  (List.range params.length).map fun index =>
    match params[index]? with
    | some (Ty.array _) | some (Ty.tree _) | some (Ty.treeHeader _) | some Ty.bytes =>
      if body.demands (fun _ => false) index then .owned else .borrowed
    | _ => .borrowed

namespace Reflect

open Lean Meta

def paramChoiceOf (name : Name) (source : Lean.Expr) (hiddenTables : Nat := 0) : MetaM (List Mode) := do
  let some modes ← Verified.Reflect.modesOf (← mkAppM ``Command.paramChoice #[source])
    | throwError "verified_compile_wasi: cannot evaluate the parameter modes of {name}"
  if hiddenTables > modes.length then
    throwError "verified_compile_wasi: {name} has fewer parameters than its hidden tables"
  return List.replicate hiddenTables .borrowed ++ modes.drop hiddenTables

end Reflect

end Verified.Wasi
