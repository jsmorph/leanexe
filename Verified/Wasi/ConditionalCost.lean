import Verified.Wasi.ResourceBudget

namespace Verified.Wasi.Resource

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem PureContext.returnBoolCost_nil (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (condition : Expr pureSigs context .bool)
    (env : Env context) (store : Store Unit) (locals : Locals) :
    Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) condition env slots []
      live store locals = pure.exprCost depth (slots.map Slot.mode) live condition env := by
  rw [pure.returnCost_nil]
  simp [PureContext.ownedCost, coerceCost, Ty.copyCost]

theorem ResourceExec.ite_selected {World : Type} {host : Host World}
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits}
    (execution : ResourceExec host pure program depth modes live
      (bif condition.denote pure.funs env then yes else no) env world trace outcome final spent fits) :
    ResourceExec host pure program depth modes live (.ite condition yes no) env
      world trace outcome final
      (pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env + spent)
      (pure.exprFits depth condition env && fits) := by
  cases chosen : condition.denote pure.funs env with
  | false => exact .ite_no chosen (by simpa only [chosen, Bool.cond_false] using execution)
  | true => exact .ite_yes chosen (by simpa only [chosen, Bool.cond_true] using execution)

theorem PrefixBound.ite_selected {World : Type} {host : Host World}
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.ite condition yes no) env world budget) :
    PrefixBound host pure program depth modes live
      (bif condition.denote pure.funs env then yes else no) env world
      (budget - pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env) := by
  cases chosen : condition.denote pure.funs env with
  | false => simpa only [chosen, Bool.cond_false] using bounded.ite_no chosen
  | true => simpa only [chosen, Bool.cond_true] using bounded.ite_yes chosen

theorem PrefixBound.ite_resources {World : Type} {host : Host World}
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {slots : List Slot} {live : Nat → Bool}
    {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world : World} {budget : Nat} {heap : Heap} {store : Store Unit} {source : Wasm.Module}
    (locals : Locals)
    (bounded : PrefixBound host pure program depth (slots.map Slot.mode) live
      (.ite condition yes no) env world budget) (within : heap.Within store source budget) :
    heap.Within store source
      (Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) condition env slots []
        (fun i => live i || yes.uses i || no.uses i) store locals) ∧
      pure.exprFits depth condition env = true := by
  rw [pure.returnBoolCost_nil]
  exact ⟨within.mono bounded.ite_condition.1, bounded.ite_condition.2⟩

end Verified.Wasi.Resource
