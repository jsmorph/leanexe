import Verified.Wasi.ResourcePrefix

namespace Verified.Wasi.Resource

open LeanExe.Wasi

theorem PrefixBound.returned {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace value final spent fits budget}
    (bounded : PrefixBound host pure program depth modes live command env world budget)
    (execution : ResourceExec host pure program depth modes live command env
      world trace (.returned value) final spent fits) : spent ≤ budget ∧ fits = true :=
  bounded _ _ _ _ _ (.returned execution)

theorem PrefixBound.bind_first {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {first : Command pureSigs effectSigs context intermediate}
    {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
    {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.bind first next) env world budget) :
    PrefixBound host pure program depth modes (bindLive intermediate next live) first env world budget := by
  intro trace residual final spent fits progress
  exact bounded _ _ _ _ _ (.bind_left progress)

theorem PrefixBound.bind_next {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {first : Command pureSigs effectSigs context intermediate}
    {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
    {world firstTrace value after firstSpent firstFits budget}
    (bounded : PrefixBound host pure program depth modes live (.bind first next) env world budget)
    (firstRun : ResourceExec host pure program depth modes (bindLive intermediate next live)
      first env world firstTrace (.returned value) after firstSpent firstFits) :
    PrefixBound host pure program depth (bindModes intermediate modes) (shift intermediate.bindCount live)
      next (intermediate.bindEnv value env) after (budget - firstSpent) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.bind_right firstRun progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

theorem PrefixBound.ite_condition {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {condition : Expr pureSigs context .bool} {yes no : Command pureSigs effectSigs context result}
    {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.ite condition yes no) env world budget) :
    pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env ≤ budget ∧
      pure.exprFits depth condition env = true :=
  bounded _ _ _ _ _ (.ite_charge world)

theorem PrefixBound.ite_yes {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {condition : Expr pureSigs context .bool} {yes no : Command pureSigs effectSigs context result}
    {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.ite condition yes no) env world budget)
    (chosen : condition.denote pure.funs env = true) :
    PrefixBound host pure program depth modes live yes env world
      (budget - pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.ite_yes chosen progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

theorem PrefixBound.ite_no {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {condition : Expr pureSigs context .bool} {yes no : Command pureSigs effectSigs context result}
    {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.ite condition yes no) env world budget)
    (chosen : condition.denote pure.funs env = false) :
    PrefixBound host pure program depth modes live no env world
      (budget - pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.ite_no chosen progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

theorem CallPrefixBound.entry {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {depth : UInt64} {env : Env signature.params} {world : World} {budget : Nat}
    (bounded : CallPrefixBound host pure program callee depth env world budget) : entryFits depth = true :=
  (bounded _ _ _ _ _ (.guard program callee depth env world)).2

theorem CallPrefixBound.body {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {depth : UInt64} {env : Env function.params} {world : World} {budget : Nat}
    (bounded : CallPrefixBound host pure (.cons function rest) .here depth env world budget) :
    PrefixBound host pure rest depth (entryModes function.params function.modes) (fun _ => false)
      function.body env world budget := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.here progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨total, fit.2⟩

theorem CallPrefixBound.there {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world : World} {budget : Nat}
    (bounded : CallPrefixBound host pure (.cons function rest) (.there callee) depth env world budget) :
    CallPrefixBound host pure rest callee depth env world budget := by
  intro trace residual final spent fits progress
  exact bounded _ _ _ _ _ (.there progress)

theorem PrefixBound.call_arguments {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {env : Env context}
    {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.call callee args) env world budget) :
    pure.argumentCost depth modes live signature args env ≤ budget ∧
      pure.argumentFits depth args env = true ∧ entryFits (depth + 1) = true := by
  obtain ⟨cost, fits⟩ := bounded _ _ _ _ _
    (.call (.guard program callee (depth + 1) (Env.ofFn fun i => (args i).denote pure.funs env) world))
  simp only [Bool.and_eq_true] at fits
  exact ⟨by simpa only [Nat.add_zero] using cost, fits⟩

theorem PrefixBound.call_body {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {env : Env context}
    {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.call callee args) env world budget) :
    CallPrefixBound host pure program callee (depth + 1)
      (Env.ofFn fun i => (args i).denote pure.funs env) world
      (budget - pure.argumentCost depth modes live signature args env) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.call progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

end Verified.Wasi.Resource
