import Verified.Wasi.CostEffectSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem CostFunctionResult.there {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {function : EffectFunc pureSigs effectSigs}
    {rest : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {depth : UInt64} {args : Env signature.params} {params : List Value}
    {heap : Heap} {initial : Store (Observed World)} {aborts : Bool}
    {outcome : Result (Observed World)}
    (classification : CostFunctionResult host pure rest callee depth args params heap initial aborts outcome) :
    CostFunctionResult host pure (.cons function rest) (.there callee) depth args params heap initial
      aborts outcome := by
  cases classification with
  | returned value finalHeap final words trace spent fits execution step rep top =>
      exact .returned value finalHeap final words trace spent fits (.there execution) step rep top
  | trapped final message classification => exact .trapped final message classification

theorem CostEffectSpec.there {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {function : EffectFunc pureSigs effectSigs}
    {rest : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {index : Nat} {pool : Bytes.LiteralPool}
    (spec : CostEffectSpec source target pure rest callee index pool) :
    CostEffectSpec source target pure (.cons function rest) (.there callee) index pool := by
  intro World host targetHost depth heap initial params args budget aborts
    valid at_ rep separate input scratch cap resources
  obtain ⟨bound, runs⟩ := spec World host targetHost depth heap initial params args budget aborts
    valid at_ rep separate input scratch cap (fun noAbort => by
      obtain ⟨within, bounded⟩ := resources noAbort
      exact ⟨within, bounded.there⟩)
  exact ⟨bound, fun fuel enough => (runs fuel enough).there⟩

end Verified.Wasi
