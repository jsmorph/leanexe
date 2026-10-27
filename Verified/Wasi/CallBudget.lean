import Verified.Wasi.CallFrame
import Verified.Wasi.ResourceCompilerCost

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem ArgumentsAfter.call_budget {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {source : Wasm.Module}
    {args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)}
    {depth : UInt64} {env : Env context} {slots : List Slot} {all kept live : Nat → Bool}
    {base budget : Nat} {heap argumentHeap : Heap} {initial arguments : Store (Observed World)}
    {locals argumentLocals : Locals} {params : List Value} {fresh : List (Nat × Nat)}
    (after : ArgumentsAfter pure.funs pure.flags (pure.callBounds depth) (pure.callFits depth)
      signature.mode args env slots all kept base heap initial locals argumentHeap arguments
      argumentLocals params fresh)
    (charge : pure.argumentCost depth (slots.map Slot.mode) live signature args env =
      argumentCost pure.funs pure.flags (pure.callBounds depth) signature.mode args env slots all kept)
    (sameWorld : arguments.host = initial.host)
    (within : heap.Within (PureTransport.erase initial) source budget)
    (bounded : Resource.PrefixBound (observedHost host) pure program depth (slots.map Slot.mode)
      live (.call callee args) env initial.host budget) :
    argumentHeap.Within (PureTransport.erase arguments) source
        (budget - pure.argumentCost depth (slots.map Slot.mode) live signature args env) ∧
      Resource.CallPrefixBound (observedHost host) pure program callee (depth + 1)
        (Env.ofFn fun i => (args i).denote pure.funs env) arguments.host
        (budget - pure.argumentCost depth (slots.map Slot.mode) live signature args env) := by
  obtain ⟨chargeBound, fits, _⟩ := bounded.call_arguments
  have allFits : (argsAll fun i => (args i).fits pure.funs (pure.callFits depth) env) = true := by
    simpa only [Resource.PureContext.argumentFits, Resource.PureContext.exprFits] using fits
  have top := after.top allFits
  rw [← charge] at top
  refine ⟨within.shift top (by omega) (after.step.cap source), ?_⟩
  simpa only [sameWorld] using bounded.call_body

theorem call_arguments_allowed {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {source : Wasm.Module}
    {args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)}
    {depth : UInt64} {env : Env context} {slots : List Slot} {all kept live : Nat → Bool}
    {budget : Nat} {heap : Heap} {initial : Store (Observed World)} {aborts : Bool}
    (charge : pure.argumentCost depth (slots.map Slot.mode) live signature args env =
      argumentCost pure.funs pure.flags (pure.callBounds depth) signature.mode args env slots all kept)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.PrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live
        (.call callee args) env initial.host budget)
    (failure : (!(argsAll fun i => (args i).fits pure.funs (pure.callFits depth) env) ||
      !decide (heap.Within (PureTransport.erase initial) source
        (argumentCost pure.funs pure.flags (pure.callBounds depth) signature.mode args env
          slots all kept))) = true) : aborts = true := by
  cases policy : aborts with
  | true => rfl
  | false =>
      obtain ⟨within, bounded⟩ := resources policy
      obtain ⟨chargeBound, fits, _⟩ := bounded.call_arguments
      have allFits : (argsAll fun i => (args i).fits pure.funs (pure.callFits depth) env) = true := by
        simpa only [Resource.PureContext.argumentFits, Resource.PureContext.exprFits] using fits
      have room := within.mono chargeBound
      rw [charge] at room
      simp only [allFits, Bool.not_true, Bool.false_or, room, decide_true] at failure
      exact nomatch failure

end Verified.Wasi
