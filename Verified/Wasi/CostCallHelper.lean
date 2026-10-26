import Verified.Wasi.CostEffectSpec

namespace Verified.Wasi.Resource

open LeanExe.Wasi

theorem ResourceCall.returned_prefix {World : Type} {host : Host World}
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world trace value final spent fits}
    (execution : ResourceCall host pure program callee depth env world trace (.returned value)
      final spent fits) :
    ResourceCallPrefix host pure program callee depth env world trace (.pure value) final spent
      fits := by
  induction callee with
  | here =>
      cases execution with
      | here run => exact .here (.returned run)
  | there callee ih =>
      cases execution with
      | there run => exact .there (ih run)

theorem CallPrefixBound.returned {World : Type} {host : Host World}
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world : World} {budget : Nat} {trace value final spent fits}
    (bounded : CallPrefixBound host pure program callee depth env world budget)
    (execution : ResourceCall host pure program callee depth env world trace (.returned value)
      final spent fits) :
    spent ≤ budget ∧ fits = true :=
  bounded _ _ _ _ _ execution.returned_prefix

end Verified.Wasi.Resource

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_cost_effect_helper {World : Type} {source target : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {signature : EffectSig} {callee : EffectVar effectSigs signature}
    {index : Nat} {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {depth : UInt64} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {params values : List Value} {args : Env signature.params} {function : Wasm.Function}
    {rest : Program} {Q : Assertion (Observed World)} {budget : Nat} {aborts : Bool}
    (spec : CostEffectSpec source target pure program callee index pool)
    (noImport : target.imports[index]? = none)
    (lookup : target.funcs[index - target.imports.length]? = some function)
    (arity : function.numParams = 1 + widthSum signature.params)
    (hostValid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep signature.mode heap (PureTransport.erase initial) params args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) signature.mode params args)
      (Env.reads (PureTransport.erase initial) signature.mode params args))
    (input : @Bytes.LiteralPool.Input (Env signature.params)
      (Env.represent signature.params signature.modes) pool heap (PureTransport.erase initial)
      params args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) signature.mode params args,
      regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program callee depth args initial.host budget)
    (returned : ∀ value finalHeap final words trace spent fits,
      Resource.ResourceCall (observedHost host) pure program callee depth args initial.host
        trace (.returned value) final.host spent fits →
      Step heap (PureTransport.erase initial)
        (fun region => Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode params args) region ∧
          regionsDisjoint region ABI.scratch)
        finalHeap (PureTransport.erase final)
        (signature.result.fresh (PureTransport.erase final) words value) →
      signature.result.Rep finalHeap (PureTransport.erase final) words value →
      (fits = true → finalHeap.top.toNat ≤ heap.top.toNat + spent) →
      wp target rest Q final { locals with values := words.reverse ++ values } targetHost)
    (trapped : ∀ final message,
      FunctionResult host signature ((program.funs pure.funs).get callee args) args params heap
        initial aborts (.Trap final message) → Q (.Trap final message)) :
    wp target (.call index :: rest) Q initial
      { locals with values := (.i64 depth :: params).reverse ++ values } targetHost := by
  obtain ⟨bound, allFuel⟩ := spec World host targetHost depth heap initial params args budget aborts
    hostValid at_ rep separate input scratch cap resources
  have runPost := allFuel bound le_rfl
  generalize runEquation : run bound target index initial ((.i64 depth :: params).reverse)
    targetHost = outcome at runPost
  have length : ((.i64 depth :: params).reverse).length = function.numParams := by
    rw [List.length_reverse, List.length_cons, rep.length, arity]
    omega
  cases runPost with
  | returned value finalHeap final words trace spent fits execution step representation top =>
      exact wp_call_returned_at
        (run_append_of_success noImport lookup length runEquation values)
        (returned value finalHeap final words trace spent fits execution step representation top)
  | trapped final message classification =>
      exact wp_call_trapped_at (run_append_of_trap noImport lookup length runEquation values)
        (trapped final message classification)

end Verified.Wasi
