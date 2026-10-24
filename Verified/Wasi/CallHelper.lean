import Verified.Wasi.EffectSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_effect_helper {World : Type} {source target : Wasm.Module} {host : Host World}
    {signature : EffectSig} {meaning : Env signature.params → Action signature.result.denote}
    {index : Nat} {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {depth : UInt64} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {params values : List Value} {args : Env signature.params} {function : Wasm.Function}
    {rest : Program} {Q : Assertion (Observed World)}
    (spec : EffectSpec target signature index meaning pool)
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
    (returned : ∀ value finalHeap final words trace,
      Exec (observedHost host) (meaning args) initial.host trace (.returned value) final.host →
      Step heap (PureTransport.erase initial)
        (fun region => Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode params args) region ∧
          regionsDisjoint region ABI.scratch)
        finalHeap (PureTransport.erase final)
        (signature.result.fresh (PureTransport.erase final) words value) →
      signature.result.Rep finalHeap (PureTransport.erase final) words value →
      wp target rest Q final { locals with values := words.reverse ++ values } targetHost)
    (terminal : ∀ final trace outcome message,
      Exec (observedHost host) (meaning args) initial.host trace outcome final.host →
      TerminalMessage message outcome → Q (.Trap final message))
    (resource : ∀ final trace residual,
      Prefix (observedHost host) (meaning args) initial.host trace residual final.host →
      Q (.Trap final "unreachable")) :
    wp target (.call index :: rest) Q initial
      { locals with values := (.i64 depth :: params).reverse ++ values } targetHost := by
  obtain ⟨bound, allFuel⟩ := spec World host targetHost depth heap initial params args
    hostValid at_ rep separate input scratch cap
  have runPost := allFuel bound le_rfl
  generalize runEquation : run bound target index initial ((.i64 depth :: params).reverse)
    targetHost = outcome at runPost
  have length : ((.i64 depth :: params).reverse).length = function.numParams := by
    rw [List.length_reverse, List.length_cons, rep.length, arity]
    omega
  cases runPost with
  | returned value finalHeap final words trace execution step representation =>
      exact wp_call_returned_at
        (run_append_of_success noImport lookup length runEquation values)
        (returned value finalHeap final words trace execution step representation)
  | terminal final trace outcome message execution ending =>
      exact wp_call_trapped_at (run_append_of_trap noImport lookup length runEquation values)
        (terminal final trace outcome message execution ending)
  | resource final trace residual _ progress =>
      exact wp_call_trapped_at (run_append_of_trap noImport lookup length runEquation values)
        (resource final trace residual progress)

end Verified.Wasi
