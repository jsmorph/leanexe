import Verified.Wasi.FunctionDispatcher
import Verified.Wasi.FunctionRun
import Verified.Wasi.CostResults

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def CostFunctionPost {World : Type} (host : Host World) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (callee : EffectVar effectSigs signature)
    (depth : UInt64) (args : Env signature.params) (params : List Value)
    (heap : Heap) (initial : Store (Observed World)) (aborts : Bool) : Assertion (Observed World) :=
  FunctionRunPost signature.result.width
    (CostFunctionResult host pure program callee depth args params heap initial aborts)

theorem cost_function_post_body {World : Type} {host : Host World}
    {pure : Resource.PureContext pureSigs} {function : EffectFunc pureSigs effectSigs}
    {rest : EffectProg pureSigs effectSigs} {depth : UInt64} {args : Env function.params}
    {params : List Value} {heap middleHeap : Heap} {initial middle : Store (Observed World)}
    {locals middleLocals : Locals} {aborts : Bool} {continuation : Continuation (Observed World)}
    (rep : Env.Rep function.sig.mode heap (PureTransport.erase initial) params args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) function.sig.mode params args)
      (Env.reads (PureTransport.erase initial) function.sig.mode params args))
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) function.sig.mode params args,
      regionsDisjoint ABI.scratch region)
    (held : ∀ {type : Ty} (x : Var function.params type),
      LocalsHold locals (1 + x.offset) type.types ((params.drop x.offset).take type.width))
    (prologue : After args (paramSlots function.params function.modes 1)
      (fun _ => true) function.body.uses (1 + widthSum function.params)
      heap initial locals .unit () middleHeap middle middleLocals [])
    (sameTop : middleHeap.top = heap.top) (sameWorld : middle.host = initial.host)
    (empty : middleLocals.values = [])
    (body : CostCommandResult host pure rest function.body depth args
      (paramSlots function.params function.modes 1) function.body.uses (fun _ => false)
      (1 + widthSum function.params) middleHeap middle middleLocals aborts continuation) :
    CostFunctionPost host pure (.cons function rest) .here depth args params heap initial aborts
      continuation := by
  cases body with
  | returned value finalHeap final finalLocals words trace spent fits execution after top =>
      change CostFunctionResult host pure (.cons function rest) .here depth args params heap initial aborts
        (.Success ((words.reverse ++ middleLocals.values).take function.result.width) final)
      have out : (words.reverse ++ middleLocals.values).take function.result.width = words.reverse := by
        rw [empty, List.append_nil]
        exact List.take_of_length_le (by rw [List.length_reverse, after.rep.length])
      rw [out]
      have combined := After.thenUnit (params_holds rep separate held)
        (params_scratch rep scratch held) prologue after
        (fun _ _ => rfl) (fun _ impossible => Bool.noConfusion impossible)
      have call : Resource.ResourceCall (observedHost host) pure (.cons function rest) .here depth args
          initial.host trace (.returned value) final.host spent (Resource.entryFits depth && fits) := by
        apply Resource.ResourceCall.here
        rw [← sameWorld]
        simpa only [entryModes, paramSlots_modes, EffectFunc.sig] using execution
      refine CostFunctionResult.returned (signature := function.sig) value finalHeap final words trace
        spent (Resource.entryFits depth && fits) call
        (function_after_step (function := function) rep held combined) ?_ ?_
      · exact combined.rep
      · intro fitted
        simp only [Bool.and_eq_true] at fitted
        have growth := top fitted.2
        rw [sameTop] at growth
        exact growth
  | trapped final message classification =>
      change CostFunctionResult host pure (.cons function rest) .here depth args params heap initial aborts
        (.Trap final message)
      apply CostFunctionResult.trapped final message
      have converted := function_post_body (function := function) rep separate scratch held prologue
        sameWorld empty classification
      simpa only [FunctionPost, EffectProg.funs, EffectFuns.get, EffectFunc.sig] using converted

end Verified.Wasi
