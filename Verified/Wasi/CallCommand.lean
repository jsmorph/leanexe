import Verified.Wasi.CallFrame
import Verified.Wasi.CallHelper
import Verified.Wasi.ResultRelease
import Verified.Wasi.WriteCommand

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_call_after_arguments {World : Type} {S : List Sig} {context : List Ty}
    {source target : Wasm.Module} {host : Host World}
    {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {signature : EffectSig}
    {args : (i : Fin signature.params.length) → Expr S context (signature.params.get i)}
    {meaning : Env signature.params → Action signature.result.denote}
    {env : Env context} {slots : List Slot} {all kept live : Nat → Bool} {base : Nat}
    {heap argumentHeap : Heap} {initial arguments : Store (Observed World)}
    {locals argumentLocals : Locals} {params : List Value} {fresh : List (Nat × Nat)}
    {depth : UInt64} {index : Nat} {function : Wasm.Function} {pool : Bytes.LiteralPool}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (spec : EffectSpec target signature index meaning pool)
    (noImport : target.imports[index]? = none)
    (lookup : target.funcs[index - target.imports.length]? = some function)
    (arity : function.numParams = 1 + widthSum signature.params)
    (hostValid : targetHost.Satisfies target (hostSpec host))
    (vars : Holds env slots all base heap (PureTransport.erase initial) locals)
    (safe : pool.Safe env slots all heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots all (PureTransport.erase initial) locals ABI.scratch)
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (keptSelected : ∀ i, kept i = true → all i = true)
    (liveSelected : ∀ i, live i = true → kept i = true)
    (after : ArgumentsAfter funs flags bounds fits signature.mode args env slots all kept base
      heap initial locals argumentHeap arguments argumentLocals params fresh)
    (sameWorld : arguments.host = initial.host)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (form : Encoding.ProgramForm (releaseWhere context slots (fun i => kept i && !live i)))
    (closed : Relocation.programClosed source.funcs.length
      (releaseWhere context slots (fun i => kept i && !live i)) = true) :
    wp target (.call index ::
        Relocation.program (releaseWhere context slots (fun i => kept i && !live i)))
      (CommandResult host env slots all live base signature.result
        (meaning (Env.ofFn fun i => (args i).denote funs env)) heap initial locals true)
      arguments { argumentLocals with
        values := (.i64 depth :: params).reverse ++ locals.values } targetHost := by
  refine wp_effect_helper spec noImport lookup arity hostValid after.step.at_ after.rep
    after.separate (after.pool_input uses safe) (after.scratch uses scratch)
    (by rw [after.step.cap target]; exact cap) ?_ ?_ ?_
  · intro value finalHeap final words trace execution step rep
    have callAfter := after.call uses keptSelected vars scratch step rep
    have updated : After env slots all kept base heap initial locals signature.result value
        finalHeap final { argumentLocals with values := words.reverse ++ locals.values } words :=
      ⟨callAfter.step, callAfter.frame.trans Frame.ofValues,
        callAfter.holds, callAfter.rep, callAfter.apart⟩
    rw [← List.append_nil
      (Relocation.program (releaseWhere context slots (fun i => kept i && !live i)))]
    refine wp_release_context (sourceHost := sourceHost) (rest := []) runtime layout profile
      form closed updated.holds updated.step.at_
      (fun i selected => by simp only [Bool.and_eq_true] at selected; exact selected.1) ?_
    intro releasedHeap released evolution _ releasedWorld
    have retained : ∀ i, live i = true → (kept i && !(kept i && !live i)) = true :=
      fun i selected => by simp only [selected, liveSelected i selected,
        Bool.not_true, Bool.and_false, Bool.not_false, Bool.and_self]
    have resultAfter := After.release vars scratch updated keptSelected liveSelected
      (evolution.mono retained)
    rw [wp_nil]
    apply CommandResult.returned value releasedHeap released
      { argumentLocals with values := words.reverse ++ locals.values } words trace
    · rw [releasedWorld, ← sameWorld]
      exact execution
    · exact resultAfter
  · intro final trace outcome message execution ending
    apply CommandResult.terminal final trace outcome message
    · rw [← sameWorld]
      exact execution
    · exact ending
  · intro final trace residual progress
    apply CommandResult.resource final trace residual rfl
    rw [← sameWorld]
    exact progress

end Verified.Wasi
