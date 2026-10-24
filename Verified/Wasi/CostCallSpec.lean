import Verified.Wasi.CommandCallSpec
import Verified.Wasi.CallBudget
import Verified.Wasi.CostCallHelper
import Verified.Wasi.CostCodeSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cost_command_call_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {signature : EffectSig}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (calls : CostEffectCalls source target pure program pool) (sourceHost : HostEnv Unit)
    (callee : EffectVar effectSigs signature)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
    CostCommandCodeSpec source target pure program pool (.call callee args) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ depthParam positions vars at_ safe scratch cap low room ready covered place resources
  let all := fun i => live i || argsAny fun j => (args j).uses i
  let kept := fun i => all i &&
    !(argsAny fun j => signature.callMoves slots live args j && (args j).uses i)
  let charge := pure.argumentCost depth (slots.map Slot.mode) live signature args env
  let fits := pure.argumentFits depth args env
  let Q := CostCommandResult host pure program (.call callee args) depth env slots
    all live base heap initial locals aborts
  have chargeEq : charge = argumentCost pure.funs pure.flags (pure.callBounds depth)
      signature.mode args env slots all kept := by
    simpa only [charge, all, kept, Expr.usesFast_eq] using
      pure.argumentCost_compiler depth signature slots live args env
  have uses : ∀ i k, (args i).uses k = true → all k = true := by
    intro i k used
    simp only [all, Bool.or_eq_true]
    exact Or.inr (le_argsAny _ i used)
  have keptAll : ∀ i, kept i = true → all i = true := by
    intro i selected
    simp only [kept, Bool.and_eq_true] at selected
    exact selected.1
  have placement := signature.placeArgs_facts args place
  have liveKept : ∀ i, live i = true → kept i = true :=
    fun i selected => signature.live_kept slots live args placement.2.1 i selected
  have specs := fun i => (args i).code_spec source pure.funs pure.flags
    (pure.callBounds depth) (pure.callFits depth) sourceHost facts.runtime
    (Calls.at facts.calls depth) ((Command.covered_call callee args pool).mp covered i)
    (fun _ => depthParam)
  have fragments : ∀ fragment ∈
      [argsCode (fun i =>
        if (signature.params.get i).scalar then (args i).code (pool := pool) h slots base all
        else if signature.mode i = .owned then (args i).ownedCode h slots base kept
        else (args i).placeCode h slots),
        releaseWhere context slots (fun i => kept i && !live i)],
      Encoding.ProgramForm fragment ∧ Relocation.programClosed source.funcs.length fragment = true := by
    simpa only [Command.Ready, Command.fragments, Expr.usesFast_eq, all, kept] using ready
  have argumentsReady := fragments _ (List.mem_cons_self ..)
  have cleanupReady := fragments _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have argumentRoom : ∀ i : Fin signature.params.length,
      base + (if signature.mode i = .owned then copyWidth (signature.params.get i)
        else (args i).width) ≤ h := fun i =>
    (Nat.add_le_add_left (le_argsMax (fun i => if signature.mode i = .owned then
      copyWidth (signature.params.get i) else (args i).width) i) base).trans room
  obtain ⟨function, lookup, arity⟩ := facts.effectFunctions callee
  have noImport : target.imports[Wrappers.effectIndex source callee.index]? = none :=
    List.getElem?_eq_none (by
      rw [facts.imports, ABI.imports_length]
      simp only [Wrappers.effectIndex, Module.extraIndex]
      omega)
  have targetCap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535 := by
    rw [PureTransport.memoryCap_zero_eq facts.layout.memoryCap]
    exact cap
  simp only [Command.code, Expr.usesFast_eq, List.append_assoc]
  refine wp_effect_depth depthParam ?_
  refine wp_arguments (Q := Q) (targetHost := targetHost) (sourceHost := sourceHost)
    (funs := pure.funs) (flags := pure.flags) (bounds := pure.callBounds depth)
    (fits := pure.callFits depth) (all := all) (kept := kept)
    facts.runtime facts.layout facts.profile specs uses keptAll
    (fun _ owned => paramMode_owned owned) (fun i scalar _ => placement.1 i scalar)
    (signature.kept_owned slots live args placement.2.1) placement.2.2 positions rfl
    vars at_ (safe.values _) cap low argumentRoom argumentsReady.1 argumentsReady.2
    (fun failure final sameWorld => .trapped final "unreachable"
      (CommandResult.resource_refl (call_arguments_allowed chargeEq resources failure) sameWorld)) ?_
  intro argumentHeap arguments argumentLocals params fresh prepared sameWorld
  have prepared := prepared.ofValues
  have calleeBudget : aborts = false →
      argumentHeap.Within (PureTransport.erase arguments) source (budget - charge) ∧
        Resource.CallPrefixBound (observedHost host) pure program callee (depth + 1)
          (Env.ofFn fun i => (args i).denote pure.funs env) arguments.host (budget - charge) := by
    intro noAbort
    obtain ⟨within, bounded⟩ := resources noAbort
    exact prepared.call_budget chargeEq sameWorld within bounded
  have suffix : wp target (.call (Wrappers.effectIndex source callee.index) ::
        Relocation.program (releaseWhere context slots (fun i => kept i && !live i))) Q
      arguments { argumentLocals with values := (.i64 (depth + 1) :: params).reverse ++ locals.values }
      targetHost := by
    refine wp_cost_effect_helper (calls callee) noImport lookup arity valid prepared.step.at_
      prepared.rep prepared.separate (prepared.pool_input uses safe) (prepared.scratch uses scratch)
      (by rw [prepared.step.cap target]; exact targetCap) calleeBudget ?_ ?_
    · intro value finalHeap final words trace spent calleeFits execution step rep top
      have callAfter := prepared.call uses keptAll vars scratch step rep
      have updated : After env slots all kept base heap initial locals signature.result value
          finalHeap final { argumentLocals with values := words.reverse ++ locals.values } words :=
        ⟨callAfter.step, callAfter.frame.trans Frame.ofValues,
          callAfter.holds, callAfter.rep, callAfter.apart⟩
      rw [← List.append_nil
        (Relocation.program (releaseWhere context slots (fun i => kept i && !live i)))]
      refine wp_release_context (sourceHost := sourceHost) (targetHost := targetHost)
        (rest := []) facts.runtime facts.layout facts.profile cleanupReady.1 cleanupReady.2
        updated.holds updated.step.at_
        (fun i selected => by simp only [Bool.and_eq_true] at selected; exact selected.1) ?_
      intro releasedHeap released evolution releaseTop releasedWorld
      have retained : ∀ i, live i = true → (kept i && !(kept i && !live i)) = true :=
        fun i selected => by simp only [selected, liveKept i selected,
          Bool.not_true, Bool.and_false, Bool.not_false, Bool.and_self]
      have resultAfter := After.release vars scratch updated keptAll liveKept
        (evolution.mono retained)
      have sourceCall := Resource.ResourceExec.call (depth := depth) (modes := slots.map Slot.mode)
        (live := live) (args := args) (env := env)
        (show Resource.ResourceCall (observedHost host) pure program callee (depth + 1)
          (Env.ofFn fun i => (args i).denote pure.funs env) initial.host trace
          (.returned value) released.host spent calleeFits from by
            rw [releasedWorld, ← sameWorld]
            exact execution)
      rw [wp_nil]
      refine CostCommandResult.returned value releasedHeap released
        { argumentLocals with values := words.reverse ++ locals.values } words trace
        (charge + spent) (fits && calleeFits) sourceCall resultAfter ?_
      intro bothFit
      simp only [Bool.and_eq_true] at bothFit
      have argumentFits : (argsAll fun i => (args i).fits pure.funs (pure.callFits depth) env) = true := by
        simpa only [fits, Resource.PureContext.argumentFits, Resource.PureContext.exprFits] using bothFit.1
      have argumentTop := prepared.top argumentFits
      rw [← chargeEq] at argumentTop
      have calleeTop := top bothFit.2
      have sameTop := congrArg UInt64.toNat releaseTop
      omega
    · intro final message classification
      cases classification with
      | terminal final trace outcome message execution ending =>
          exact .trapped final message (.terminal final trace outcome message
            (by rw [← sameWorld]; exact execution) ending)
      | resource final trace residual allowed progress =>
          exact .trapped final "unreachable" (.resource final trace residual allowed
            (by rw [← sameWorld]; exact progress))
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
    Command.denote, all, kept] using suffix

end Verified.Wasi
