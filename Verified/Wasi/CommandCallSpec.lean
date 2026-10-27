import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CallOwnership
import Verified.Wasi.CallCommand

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_effect_depth {World : Type} {target : Wasm.Module} {targetHost : HostEnv World}
    {initial : Store World} {locals : Locals} {depth : UInt64} {rest : Program}
    {Q : Assertion World} (parameters : locals.params.head? = some (.i64 depth))
    (next : wp target rest Q initial
      { locals with values := .i64 (depth + 1) :: locals.values } targetHost) :
    wp target ([.localGet 0, .constI64 1, .addI64] ++ rest) Q initial locals targetHost := by
  have depthLocal : locals.get 0 = some (.i64 depth) := by
    cases words : locals.params with
    | nil => simp only [words, List.head?_nil, reduceCtorEq] at parameters
    | cons value tail =>
        have valueEq : value = .i64 depth := by
          simpa only [words, List.head?_cons, Option.some.injEq] using parameters
        simp [Locals.get, words, valueEq]
  simpa only [List.cons_append, List.nil_append, wp_localGet_cons, depthLocal,
    wp_constI64_cons, wp_addI64_cons] using next

theorem command_call_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {signature : EffectSig}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (callee : EffectVar effectSigs signature)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
    CommandCodeSpec source target pure effects pool (.call callee args) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ depthParam positions vars at_ safe scratch cap low room ready covered place
  let all := fun i => live i || argsAny fun j => (args j).uses i
  let kept := fun i => all i &&
    !(argsAny fun j => signature.callMoves slots live args j && (args j).uses i)
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
  refine wp_arguments (targetHost := targetHost) (sourceHost := sourceHost)
    (funs := pure.funs) (flags := pure.flags) (bounds := pure.callBounds depth)
    (fits := pure.callFits depth) (all := all) (kept := kept)
    facts.runtime facts.layout facts.profile specs uses keptAll
    (fun _ owned => paramMode_owned owned) (fun i scalar _ => placement.1 i scalar)
    (signature.kept_owned slots live args placement.2.1) placement.2.2 positions rfl
    vars at_ (safe.values _) cap low argumentRoom argumentsReady.1 argumentsReady.2
    (fun _ final sameWorld => CommandResult.resource_refl rfl sameWorld) ?_
  intro argumentHeap arguments argumentLocals words fresh prepared sameWorld
  have prepared := prepared.ofValues
  have suffix := wp_call_after_arguments (sourceHost := sourceHost) facts.runtime facts.layout
    facts.profile (facts.effectCalls callee) noImport lookup arity valid vars safe scratch uses
    keptAll liveKept prepared sameWorld targetCap cleanupReady.1 cleanupReady.2
    (depth := depth + 1)
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
    Command.denote, all, kept] using suffix

end Verified.Wasi
