import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.ResourceCompilerCost
import Verified.AlignedCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cost_command_unit_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} :
    CostCommandCodeSpec source target pure program pool (.unit (context := context)) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    _ _ _ _ vars at_ _ _ _ _ _ _ _ _ _
  simp only [Command.uses, Bool.or_false] at vars ⊢
  change wp target [] _ initial locals targetHost
  rw [wp_nil]
  have result : CostCommandResult host pure program .unit depth env slots live live base heap initial
      locals aborts (.Fallthrough initial { locals with values := ([] : List Value).reverse ++ locals.values }) :=
    CostCommandResult.returned (result := .unit) () heap initial locals [] [] 0 true
      (.unit program depth (slots.map Slot.mode) live env initial.host)
      (After.unit at_ vars) (by intro _; omega)
  cases locals
  simpa only [List.reverse_nil, List.nil_append] using result

theorem cost_command_ret_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {type : Ty}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (value : Expr pureSigs context type) :
    CostCommandCodeSpec source target pure program pool (.ret value) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    _ _ depthParam positions vars at_ safe _ cap low room ready covered place resource
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := value.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have allowed : (!(value.fits pure.funs (pure.callFits depth) env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost pure.funs pure.flags (pure.callBounds depth) value env slots [] live
          (PureTransport.erase initial) locals))) = true → aborts = true := by
    intro failure
    cases aborts with
    | true => rfl
    | false =>
      obtain ⟨within, bounded⟩ := resource rfl
      obtain ⟨withinValue, fitsValue⟩ := bounded.ret_resources locals within
      simp only [Resource.PureContext.exprFits] at fitsValue
      simp [fitsValue, withinValue] at failure
  have execution := wp_return facts.runtime facts.layout facts.profile spec fragment.1 fragment.2
    positions rfl vars at_ safe cap low room place (rest := [])
    (targetHost := targetHost)
    (Q := CostCommandResult host pure program (.ret value) depth env slots
      (fun i => live i || value.uses i) live base heap initial locals aborts)
    (fun failure final sameWorld =>
      CostCommandResult.trapped final "unreachable" (CommandResult.resource_refl (allowed failure) sameWorld))
    (fun finalHeap finalStore finalLocals words after sameWorld top => by
      rw [wp_nil]
      refine CostCommandResult.returned (result := .value type) (value.denote pure.funs env)
        finalHeap finalStore finalLocals words []
        (pure.ownedCost depth (slots.map Slot.mode) live value env) (pure.exprFits depth value env)
        ?_ after ?_
      · rw [sameWorld]
        exact .ret program depth (slots.map Slot.mode) live value env initial.host
      · intro fitsValue
        simpa only [pure.returnCost_nil] using top fitsValue)
  simpa only [Command.code, Command.uses, List.append_nil] using execution

end Verified.Wasi
