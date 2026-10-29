import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.ResourceCompilerCost
import Verified.Wasi.ExitCommand
import Verified.AlignedCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cost_command_exit_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {result : ResultTy}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (status : Expr pureSigs context .word) :
    CostCommandCodeSpec source target pure program pool (.exit (result := result) status) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ depthParam positions vars at_ safe _ cap low room ready covered place resource
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := status.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have noCoerce : coerceCode h .word (status.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have allowed : (!(status.fits pure.funs (pure.callFits depth) env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost pure.funs pure.flags (pure.callBounds depth) status env slots [] live
          (PureTransport.erase initial) locals))) = true → aborts = true := by
    intro failure
    cases aborts with
    | true => rfl
    | false =>
      obtain ⟨within, bounded⟩ := resource rfl
      obtain ⟨withinStatus, fitsStatus⟩ := bounded.exit_resources locals within
      simp only [Resource.PureContext.exprFits] at fitsStatus
      simp [fitsStatus, withinStatus] at failure
  have execution := wp_command_exit (effectFuns := program.funs pure.funs) (result := result)
    facts.runtime facts.layout facts.profile facts.imports valid spec
    (by simpa only [noCoerce, List.append_nil] using fragment.1)
    (by simpa only [noCoerce, List.append_nil] using fragment.2)
    positions rfl vars at_ safe cap low room place allowed
  refine wp.conseq (fun continuation classification => ?_) execution
  cases classification with
  | returned value finalHeap final finalLocals words trace run after => cases run
  | terminal final trace outcome message run terminal =>
    exact .trapped final message (.terminal final trace outcome message run terminal)
  | resource final trace residual allowed progress =>
    exact .trapped final "unreachable" (.resource final trace residual allowed progress)

end Verified.Wasi
