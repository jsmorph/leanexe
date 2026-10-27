import Verified.Wasi.ProcessRunProofs
import LeanExe.Wasi.ProcessRelated

namespace Verified.Wasi

open Wasm LeanExe.Wasi

theorem ProcessCommandExec.transport_back {World σ τ : Type} {host : Host World}
    {states : σ → τ → Prop} {left : Process σ} {right : Process τ}
    {leftBegin : Action (ProcessStep σ)} {rightBegin : Action (ProcessStep τ)}
    (processes : Process.Rel states left right)
    (begins : Action.Rel (ProcessStep.Rel states) leftBegin rightBegin)
    {world trace outcome final}
    (execution : ProcessCommandExec host rightBegin right world trace outcome final) :
    ProcessCommandExec host leftBegin left world trace outcome final := by
  cases execution with
  | next started continued finished =>
      obtain ⟨native, started, values⟩ := begins.exec_back started
      cases values with
      | returned state => exact .next started (processes.continue_back state continued) finished
  | beginExit execution =>
      obtain ⟨native, execution, values⟩ := begins.exec_back execution
      cases values with
      | exited status => exact .beginExit execution
  | beginTrap execution =>
      obtain ⟨native, execution, values⟩ := begins.exec_back execution
      cases values with
      | trapped message => exact .beginTrap execution

theorem ProcessCommandPrefix.transport_back {World σ τ : Type} {host : Host World}
    {states : σ → τ → Prop} {left : Process σ} {right : Process τ}
    {leftBegin : Action (ProcessStep σ)} {rightBegin : Action (ProcessStep τ)}
    (processes : Process.Rel states left right)
    (begins : Action.Rel (ProcessStep.Rel states) leftBegin rightBegin)
    {world trace residual final}
    (progress : ProcessCommandPrefix host rightBegin right world trace residual final) :
    ∃ native, ProcessCommandPrefix host leftBegin left world trace native final ∧
      Action.Rel (ProcessStep.Rel states) native residual := by
  cases progress with
  | begin progress =>
      obtain ⟨native, progress, related⟩ := begins.transportPrefixBack progress
      exact ⟨native, .begin progress, related⟩
  | next started progress =>
      obtain ⟨native, started, values⟩ := begins.exec_back started
      cases values with
      | returned state =>
          obtain ⟨residual, progress, related⟩ := processes.pending_back state progress
          exact ⟨residual, .next started progress, related⟩

theorem ProcessEntryResult.transport_back {World σ τ : Type} {host : Host World}
    {states : σ → τ → Prop} {left : Process σ} {right : Process τ}
    {leftBegin : Action (ProcessStep σ)} {rightBegin : Action (ProcessStep τ)}
    (processes : Process.Rel states left right)
    (begins : Action.Rel (ProcessStep.Rel states) leftBegin rightBegin)
    {world continuation}
    (classification : ProcessEntryResult host rightBegin right world continuation) :
    ProcessEntryResult host leftBegin left world continuation := by
  cases classification with
  | terminal final trace outcome message execution terminal =>
      exact .terminal final trace outcome message (execution.transport_back processes begins) terminal
  | resource final trace residual progress =>
      obtain ⟨native, progress, _⟩ := progress.transport_back processes begins
      exact .resource final trace native progress

theorem ProcessEntryRunResult.transport_back {World σ τ : Type} {host : Host World}
    {states : σ → τ → Prop} {left : Process σ} {right : Process τ}
    {leftBegin : Action (ProcessStep σ)} {rightBegin : Action (ProcessStep τ)}
    (processes : Process.Rel states left right)
    (begins : Action.Rel (ProcessStep.Rel states) leftBegin rightBegin)
    {world result}
    (classification : ProcessEntryRunResult host rightBegin right world result) :
    ProcessEntryRunResult host leftBegin left world result := by
  cases result with
  | Trap final message => exact ProcessEntryResult.transport_back processes begins classification
  | _ => exact False.elim classification

end Verified.Wasi
