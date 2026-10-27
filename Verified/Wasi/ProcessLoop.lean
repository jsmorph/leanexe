import LeanExe.ProofKit.PartialLoop
import LeanExe.Wasi.ProcessRelations
import Verified.Wasi.CommandSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi

inductive ProcessIterationResult {World σ : Type} (host : Host World) (process : Process σ)
    (current : ProcessStep σ) (world : World)
    (represented : ProcessStep σ → Store World → Locals → Prop) (values : List Value) :
    Continuation World → Prop where
  | stopped (final : Store World) (after : Locals)
      (sameWorld : final.host = world) (stopped : current.running = false)
      (rep : represented current final after) :
      ProcessIterationResult host process current world represented values (.Break 1 final after)
  | next (result : ProcessStep σ) (final : Store World) (after : Locals) (trace : List Event)
      (running : current.running = true)
      (execution : LeanExe.Wasi.Exec host (process.step current.state)
        world trace (.returned result) final.host)
      (rep : represented result final { after with values }) :
      ProcessIterationResult host process current world represented values (.Break 0 final after)
  | terminal (final : Store World) (trace : List Event) (outcome : Outcome (ProcessStep σ))
      (message : String) (running : current.running = true)
      (execution : LeanExe.Wasi.Exec host (process.step current.state) world trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      ProcessIterationResult host process current world represented values (.Trap final message)
  | resource (final : Store World) (trace : List Event) (residual : Action (ProcessStep σ))
      (running : current.running = true)
      (progress : LeanExe.Wasi.Prefix host (process.step current.state)
        world trace residual final.host) :
      ProcessIterationResult host process current world represented values (.Trap final "unreachable")

inductive ProcessLoopResult {World σ : Type} (host : Host World) (process : Process σ)
    (initial : ProcessStep σ) (world : World)
    (represented : ProcessStep σ → Store World → Locals → Prop) : Continuation World → Prop where
  | stopped (current : ProcessStep σ) (final : Store World) (after : Locals) (trace : List Event)
      (history : Process.Progress host process initial world trace current final.host)
      (stopped : current.running = false) (rep : represented current final after) :
      ProcessLoopResult host process initial world represented (.Break 0 final after)
  | terminal (final : Store World) (trace : List Event) (outcome : Outcome UInt64) (message : String)
      (execution : Process.Continue host process initial world trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      ProcessLoopResult host process initial world represented (.Trap final message)
  | resource (final : Store World) (trace : List Event) (residual : Action (ProcessStep σ))
      (progress : Process.Pending host process initial world trace residual final.host) :
      ProcessLoopResult host process initial world represented (.Trap final "unreachable")

def ProcessLoopInvariant {World σ : Type} (host : Host World) (process : Process σ)
    (initial : ProcessStep σ) (world : World)
    (represented : ProcessStep σ → Store World → Locals → Prop)
    (store : Store World) (locals : Locals) : Prop :=
  ∃ trace current,
    Process.Progress host process initial world trace current store.host ∧
    represented current store locals

theorem ProcessIterationResult.advance {World σ : Type} {host : Host World} {process : Process σ}
    {initial current : ProcessStep σ} {world : World} {store : Store World}
    {represented : ProcessStep σ → Store World → Locals → Prop} {values : List Value}
    {before : List Event} {continuation : Continuation World}
    (history : Process.Progress host process initial world before current store.host)
    (iteration : ProcessIterationResult host process current store.host represented values continuation) :
    PartialLoopPost (ProcessLoopInvariant host process initial world represented)
      (ProcessLoopResult host process initial world represented) values continuation := by
  cases iteration with
  | stopped final after sameWorld stopped rep =>
      exact ProcessLoopResult.stopped current final after before
        (by simpa only [sameWorld] using history) stopped rep
  | next result final after trace running execution rep =>
      exact ⟨before ++ trace, result, history.next running execution, rep⟩
  | terminal final trace outcome message running execution terminal =>
      cases outcome with
      | returned result => exact terminal.elim
      | exited status =>
          have currentExecution : Process.Continue host process current store.host trace
              (.exited status) final.host := by
            simp only [Process.Continue, running, ↓reduceIte]
            exact Process.Exec.exit execution
          exact ProcessLoopResult.terminal final (before ++ trace) (.exited status) message
            (history.finish currentExecution) terminal
      | trapped cause =>
          have currentExecution : Process.Continue host process current store.host trace
              (.trapped cause) final.host := by
            simp only [Process.Continue, running, ↓reduceIte]
            exact Process.Exec.trap execution
          exact ProcessLoopResult.terminal final (before ++ trace) (.trapped cause) message
            (history.finish currentExecution) terminal
  | resource final trace residual running progress =>
      exact ProcessLoopResult.resource final (before ++ trace) residual
        ⟨before, current, store.host, trace, history, running, progress, rfl⟩

theorem pwp_process_loop {World σ : Type} {host : Host World} {process : Process σ}
    {module : Wasm.Module} {body : Program} {targetHost : HostEnv World}
    {initial : ProcessStep σ} {store : Store World} {locals : Locals}
    (represented : ProcessStep σ → Store World → Locals → Prop)
    (initialRep : represented initial store locals)
    (iteration : ∀ current store locals, represented current store locals →
      pwp module body (ProcessIterationResult host process current store.host represented locals.values)
        store locals targetHost) :
    pwp module [.loop 0 0 body [] []]
      (ProcessLoopResult host process initial store.host represented) store locals targetHost := by
  refine pwp_loop (module := module) (body := body)
    (post := ProcessLoopResult host process initial store.host represented)
    (store := store) (locals := locals) (host := targetHost)
    (ProcessLoopInvariant host process initial store.host represented) ?_ ?_
  · exact ⟨[], initial, Process.Progress.refl initial store.host, initialRep⟩
  · intro currentStore currentLocals held
    obtain ⟨trace, current, history, rep⟩ := held
    exact (iteration current currentStore currentLocals rep).conseq
      (fun _ result => result.advance history)

inductive ProcessBlockResult {World σ : Type} (host : Host World) (process : Process σ)
    (initial : ProcessStep σ) (world : World)
    (represented : ProcessStep σ → Store World → Locals → Prop) (values : List Value) :
    Continuation World → Prop where
  | stopped (current : ProcessStep σ) (final : Store World) (after : Locals) (trace : List Event)
      (history : Process.Progress host process initial world trace current final.host)
      (stopped : current.running = false) (rep : represented current final after) :
      ProcessBlockResult host process initial world represented values
        (.Fallthrough final { after with values })
  | terminal (final : Store World) (trace : List Event) (outcome : Outcome UInt64) (message : String)
      (execution : Process.Continue host process initial world trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      ProcessBlockResult host process initial world represented values (.Trap final message)
  | resource (final : Store World) (trace : List Event) (residual : Action (ProcessStep σ))
      (progress : Process.Pending host process initial world trace residual final.host) :
      ProcessBlockResult host process initial world represented values (.Trap final "unreachable")

theorem pwp_process_block {World σ : Type} {host : Host World} {process : Process σ}
    {module : Wasm.Module} {body : Program} {targetHost : HostEnv World}
    {initial : ProcessStep σ} {store : Store World} {locals : Locals}
    (represented : ProcessStep σ → Store World → Locals → Prop)
    (initialRep : represented initial store locals)
    (iteration : ∀ current store locals, represented current store locals →
      pwp module body (ProcessIterationResult host process current store.host represented locals.values)
        store locals targetHost) :
    pwp module [.block 0 0 [.loop 0 0 body [] []] [] []]
      (ProcessBlockResult host process initial store.host represented locals.values)
      store locals targetHost := by
  have loop := pwp_process_loop represented initialRep iteration
  intro fuel completed
  cases fuel with
  | zero => exact False.elim (completed (by simp only [exec, execOne.eq_def]))
  | succ fuel =>
      rw [exec_block_cons] at completed ⊢
      have loopCompleted : exec fuel module store locals [.loop 0 0 body [] []] targetHost ≠
          .OutOfFuel := by
        intro exhausted
        simp only [exhausted] at completed
        exact completed rfl
      have classification := loop fuel loopCompleted
      generalize loopResult : exec fuel module store locals [.loop 0 0 body [] []] targetHost =
        result at classification
      rw [loopResult] at completed
      cases classification with
      | stopped current final after trace history stopped rep =>
          simpa only [List.take_zero, List.drop_zero, List.nil_append, exec] using
            ProcessBlockResult.stopped current final after trace history stopped rep
      | terminal final trace outcome message nativeExecution terminal =>
          exact ProcessBlockResult.terminal final trace outcome message nativeExecution terminal
      | resource final trace residual progress =>
          exact ProcessBlockResult.resource final trace residual progress

end Verified.Wasi
