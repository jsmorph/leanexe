import Verified.Wasi.ProcessLoop
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Block

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def ProcessRankDecrease {World : Type} (rank : Store World → Locals → Nat)
    (store : Store World) (locals : Locals) : Assertion World
  | .Break 0 final after => rank final { after with values := locals.values } < rank store locals
  | _ => True

def RankedProcessIterationResult {World σ : Type} (host : Host World) (process : Process σ)
    (current : ProcessStep σ) (represented : ProcessStep σ → Store World → Locals → Prop)
    (rank : Store World → Locals → Nat) (store : Store World) (locals : Locals) : Assertion World :=
  fun continuation =>
    ProcessIterationResult host process current store.host represented locals.values continuation ∧
    ProcessRankDecrease rank store locals continuation

theorem wp_process_loop_ranked {World σ : Type} {host : Host World} {process : Process σ}
    {module : Wasm.Module} {body : Program} {targetHost : HostEnv World}
    {initial : ProcessStep σ} {store : Store World} {locals : Locals}
    (represented : ProcessStep σ → Store World → Locals → Prop)
    (rank : Store World → Locals → Nat)
    (initialRep : represented initial store locals)
    (iteration : ∀ current store locals, represented current store locals →
      wp module body (RankedProcessIterationResult host process current represented rank store locals)
        store locals targetHost) :
    wp module [.loop 0 0 body [] []]
      (ProcessLoopResult host process initial store.host represented) store locals targetHost := by
  refine wp_loop_cons (m := module) (ps := 0) (rs := 0) (body := body) (rest := [])
    (Q := ProcessLoopResult host process initial store.host represented)
    (st := store) (s := locals) (env := targetHost)
    (ProcessLoopInvariant host process initial store.host represented) rank ?_ ?_
  · exact ⟨[], initial, Process.Progress.refl initial store.host, initialRep⟩
  · intro currentStore currentLocals held
    obtain ⟨trace, current, history, rep⟩ := held
    apply wp.conseq (h := iteration current currentStore currentLocals rep)
    intro continuation classified
    obtain ⟨result, decreased⟩ := classified
    have advanced := result.advance history
    cases continuation with
    | Fallthrough final after =>
        change wp module [] (ProcessLoopResult host process initial store.host represented)
          final { after with values := currentLocals.values } targetHost
        rw [wp_nil]
        simpa only [PartialLoopPost, List.take_zero, List.drop_zero, List.nil_append] using advanced
    | Break index final after =>
        cases index with
        | zero =>
            exact ⟨by simpa only [PartialLoopPost, List.take_zero, List.drop_zero, List.nil_append]
                using advanced,
              by simpa only [ProcessRankDecrease, List.take_zero, List.drop_zero, List.nil_append]
                using decreased⟩
        | succ index => exact advanced
    | _ => exact advanced

theorem wp_process_block_ranked {World σ : Type} {host : Host World} {process : Process σ}
    {module : Wasm.Module} {body : Program} {targetHost : HostEnv World}
    {initial : ProcessStep σ} {store : Store World} {locals : Locals}
    (represented : ProcessStep σ → Store World → Locals → Prop)
    (rank : Store World → Locals → Nat)
    (initialRep : represented initial store locals)
    (iteration : ∀ current store locals, represented current store locals →
      wp module body (RankedProcessIterationResult host process current represented rank store locals)
        store locals targetHost) :
    wp module [.block 0 0 [.loop 0 0 body [] []] [] []]
      (ProcessBlockResult host process initial store.host represented locals.values)
      store locals targetHost := by
  have loop := wp_process_loop_ranked represented rank initialRep iteration
  refine wp_block_cons (m := module) (ps := 0) (rs := 0)
    (body := [.loop 0 0 body [] []]) (rest := [])
    (Q := ProcessBlockResult host process initial store.host represented locals.values)
    (st := store) (s := locals) (env := targetHost) ?_
  apply wp.conseq (h := loop)
  intro continuation classification
  cases classification with
  | stopped current final after trace history stopped rep =>
      change wp module [] (ProcessBlockResult host process initial store.host represented locals.values)
        final { after with values := locals.values } targetHost
      rw [wp_nil]
      simpa only [List.take_zero, List.drop_zero, List.nil_append] using
        ProcessBlockResult.stopped current final after trace history stopped rep
  | terminal final trace outcome message nativeExecution terminal =>
      exact ProcessBlockResult.terminal final trace outcome message nativeExecution terminal
  | resource final trace residual progress =>
      exact ProcessBlockResult.resource final trace residual progress

end Verified.Wasi
