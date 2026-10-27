import Verified.Wasi.LoopControl
import LeanExe.Wasi.Prefix

namespace Verified.Wasi

open LeanExe.Wasi

def loopResidual (count index : UInt64) (test : UInt64 → σ → Bool)
    (step : UInt64 → σ → Action σ) (next : σ → Action α) (state : σ) : Action α :=
  resumeLoop test step next (count.toNat - index.toNat) index.toNat state

theorem loop_residual_done (count : UInt64) (test : UInt64 → σ → Bool)
    (step : UInt64 → σ → Action σ) (next : σ → Action α) (state : σ) :
    loopResidual count count test step next state = next state := by
  simp only [loopResidual, Nat.sub_self, resumeLoop]

theorem loop_remaining_succ {index count : UInt64} (bound : index < count) :
    count.toNat - index.toNat = (count.toNat - (index + 1).toNat) + 1 := by
  rw [loop_increment_toNat bound]
  have less := UInt64.lt_iff_toNat_lt.mp bound
  omega

theorem loop_successor_le {index count : UInt64} (bound : index < count) : index + 1 ≤ count := by
  apply UInt64.le_iff_toNat_le.mpr
  rw [loop_increment_toNat bound]
  have less := UInt64.lt_iff_toNat_lt.mp bound
  omega

theorem loop_residual_unfold {index count : UInt64} (bound : index < count)
    (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ)
    (next : σ → Action α) (state : σ) :
    loopResidual count index test step next state =
      if test index state then Action.bind (step index state)
        (loopResidual count (index + 1) test step next) else next state := by
  unfold loopResidual
  rw [loop_remaining_succ bound, resumeLoop, UInt64.ofNat_toNat]
  rw [loop_increment_toNat bound]

structure LoopProgress {World : Type} (host : Host World)
    (count : UInt64) (initialState : σ) (test : UInt64 → σ → Bool)
    (step : UInt64 → σ → Action σ) (next : σ → Action α) (initialWorld : World)
    (index : UInt64) (state : σ) (trace : List Event) (world : World) : Prop where
  bound : index ≤ count
  progress : Prefix host (.loop count initialState test step next) initialWorld trace
    (loopResidual count index test step next state) world

namespace LoopProgress

theorem initial {World : Type} {host : Host World} (count : UInt64) (state : σ)
    (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ)
    (next : σ → Action α) (world : World) :
    LoopProgress host count state test step next world 0 state [] world := by
  refine ⟨UInt64.le_iff_toNat_le.mpr (Nat.zero_le _), ?_⟩
  simpa only [loopResidual, UInt64.toNat_zero, Nat.sub_zero] using
    (Prefix.loop (host := host) (count := count) (state := state) (test := test)
      (step := step) (next := next) (world := world))

theorem after_return {World : Type} {host : Host World}
    {count index : UInt64} {initialState state afterState : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world after final : World} {trace first rest : List Event} {residual : Action α}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (bound : index < count) (runs : test index state = true)
    (returned : Exec host (step index state) world first (.returned afterState) after)
    (remaining : Prefix host (loopResidual count (index + 1) test step next afterState)
      after rest residual final) :
    Prefix host (.loop count initialState test step next) initialWorld
      (trace ++ (first ++ rest)) residual final := by
  have progress := history.progress
  rw [loop_residual_unfold bound, ite_eq_left runs] at progress
  exact progress.trans (Prefix.bind_after returned remaining)

theorem advance {World : Type} {host : Host World}
    {count index : UInt64} {initialState state afterState : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world after : World} {trace first : List Event}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (bound : index < count) (runs : test index state = true)
    (returned : Exec host (step index state) world first (.returned afterState) after) :
    LoopProgress host count initialState test step next initialWorld
      (index + 1) afterState (trace ++ first) after := by
  refine ⟨loop_successor_le bound, ?_⟩
  simpa only [List.append_nil] using
    history.after_return bound runs returned (Prefix.refl _ after)

theorem resource {World : Type} {host : Host World}
    {count index : UInt64} {initialState state : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world final : World} {trace first : List Event} {residual : Action σ}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (bound : index < count) (runs : test index state = true)
    (interrupted : Prefix host (step index state) world first residual final) :
    Prefix host (.loop count initialState test step next) initialWorld (trace ++ first)
      (Action.bind residual (loopResidual count (index + 1) test step next)) final := by
  have progress := history.progress
  rw [loop_residual_unfold bound, ite_eq_left runs] at progress
  exact progress.trans interrupted.bind

theorem complete {World : Type} {host : Host World}
    {count index : UInt64} {initialState state : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world final : World} {trace rest : List Event} {outcome : Outcome α}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (remaining : Exec host (loopResidual count index test step next state)
      world rest outcome final) :
    Exec host (.loop count initialState test step next) initialWorld (trace ++ rest) outcome final :=
  history.progress.complete remaining

theorem done {World : Type} {host : Host World}
    {count : UInt64} {initialState state : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world final : World} {trace rest : List Event} {outcome : Outcome α}
    (history : LoopProgress host count initialState test step next initialWorld count state trace world)
    (remaining : Exec host (next state) world rest outcome final) :
    Exec host (.loop count initialState test step next) initialWorld (trace ++ rest) outcome final := by
  apply history.complete
  simpa only [loop_residual_done] using remaining

theorem stopped {World : Type} {host : Host World}
    {count index : UInt64} {initialState state : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world final : World} {trace rest : List Event} {outcome : Outcome α}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (bound : index < count) (stops : test index state = false)
    (remaining : Exec host (next state) world rest outcome final) :
    Exec host (.loop count initialState test step next) initialWorld (trace ++ rest) outcome final := by
  apply history.complete
  simpa only [loop_residual_unfold bound, stops, Bool.false_eq_true, ite_false] using remaining

theorem exited {World : Type} {host : Host World}
    {count index code : UInt64} {initialState state : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world final : World} {trace first : List Event}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (bound : index < count) (runs : test index state = true)
    (terminal : Exec host (step index state) world first (.exited code) final) :
    Exec host (.loop count initialState test step next) initialWorld
      (trace ++ first) (.exited code) final := by
  have stopped : LoopExec host ((count.toNat - (index + 1).toNat) + 1) index.toNat state
      test step next world first (.exited code) final :=
    .exit (by simpa only [UInt64.ofNat_toNat] using runs)
      (by simpa only [UInt64.ofNat_toNat] using terminal)
  apply history.complete
  simpa only [loopResidual, loop_remaining_succ bound] using stopped.resume

theorem trapped {World : Type} {host : Host World}
    {count index : UInt64} {initialState state : σ}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    {initialWorld world final : World} {trace first : List Event} {message : String}
    (history : LoopProgress host count initialState test step next initialWorld index state trace world)
    (bound : index < count) (runs : test index state = true)
    (terminal : Exec host (step index state) world first (.trapped message) final) :
    Exec host (.loop count initialState test step next) initialWorld
      (trace ++ first) (.trapped message) final := by
  have stopped : LoopExec host ((count.toNat - (index + 1).toNat) + 1) index.toNat state
      test step next world first (.trapped message) final :=
    .trap (by simpa only [UInt64.ofNat_toNat] using runs)
      (by simpa only [UInt64.ofNat_toNat] using terminal)
  apply history.complete
  simpa only [loopResidual, loop_remaining_succ bound] using stopped.resume

end LoopProgress

end Verified.Wasi
