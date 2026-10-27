import LeanExe.Wasi.Interpreter

namespace LeanExe.Wasi

structure ProcessStep (σ : Type) where
  running : Bool
  status : UInt64
  state : σ

structure Process (σ : Type) where
  initial : σ
  step : σ → Action (ProcessStep σ)

namespace Process

inductive Exec {World σ : Type} (host : Host World) (process : Process σ) :
    σ → World → List Event → Outcome UInt64 → World → Prop where
  | done {state world trace result final}
      (execution : LeanExe.Wasi.Exec host (process.step state) world trace (.returned result) final)
      (stopped : result.running = false) :
      Exec host process state world trace (.returned result.status) final
  | next {state world first result middle rest outcome final}
      (execution : LeanExe.Wasi.Exec host (process.step state) world first (.returned result) middle)
      (running : result.running = true)
      (continuation : Exec host process result.state middle rest outcome final) :
      Exec host process state world (first ++ rest) outcome final
  | exit {state world trace status final}
      (execution : LeanExe.Wasi.Exec host (process.step state) world trace (.exited status) final) :
      Exec host process state world trace (.exited status) final
  | trap {state world trace message final}
      (execution : LeanExe.Wasi.Exec host (process.step state) world trace (.trapped message) final) :
      Exec host process state world trace (.trapped message) final

inductive Prefix {World σ : Type} (host : Host World) (process : Process σ) :
    σ → World → List Event → σ → World → Prop where
  | refl (state world) : Prefix host process state world [] state world
  | next {state world first result middle rest nextState final}
      (execution : LeanExe.Wasi.Exec host (process.step state) world first (.returned result) middle)
      (running : result.running = true)
      (continuation : Prefix host process result.state middle rest nextState final) :
      Prefix host process state world (first ++ rest) nextState final

theorem Prefix.exec {World σ : Type} {host : Host World} {process : Process σ}
    {state world first nextState middle rest outcome final}
    (history : Prefix host process state world first nextState middle)
    (restExecution : Exec host process nextState middle rest outcome final) :
    Exec host process state world (first ++ rest) outcome final := by
  induction history with
  | refl => exact restExecution
  | next execution running _ ih =>
      rw [List.append_assoc]
      exact .next execution running (ih restExecution)

theorem Exec.exited_marker {World σ : Type} {host : Host World} {process : Process σ}
    {state world trace outcome final}
    (execution : Exec host process state world trace outcome final) :
    host.exited final = outcome.exitMarker (host.exited world) := by
  induction execution with
  | done execution _ => exact execution.exited_marker
  | next execution _ _ ih =>
      have unchanged := execution.exited_marker
      dsimp only [Outcome.exitMarker] at unchanged
      rw [unchanged] at ih
      exact ih
  | exit execution => exact execution.exited_marker
  | trap execution => exact execution.exited_marker

partial def runFrom (process : Process σ) (host : NativeHost) (state : σ) :
    IO (Outcome UInt64) := do
  match ← (process.step state).run host with
  | .returned result =>
      if result.running then runFrom process host result.state
      else pure (.returned result.status)
  | .exited status => pure (.exited status)
  | .trapped message => pure (.trapped message)

def runStdio (process : Process σ) : IO (Outcome UInt64) := do
  process.runFrom (← NativeHost.stdio) process.initial

end Process
end LeanExe.Wasi
