import LeanExe.Wasi.Bind

namespace LeanExe.Wasi

def resumeLoop (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ)
    (next : σ → Action α) : Nat → Nat → σ → Action α
  | 0, _, state => next state
  | remaining + 1, index, state =>
    if test (UInt64.ofNat index) state then
      Action.bind (step (UInt64.ofNat index) state)
        (resumeLoop test step next remaining (index + 1))
    else next state

inductive Prefix {World : Type} (host : Host World) :
    {α : Type} → Action α → World → List Event → Action α → World → Prop where
  | refl (action : Action α) (world : World) : Prefix host action world [] action world
  | read_reject {capacity : UInt64} {next : ReadResult → Action α} {world}
      (hCapacity : 2 ^ 32 ≤ capacity.toNat) :
      Prefix host (.read capacity next) world [] (next ⟨61, Bytes.empty⟩) world
  | read_return {capacity : UInt64} {next : ReadResult → Action α}
      {world after errno committed}
      (hCapacity : capacity.toNat < 2 ^ 32)
      (hHost : host.read world capacity (.returned errno committed) after) :
      Prefix host (.read capacity next) world [.read capacity (.returned errno committed)]
        (next (readResult errno committed)) after
  | write_return {output : Output} {bytes : Bytes} {next : WriteResult → Action α}
      {world after errno committed}
      (hHost : host.write world output bytes (.returned errno committed) after) :
      Prefix host (.write output bytes next) world [.write output bytes (.returned errno committed)]
        (next (writeResult errno committed)) after
  | loop {count : UInt64} {state : σ} {test : UInt64 → σ → Bool}
      {step : UInt64 → σ → Action σ} {next : σ → Action α} {world} :
      Prefix host (.loop count state test step next) world []
        (resumeLoop test step next count.toNat 0 state) world
  | bind {action residual : Action α} {next : α → Action β} {world after trace}
      (hPrefix : Prefix host action world trace residual after) :
      Prefix host (Action.bind action next) world trace (Action.bind residual next) after
  | trans {action middle residual : Action α} {world after final first rest}
      (hFirst : Prefix host action world first middle after)
      (hRest : Prefix host middle after rest residual final) :
      Prefix host action world (first ++ rest) residual final

theorem resumeLoop_bind (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ)
    (next : σ → Action α) (continuation : α → Action β) (remaining index : Nat) (state : σ) :
    Action.bind (resumeLoop test step next remaining index state) continuation =
      resumeLoop test step (fun value => Action.bind (next value) continuation)
        remaining index state := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
    simp only [resumeLoop]
    split
    · rw [Action.bind_assoc]
      congr 1
      funext value
      exact ih (index + 1) value
    · rfl

theorem LoopExec.resume {World : Type} {host : Host World} {remaining index : Nat}
    {state : σ} {test step} {next : σ → Action α} {world final trace outcome}
    (h : LoopExec host remaining index state test step next world trace outcome final) :
    Exec host (resumeLoop test step next remaining index state) world trace outcome final := by
  induction remaining generalizing index state world trace outcome final with
  | zero => cases h with | zero hNext => exact hNext
  | succ remaining ih =>
    cases h with
    | stop hTest hNext =>
      simpa only [resumeLoop, hTest, Bool.false_eq_true, ite_false] using hNext
    | next hTest hStep hRest =>
      simpa only [resumeLoop, hTest, ite_true] using hStep.bind (ih hRest)
    | exit hTest hStep =>
      simpa only [resumeLoop, hTest, ite_true, List.append_nil] using
        hStep.bind (next := resumeLoop test step next remaining _) ⟨rfl, rfl, rfl⟩
    | trap hTest hStep =>
      simpa only [resumeLoop, hTest, ite_true, List.append_nil] using
        hStep.bind (next := resumeLoop test step next remaining _) ⟨rfl, rfl, rfl⟩

theorem Exec.of_resumeLoop {World : Type} {host : Host World} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α} (remaining : Nat) :
    ∀ {index state world trace outcome final},
      Exec host (resumeLoop test step next remaining index state) world trace outcome final →
        LoopExec host remaining index state test step next world trace outcome final := by
  induction remaining with
  | zero => intro index state world trace outcome final h; exact .zero h
  | succ remaining ih =>
    intro index state world trace outcome final h
    simp only [resumeLoop] at h
    split at h
    · rename_i hTest
      obtain ⟨after, first, middle, rest, hStep, hRest, rfl⟩ := Exec.bind_iff.mp h
      cases middle with
      | returned state' => exact .next hTest hStep (ih hRest)
      | exited code =>
        obtain ⟨rfl, rfl, rfl⟩ := hRest
        simpa only [List.append_nil] using LoopExec.exit hTest hStep
      | trapped message =>
        obtain ⟨rfl, rfl, rfl⟩ := hRest
        simpa only [List.append_nil] using LoopExec.trap hTest hStep
    · rename_i hTest
      exact .stop (by simpa only [Bool.not_eq_true] using hTest) h

theorem Exec.resumeLoop_iff {World : Type} {host : Host World} {remaining index : Nat}
    {state : σ} {test step} {next : σ → Action α} {world final trace outcome} :
    Exec host (resumeLoop test step next remaining index state) world trace outcome final ↔
      LoopExec host remaining index state test step next world trace outcome final :=
  ⟨Exec.of_resumeLoop remaining, LoopExec.resume⟩

theorem Prefix.complete {World : Type} {host : Host World} {action residual : Action α}
    {world after first} (h : Prefix host action world first residual after) :
    ∀ {rest outcome final}, Exec host residual after rest outcome final →
      Exec host action world (first ++ rest) outcome final := by
  induction h with
  | refl => intro rest outcome final hRun; exact hRun
  | read_reject hCapacity => intro rest outcome final hRun; exact .read_reject hCapacity hRun
  | read_return hCapacity hHost =>
    intro rest outcome final hRun
    exact .read_return hCapacity hHost hRun
  | write_return hHost =>
    intro rest outcome final hRun
    exact .write_return hHost hRun
  | loop =>
    intro rest outcome final hRun
    exact .loop (Exec.of_resumeLoop _ hRun)
  | bind hPrefix ih =>
    intro rest outcome final hRun
    obtain ⟨after, first, middle, tail, hFirst, hTail, rfl⟩ := Exec.bind_iff.mp hRun
    simpa only [List.append_assoc] using (ih hFirst).bind hTail
  | trans hFirst hRest ihFirst ihRest =>
    intro rest outcome final hRun
    simpa only [List.append_assoc] using ihFirst (ihRest hRun)

theorem Prefix.exited_eq {World : Type} {host : Host World} {action residual : Action α}
    {world after trace} (h : Prefix host action world trace residual after) :
    host.exited after = host.exited world := by
  induction h with
  | refl | read_reject | loop => rfl
  | read_return _ hHost => exact host.read_exited hHost
  | write_return hHost => exact host.write_exited hHost
  | bind _ ih => exact ih
  | trans _ _ ihFirst ihRest => exact ihRest.trans ihFirst

theorem LoopExec.returned_prefix {World : Type} {host : Host World}
    {test : UInt64 → σ → Bool} {step : UInt64 → σ → Action σ} {next : σ → Action α}
    (hStep : ∀ index state world trace value final,
      Exec host (step index state) world trace (.returned value) final →
        Prefix host (step index state) world trace (.pure value) final)
    (hNext : ∀ state world trace value final,
      Exec host (next state) world trace (.returned value) final →
        Prefix host (next state) world trace (.pure value) final)
    (remaining : Nat) : ∀ {index state world trace value final},
      LoopExec host remaining index state test step next world trace (.returned value) final →
        Prefix host (resumeLoop test step next remaining index state)
          world trace (.pure value) final := by
  induction remaining with
  | zero =>
    intro index state world trace value final hRun
    cases hRun with | zero hRun => exact hNext _ _ _ _ _ hRun
  | succ remaining ih =>
    intro index state world trace value final hRun
    cases hRun with
    | stop hTest hRun =>
      simpa only [resumeLoop, hTest, Bool.false_eq_true, ite_false] using hNext _ _ _ _ _ hRun
    | next hTest hBody hRun =>
      have hBodyPrefix := (hStep _ _ _ _ _ _ hBody).bind
        (next := resumeLoop test step next remaining (index + 1))
      simpa only [resumeLoop, hTest, ite_true] using hBodyPrefix.trans (ih hRun)

theorem Exec.returned_prefix {World : Type} {host : Host World} (action : Action α) :
    ∀ {world trace value final}, Exec host action world trace (.returned value) final →
      Prefix host action world trace (.pure value) final := by
  induction action with
  | pure value =>
    intro world trace value' final hRun
    cases hRun
    exact .refl _ _
  | read capacity next ih =>
    intro world trace value final hRun
    cases hRun with
    | read_reject hCapacity hRun => exact (Prefix.read_reject hCapacity).trans (ih _ hRun)
    | read_return hCapacity hHost hRun =>
      exact (Prefix.read_return hCapacity hHost).trans (ih _ hRun)
  | write output bytes next ih =>
    intro world trace value final hRun
    cases hRun with
    | write_return hHost hRun => exact (Prefix.write_return hHost).trans (ih _ hRun)
  | exit code => intro world trace value final hRun; cases hRun
  | loop count state test step next hStep hNext =>
    intro world trace value final hRun
    cases hRun with
    | loop hRun =>
      exact Prefix.loop.trans (LoopExec.returned_prefix
        (fun _ _ _ _ _ _ h => hStep _ _ h) (fun _ _ _ _ _ h => hNext _ h) count.toNat hRun)

theorem Prefix.bind_after {World : Type} {host : Host World} {action : Action α}
    {next : α → Action β} {world after first value residual rest final}
    (hFirst : Exec host action world first (.returned value) after)
    (hRest : Prefix host (next value) after rest residual final) :
    Prefix host (Action.bind action next) world (first ++ rest) residual final :=
  ((Exec.returned_prefix action hFirst).bind).trans hRest

end LeanExe.Wasi
