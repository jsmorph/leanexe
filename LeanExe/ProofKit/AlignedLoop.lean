import LeanExe.ProofKit.AlignedExec

/-!
The rule for `loop` under `wpA`, the counterpart of Talos's `wp_loop_cons`: an invariant `Inv`
and a measure `μ` that each re-entry by `br 0` decreases.  As in Talos's rule, the re-entry is
the one place where the two sides run at different fuel, the inner `execOne` at `f` and the
outer `exec` at `f + 1`, and `execOne_fuel_mono` joins them.  The alignment of the loop at fuel
`f + 1` is the body's at `f` and, on a re-entry, the loop's at `f` from the next state, which the
induction hypothesis gives at every fuel from its bound on.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type} {m : Module} {Q : Assertion α} {env : HostEnv α}

theorem wpA_loop_cons {ps rs : Nat} {pt rt : List ValueType} {body rest : Program}
    (Inv : AssertionF α) (μ : Store α → Locals → Nat) {st : Store α} {s : Locals}
    (hInit : Inv st s)
    (hStep : ∀ st s, Inv st s →
        wpA m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              Inv st' { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
                μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } < μ st s
            | .Break (k + 1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wpA m (.loop ps rs body pt rt :: rest) Q st s env := by
  suffices key : ∀ n, ∀ st s, Inv st s → μ st s = n →
      wpA m (.loop ps rs body pt rt :: rest) Q st s env from key _ st s hInit rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro st s hInv hμ
  obtain ⟨Nb, hNb⟩ := hStep st s hInv
  have hunfold : ∀ f, execOne (f + 1) m st s (.loop ps rs body pt rt) env =
      (match exec f m st s body env with
       | .Fallthrough r' s' =>
         .Fallthrough r' { s' with values := s'.values.take rs ++ s.values.drop ps }
       | .Break 0 r' s' =>
         execOne f m r' { s' with values := s'.values.take ps ++ s.values.drop ps }
           (.loop ps rs body pt rt) env
       | .Break (k + 1) r' s' => .Break k r' s'
       | other => other) := fun f => execOne_loop_succ f m st s env ps rs body pt rt
  by_cases hOOF : ∀ f ≥ Nb, exec f m st s body env = .OutOfFuel
  · have hQ : Q .OutOfFuel := by
      have := (hNb Nb (Nat.le_refl _)).1
      rwa [hOOF Nb (Nat.le_refl _)] at this
    refine ⟨Nb + 1, fun F hF => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    have hb := hOOF f (by omega)
    have hs : execOne (f + 1) m st s (.loop ps rs body pt rt) env = .OutOfFuel := by
      rw [hunfold, hb]
    refine ⟨?_, ?_⟩
    · rw [exec, hs]; exact hQ
    · rw [AlignedExec, hs]
      refine ⟨?_, trivial⟩
      simp only [AlignedOne, hb]
      exact ⟨(hNb f (by omega)).2, trivial⟩
  · push Not at hOOF
    obtain ⟨f₀, hf₀, hne⟩ := hOOF
    have hstable : ∀ f ≥ f₀, exec f m st s body env = exec f₀ m st s body env :=
      fun f hf => exec_fuel_mono hf hne
    have hQb := (hNb f₀ hf₀).1
    have hOne : ∀ f ≥ f₀, AlignedExec f m st s body env := fun f hf => (hNb f (by omega)).2
    generalize hc : exec f₀ m st s body env = c at hstable hQb hne
    cases c with
    | Fallthrough st' s' =>
      obtain ⟨Nr, hNr⟩ := hQb
      refine ⟨f₀ + Nr + 1, fun F hF => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
      have hb := hstable f (by omega)
      have hs : execOne (f + 1) m st s (.loop ps rs body pt rt) env =
          .Fallthrough st' { s' with values := s'.values.take rs ++ s.values.drop ps } := by
        rw [hunfold, hb]
      have hr := hNr (f + 1) (by omega)
      refine ⟨?_, ?_⟩
      · rw [exec, hs]; exact hr.1
      · rw [AlignedExec, hs]
        refine ⟨?_, hr.2⟩
        simp only [AlignedOne, hb]
        exact ⟨hOne f (by omega), trivial⟩
    | Break n st' s' =>
      cases n with
      | zero =>
        obtain ⟨hInv', hlt⟩ := hQb
        have hIH := IH _ (by omega) st' _ hInv' rfl
        obtain ⟨Ni, hNi⟩ := hIH
        refine ⟨f₀ + Ni + 1, fun F hF => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
        have hb := hstable f (by omega)
        have hs : execOne (f + 1) m st s (.loop ps rs body pt rt) env =
            execOne f m st' { s' with values := s'.values.take ps ++ s.values.drop ps }
              (.loop ps rs body pt rt) env := by
          rw [hunfold, hb]
        have hi := hNi f (by omega)
        have hInner : AlignedOne f m st' { s' with values := s'.values.take ps ++ s.values.drop ps }
            (.loop ps rs body pt rt) env := by
          have h2 := hi.2
          rw [AlignedExec] at h2
          exact h2.1
        have hOneLoop : AlignedOne (f + 1) m st s (.loop ps rs body pt rt) env := by
          simp only [AlignedOne, hb]
          exact ⟨hOne f (by omega), hInner⟩
        by_cases hOf : execOne f m st' { s' with values := s'.values.take ps ++ s.values.drop ps }
            (.loop ps rs body pt rt) env = .OutOfFuel
        · have hs' := hs.trans hOf
          have hq := hi.1
          rw [exec, hOf] at hq
          refine ⟨?_, ?_⟩
          · rw [exec, hs']; exact hq
          · rw [AlignedExec, hs']; exact ⟨hOneLoop, trivial⟩
        · have hmono := execOne_fuel_mono (Nat.le_succ f) hOf
          have hi' := hNi (f + 1) (by omega)
          rw [exec, hmono] at hi'
          rw [AlignedExec, hmono] at hi'
          refine ⟨?_, ?_⟩
          · rw [exec, hs]; exact hi'.1
          · rw [AlignedExec, hs]; exact ⟨hOneLoop, hi'.2.2⟩
      | succ k =>
        refine ⟨f₀ + 1, fun F hF => ?_⟩
        obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
        have hb := hstable f (by omega)
        have hs : execOne (f + 1) m st s (.loop ps rs body pt rt) env = .Break k st' s' := by
          rw [hunfold, hb]
        refine ⟨?_, ?_⟩
        · rw [exec, hs]; exact hQb
        · rw [AlignedExec, hs]
          refine ⟨?_, trivial⟩
          simp only [AlignedOne, hb]
          exact ⟨hOne f (by omega), trivial⟩
    | OutOfFuel => exact absurd rfl hne
    | Return _ _ | Trap _ _ | Invalid _ | ReturnCall _ _ _ | Throwing _ _ _ _ =>
      refine ⟨f₀ + 1, fun F hF => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
      have hb := hstable f (by omega)
      have hs := hunfold f
      rw [hb] at hs
      refine ⟨?_, ?_⟩
      · rw [exec, hs]; exact hQb
      · rw [AlignedExec, hs]
        refine ⟨?_, trivial⟩
        simp only [AlignedOne, hb]
        exact ⟨hOne f (by omega), trivial⟩

end LeanExe.ProofKit
