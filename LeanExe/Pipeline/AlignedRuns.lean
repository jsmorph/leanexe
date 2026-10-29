import LeanExe.Pipeline.Aborts
import LeanExe.ProofKit.AlignedExec

/-!
Function-level alignment.  `RunsA` is `Runs` together with `AlignedRun` at every fuel from some
bound on.  `RunsA.of_wpA_entry_for` derives it from the body's `wpA`, as `Runs.of_wp_entry_for`
derives `Runs` from the body's `wp`, and `wpA_call_runs` is the call rule, the counterpart of
`wp_call_runs`: the callee's `RunsA` gives the alignment of the call, which is the alignment of
the callee's run at one fuel less.
-/

namespace LeanExe.ProofKit

open Wasm

variable {α : Type} {env : HostEnv α} {m : Module} {id : Nat} {initial : Store α}
  {args : List Value} {P : Store α → List Value → Prop}

/-- `Runs` with aligned 64-bit accesses at every fuel from some bound on. -/
def RunsA (aborts : Bool) (env : HostEnv α) (m : Module) (id : Nat) (initial : Store α)
    (args : List Value) (P : Store α → List Value → Prop) : Prop :=
  Runs aborts env m id initial args P ∧ ∃ N, ∀ fuel ≥ N, AlignedRun fuel m id initial args env

/-- The entry rule: a body whose `wpA` reaches `P` or a trap that `TrapMsg aborts` accepts gives
`RunsA aborts`. -/
theorem RunsA.of_wpA_entry_for {aborts : Bool} {f : Function}
    (hf : m.funcs[id - m.imports.length]? = some f)
    (h : wpA m f.body
        (fun c => match c with
          | .Fallthrough st' s' =>
              P st' (s'.values.take f.results.length ++ args.drop f.numParams)
          | .Return st' vs =>
              P st' (vs.take f.results.length ++ args.drop f.numParams)
          | .Trap _ msg => TrapMsg aborts msg
          | _ => False)
        initial (f.toLocals (args.take f.numParams).reverse) env)
    (hImp : m.imports[id]? = none) :
    RunsA aborts env m id initial args P := by
  refine ⟨Runs.of_wp_entry_for hf h.wp hImp, ?_⟩
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun fuel hfuel => ?_⟩
  obtain ⟨hQ, hA⟩ := hN fuel hfuel
  rw [AlignedRun]
  simp only [hImp, hf]
  refine ⟨hA, ?_⟩
  cases hexec : exec fuel m initial (f.toLocals (args.take f.numParams).reverse) f.body env with
  | ReturnCall _ _ _ => rw [hexec] at hQ; exact hQ.elim
  | _ => trivial

theorem execOne_call_succ (f : Nat) (st : Store α) (s : Locals) (id : Nat) :
    execOne (f + 1) m st s (.call id) env =
      (match run f m id st s.values env with
       | .Success vs st' => .Fallthrough st' { s with values := vs }
       | .Trap st' msg => .Trap st' msg
       | .Invalid msg => .Invalid msg
       | .OutOfFuel => .OutOfFuel
       | .Thrown tag targs st' => .Throwing tag targs st' s) := by
  rw [execOne.eq_def]; rfl

/-- The call rule: a callee whose run is aligned and returns with `Post`, or ends as
`Trapped aborts` allows, gives the caller's `wpA` when its assertion accepts those traps. -/
theorem wpA_call_runs {aborts : Bool} {st : Store α} {s : Locals} {rest : Program}
    {Q : Assertion α} {Post : Store α → List Value → Prop}
    (hRun : RunsA aborts env m id st s.values Post) (hTrap : TrapOK aborts Q)
    (hPost : ∀ st' vs, Post st' vs → wpA m rest Q st' { s with values := vs } env) :
    wpA m (.call id :: rest) Q st s env := by
  obtain ⟨⟨N, hN⟩, Na, hNa⟩ := hRun
  rcases hN N (Nat.le_refl _) with ⟨vs, st', hR, hP⟩ | hTrapped
  · obtain ⟨Nr, hNr⟩ := hPost st' vs hP
    refine ⟨N + Na + Nr + 1, fun F hF => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    have hRf : run f m id st s.values env = .Success vs st' := by
      rw [run_fuel_mono (by omega : N ≤ f) (by rw [hR]; intro h; cases h)]
      exact hR
    have hs : execOne (f + 1) m st s (.call id) env = .Fallthrough st' { s with values := vs } := by
      rw [execOne_call_succ, hRf]
    have hr := hNr (f + 1) (by omega)
    refine ⟨?_, ?_⟩
    · rw [exec, hs]; exact hr.1
    · rw [AlignedExec, hs]
      refine ⟨?_, hr.2⟩
      simp only [AlignedOne]
      exact hNa f (by omega)
  · cases aborts
    · exact hTrapped.elim
    obtain ⟨st', hR⟩ := hTrapped
    refine ⟨N + Na + 1, fun F hF => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    have hRf : run f m id st s.values env = .Trap st' "unreachable" := by
      rw [run_fuel_mono (by omega : N ≤ f) (by rw [hR]; intro h; cases h)]
      exact hR
    have hs : execOne (f + 1) m st s (.call id) env = .Trap st' "unreachable" := by
      rw [execOne_call_succ, hRf]
    refine ⟨?_, ?_⟩
    · rw [exec, hs]; exact hTrap st'
    · rw [AlignedExec, hs]
      refine ⟨?_, trivial⟩
      simp only [AlignedOne]
      exact hNa f (by omega)

end LeanExe.ProofKit
