import Project.ExpWide.Program
import Project.ExpWide.Model
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

namespace Project.ExpWide.Spec
open Wasm

private theorem domain_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpWide.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if inDomain x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.ExpWide.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  by_cases hz : x = 0
  all_goals by_cases hl : (0x8000000000000000 : UInt64) ≤ x
  all_goals by_cases hu : x ≤ (0xC020000000000000 : UInt64)
  all_goals
    repeat
      first
      | wp_run [func0Def, reduceIte, *]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [inDomain, hz, hl, hu]

theorem polynomial_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpWide.module 1 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpSmall.polynomial x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.ExpWide.module func1 _ initial (func1Def.toLocals [.i64 x]) env
  unfold func1
  wp_run [func1Def]
  simp [ExpSmall.polynomial, Wasm.f64Mul, Wasm.f64Add]

theorem evaluate_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpWide.module 2 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (evaluate x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.ExpWide.module func2 _ initial (func2Def.toLocals [.i64 x]) env
  unfold func2
  wp_run [func2Def]
  refine wp_call_tw (polynomial_exact env initial _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_run [func2Def]
  simp [evaluate, Wasm.f64Mul, Wasm.f64Div]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    TerminatesWith env m 3 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (expWide x).bits, .i64 (expWide x).status])

theorem expWide_exact : ExactSpecFor Project.ExpWide.module := by
  intro env initial x
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.ExpWide.module func3 _ initial (func3Def.toLocals [.i64 x]) env
  unfold func3
  wp_run [func3Def]
  refine wp_call_tw (domain_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hd : inDomain x
  all_goals
    repeat
      first
      | wp_run [func3Def, hd, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [hd])
  · simp [expWide, hd]
  · refine wp_call_tw (evaluate_exact env initial x) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    wp_run
    simp [expWide, hd, func3Def]

#print axioms domain_exact
#print axioms polynomial_exact
#print axioms expWide_exact
end Project.ExpWide.Spec
