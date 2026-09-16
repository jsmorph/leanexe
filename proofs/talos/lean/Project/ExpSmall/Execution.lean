import Project.ExpSmall.Program
import Project.ExpSmall.Model
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

namespace Project.ExpSmall.Spec
open Wasm

private theorem domain_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpSmall.module 0 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (if inDomain x then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.ExpSmall.module func0 _ initial (func0Def.toLocals [.i64 x]) env
  unfold func0
  by_cases hz : x = 0
  all_goals by_cases hl : (0x8000000000000000 : UInt64) ≤ x
  all_goals by_cases hu : x ≤ (0xBFF0000000000000 : UInt64)
  all_goals
    repeat
      first
      | wp_run [func0Def, reduceIte, *]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [inDomain, hz, hl, hu]

theorem polynomial_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env Project.ExpSmall.module 1 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (polynomial x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp Project.ExpSmall.module func1 _ initial (func1Def.toLocals [.i64 x]) env
  unfold func1
  wp_run [func1Def]
  simp [polynomial, Wasm.f64Mul, Wasm.f64Add]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    TerminatesWith env m 2 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (expSmall x).bits, .i64 (expSmall x).status])

theorem expSmall_exact : ExactSpecFor Project.ExpSmall.module := by
  intro env initial x
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.ExpSmall.module func2 _ initial (func2Def.toLocals [.i64 x]) env
  unfold func2
  wp_run [func2Def]
  refine wp_call_tw (domain_exact env initial x) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hd : inDomain x
  all_goals
    repeat
      first
      | wp_run [func2Def, hd, reduceIte]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [hd])
  · simp [expSmall, hd]
  · refine wp_call_tw (polynomial_exact env initial x) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    wp_run
    simp [expSmall, hd, func2Def]

#print axioms domain_exact
#print axioms polynomial_exact
#print axioms expSmall_exact
end Project.ExpSmall.Spec
