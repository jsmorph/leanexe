import Project.Softmax.ExecutionBase

namespace Project.Softmax.Spec
open Wasm

set_option maxHeartbeats 2000000

theorem rowMaximum_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.Softmax.module 4 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = [.i64 (rowMaximum n a b c d)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func4 _ initial (func4Def.toLocals [.i64 n, .i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func4
  wp_fixed_frame [func4Def]
  refine wp_call_tw (activeScore_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  refine wp_call_tw (maximum_exact env initial _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  refine wp_call_tw (activeScore_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  refine wp_call_tw (activeScore_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  refine wp_call_tw (maximum_exact env initial _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  refine wp_call_tw (maximum_exact env initial _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func4Def]
  simp [rowMaximum]

theorem compute_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.Softmax.module 10 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = resultWords (compute n a b c d)) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func10 _ initial (func10Def.toLocals [.i64 n, .i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func10
  wp_fixed_frame [func10Def]
  refine wp_call_tw (rowMaximum_exact env initial _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (weight_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (total_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  refine wp_call_tw (probability_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func10Def]
  simp [resultWords, compute]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64),
    TerminatesWith env m 11 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = resultWords (softmax n a b c d))

theorem softmax_exact (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64) :
    TerminatesWith env Project.Softmax.module 11 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = resultWords (softmax n a b c d)) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_ (by decide)
  change wp Project.Softmax.module func11 _ initial (func11Def.toLocals [.i64 n, .i64 a, .i64 b, .i64 c, .i64 d]) env
  unfold func11
  wp_fixed_frame [func11Def]
  refine wp_call_tw (domain_exact env initial _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hd : inDomain n a b c d
  all_goals
    repeat
      first
      | wp_fixed_frame [func11Def, reduceIte, *]
      | (refine wp_call_tw (compute_exact env initial _ _ _ _ _) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [softmax, hd, resultWords]


#print axioms softmax_exact
end Project.Softmax.Spec
