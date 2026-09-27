import Project.EulerConservative.Helpers

namespace Project.EulerConservative.Execution
open Wasm
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Consume determined scalar code and guards, stopping at the next helper call. -/
macro "side_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [boolWord, *]
    | refine wp_iff_cons rfl ?_
      simp [boolWord, *])

theorem stateGuard_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum energy : UInt64) :
    TerminatesWith env m 3 initial [.i64 energy, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Model.stateGuard rho momentum energy))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def)
    (by simpa [layout.noImports] using layout.state) ?_ (by simp [layout.noImports])
  change wp m func3 _ initial
    { params := [.i64 rho, .i64 momentum, .i64 energy],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0], values := [] } env
  unfold func3
  wp_run
  refine wp_call_tw (positiveBits_exact layout env initial rho) ?_
  rintro st0 values0 ⟨hst0, rfl⟩
  subst st0
  cases hr : Model.positiveBits rho
  · side_peel
    simp [Model.stateGuard, hr, func3Def]
  · side_peel
    refine wp_call_tw (finiteBits_exact layout env initial momentum) ?_
    rintro st1 values1 ⟨hst1, rfl⟩
    subst st1
    cases hm : Model.finiteBits momentum
    · side_peel
      simp [Model.stateGuard, hr, hm, func3Def]
    · side_peel
      refine wp_call_tw (positiveBits_exact layout env initial energy) ?_
      rintro st2 values2 ⟨hst2, rfl⟩
      subst st2
      cases he : Model.positiveBits energy
      · side_peel
        simp [Model.stateGuard, hr, hm, he, func3Def]
      · side_peel
        refine wp_call_tw (absBits_exact layout env initial momentum) ?_
        rintro st3 values3 ⟨hst3, rfl⟩
        subst st3
        by_cases hmr : Model.absBits momentum ≤ rho <;> by_cases hre : rho ≤ energy
        all_goals
          side_peel
          simp [Model.stateGuard, hr, hm, he, hmr, hre, func3Def]

#print axioms stateGuard_exact
end Project.EulerConservative.Execution
