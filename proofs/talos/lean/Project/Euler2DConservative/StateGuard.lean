import Project.Euler2DConservative.EnergyGuard
import Project.EulerConservative.StateGuard

namespace Project.Euler2DConservative.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem narrowStateGuard_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64) :
    TerminatesWith env m 3 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Model.narrowStateGuard rho momentum transverse energy))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def)
    (by simpa [layout.noImports] using layout.narrowState) ?_ (by simp [layout.noImports])
  change wp m func3 _ initial (func3Def.toLocals [.i64 rho, .i64 momentum, .i64 transverse, .i64 energy]) env
  unfold func3
  wp_run [func3Def]
  refine wp_call_tw (positiveBits_exact layout env initial rho) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hr : Model.positiveBits rho
  · side_peel
    simp [Model.narrowStateGuard, hr, func3Def]
  · side_peel
    refine wp_call_tw (finiteBits_exact layout env initial momentum) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases hm : Model.finiteBits momentum
    · side_peel
      simp [Model.narrowStateGuard, hr, hm, func3Def]
    · side_peel
      refine wp_call_tw (finiteBits_exact layout env initial transverse) ?_
      rintro st values ⟨hst, rfl⟩
      subst st
      cases ht : Model.finiteBits transverse
      · side_peel
        simp [Model.narrowStateGuard, hr, hm, ht, func3Def]
      · side_peel
        refine wp_call_tw (positiveBits_exact layout env initial energy) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        cases he : Model.positiveBits energy
        · side_peel
          simp [Model.narrowStateGuard, hr, hm, ht, he, func3Def]
        · side_peel
          refine wp_call_tw (absBits_exact layout env initial momentum) ?_
          rintro st values ⟨hst, rfl⟩
          subst st
          by_cases hmr : Model.absBits momentum ≤ rho
          · side_peel
            refine wp_call_tw (absBits_exact layout env initial transverse) ?_
            rintro st values ⟨hst, rfl⟩
            subst st
            by_cases htr : Model.absBits transverse ≤ rho <;> by_cases hre : rho < energy
            all_goals
              side_peel
              simp [Model.narrowStateGuard, hr, hm, ht, he, hmr, htr, hre, func3Def]
          · side_peel
            simp [Model.narrowStateGuard, hr, hm, ht, he, hmr, func3Def]

theorem stateGuard_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64) :
    TerminatesWith env m 11 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Model.stateGuard rho momentum transverse energy))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def)
    (by simpa [layout.noImports] using layout.state) ?_ (by simp [layout.noImports])
  change wp m func11 _ initial (func11Def.toLocals [.i64 rho, .i64 momentum, .i64 transverse, .i64 energy]) env
  unfold func11
  wp_run [func11Def]
  refine wp_call_tw (narrowStateGuard_exact layout env initial rho momentum transverse energy) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hn : Model.narrowStateGuard rho momentum transverse energy
  · guard_peel
    refine wp_call_tw (energyGuard_exact layout env initial rho momentum transverse energy) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases he : Model.energyGuard rho momentum transverse energy <;> guard_peel <;>
      simp [Model.stateGuard, hn, he, func11Def]
  · guard_peel
    simp [Model.stateGuard, hn, func11Def]

#print axioms narrowStateGuard_exact
#print axioms stateGuard_exact
end Project.Euler2DConservative.Execution
