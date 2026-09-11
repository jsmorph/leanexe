import Project.Euler2DConservative.Helpers
import Project.EulerConservative.Execution
import Project.ProofKit.CallRemainder

namespace Project.Euler2DConservative.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

macro "guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [boolWord, List.set, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.getElem?_nil, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | (try simp only [Wasm.wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp [boolWord, *]))

macro "guard_call" call:term : tactic => `(tactic|
  (refine wp_call_tw $call ?_
   rintro st values ⟨hst, hvalues⟩
   subst st
   subst values
   guard_peel))

macro "guard_tail_call" call:term : tactic => `(tactic|
  (refine wp_call_tw $call ?_
   rintro st values ⟨out, hvalues, hst, hout⟩
   subst st
   subst out
   subst values
   guard_peel))

theorem maxWord_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64) :
    TerminatesWith env m 4 initial [.i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (Model.maxWord a b)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def)
    (by simpa [layout.noImports] using layout.maxWord) ?_ (by simp [layout.noImports])
  change wp m func4 _ initial (func4Def.toLocals [.i64 a, .i64 b]) env
  unfold func4
  by_cases hab : a < b <;> guard_peel <;> simp [Model.maxWord, hab, func4Def]

theorem exponentBits_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (bits : UInt64) :
    TerminatesWith env m 5 initial [.i64 bits]
      (fun final values => final = initial ∧ values = [.i64 (Model.exponentBits bits)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def)
    (by simpa [layout.noImports] using layout.exponent) ?_ (by simp [layout.noImports])
  change wp m func5 _ initial (func5Def.toLocals [.i64 bits]) env
  unfold func5
  wp_run [func5Def]
  guard_call (absBits_exact layout env initial bits)
  simp [Model.exponentBits, func5Def]

theorem topExponent_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env m 6 initial [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = [.i64 (Model.topExponent rho mx my energy)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def)
    (by simpa [layout.noImports] using layout.topExponent) ?_ (by simp [layout.noImports])
  change wp m func6 _ initial (func6Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func6
  wp_run [func6Def]
  guard_call (exponentBits_exact layout env initial rho)
  guard_call (exponentBits_exact layout env initial mx)
  guard_call (maxWord_exact layout env initial (Model.exponentBits rho) (Model.exponentBits mx))
  guard_call (exponentBits_exact layout env initial my)
  guard_call (exponentBits_exact layout env initial energy)
  guard_call (maxWord_exact layout env initial (Model.exponentBits my) (Model.exponentBits energy))
  guard_call (maxWord_exact layout env initial
    (Model.maxWord (Model.exponentBits rho) (Model.exponentBits mx))
    (Model.maxWord (Model.exponentBits my) (Model.exponentBits energy)))
  simp [Model.topExponent, func6Def]

theorem normalizable_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (bits top : UInt64) :
    TerminatesWith env m 7 initial [.i64 top, .i64 bits]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Model.normalizable bits top))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def)
    (by simpa [layout.noImports] using layout.normalizable) ?_ (by simp [layout.noImports])
  change wp m func7 _ initial (func7Def.toLocals [.i64 bits, .i64 top]) env
  unfold func7
  wp_run [func7Def]
  guard_call (absBits_exact layout env initial bits)
  by_cases hz : Model.absBits bits = 0
  · guard_peel
    simp [Model.normalizable, hz, func7Def]
  · guard_peel
    guard_tail_call ((exponentBits_exact layout env initial bits).append_args
      (by simp [layout.noImports])
      (by simpa [layout.noImports] using layout.exponent) rfl [.i64 0])
    by_cases he : (0 : UInt64) < Model.exponentBits bits
    · have he0 : Model.exponentBits bits ≠ 0 := by
        intro hzero
        simpa [hzero] using he
      guard_peel
      guard_tail_call ((exponentBits_exact layout env initial bits).append_args
        (by simp [layout.noImports])
        (by simpa [layout.noImports] using layout.exponent) rfl [.i64 top])
      by_cases ht : top < Model.exponentBits bits + 1021 <;> guard_peel <;>
        simp [Model.normalizable, hz, he, ht, func7Def]
    · have he0 : Model.exponentBits bits = 0 := by
        apply UInt64.toNat_inj.mp
        have hn : ¬0 < (Model.exponentBits bits).toNat := he
        change (Model.exponentBits bits).toNat = 0
        omega
      guard_peel
      simp [Model.normalizable, hz, he, func7Def]

theorem energyResidual_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env m 8 initial [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = [.i64 (Model.energyResidual rho mx my energy)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def)
    (by simpa [layout.noImports] using layout.residual) ?_ (by simp [layout.noImports])
  change wp m func8 _ initial (func8Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func8
  side_fp_peel
  simp [Model.energyResidual, func8Def]

theorem normalizedMagnitude_exact {m : Wasm.Module} (layout : HelperLayout m)
    (env : HostEnv Unit) (initial : Store Unit) (bits top : UInt64) :
    TerminatesWith env m 9 initial [.i64 top, .i64 bits]
      (fun final values => final = initial ∧ values = [.i64 (Model.normalizedMagnitude bits top)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def)
    (by simpa [layout.noImports] using layout.normalized) ?_ (by simp [layout.noImports])
  change wp m func9 _ initial (func9Def.toLocals [.i64 bits, .i64 top]) env
  unfold func9
  wp_run [func9Def]
  guard_call (absBits_exact layout env initial bits)
  by_cases hz : Model.absBits bits = 0
  · guard_peel
    simp [Model.normalizedMagnitude, hz, func9Def]
  · guard_peel
    guard_call (exponentBits_exact layout env initial bits)
    guard_tail_call ((absBits_exact layout env initial bits).append_args
      (by simp [layout.noImports])
      (by simpa [layout.noImports] using layout.abs) rfl
      [.i64 ((Model.exponentBits bits + 1021 - top) * 4503599627370496)])
    simp [Model.normalizedMagnitude, hz, func9Def]

#print axioms maxWord_exact
#print axioms exponentBits_exact
#print axioms topExponent_exact
#print axioms normalizable_exact
#print axioms energyResidual_exact
#print axioms normalizedMagnitude_exact
end Project.Euler2DConservative.Execution
