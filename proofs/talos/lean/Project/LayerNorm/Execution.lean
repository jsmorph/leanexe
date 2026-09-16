import Project.LayerNorm.ExecutionBase

namespace Project.LayerNorm.Spec
open Wasm

set_option maxHeartbeats 2000000

def arguments (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) : List Value :=
  [.i64 b3, .i64 b2, .i64 b1, .i64 b0, .i64 g3, .i64 g2, .i64 g1, .i64 g0,
    .i64 x3, .i64 x2, .i64 x1, .i64 x0]

theorem compute_exact (env : HostEnv Unit) (initial : Store Unit)
    (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64) :
    TerminatesWith env Project.LayerNorm.module 5 initial
      (arguments x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)
      (fun final values => final = initial ∧
        values = resultWords (compute x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)) := by
  unfold arguments
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func5 _ initial
    (func5Def.toLocals [.i64 x0, .i64 x1, .i64 x2, .i64 x3, .i64 g0, .i64 g1,
      .i64 g2, .i64 g3, .i64 b0, .i64 b1, .i64 b2, .i64 b3]) env
  unfold func5
  repeat
    first
    | wp_fixed_frame [func5Def]
    | (refine wp_call_tw (average_exact env initial _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
    | (refine wp_call_tw (denominator_exact env initial _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
    | (refine wp_call_tw (affine_exact env initial _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
  all_goals simp [compute, resultWords, Wasm.f64Sub]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64),
    TerminatesWith env m 6 initial (arguments x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)
      (fun final values => final = initial ∧
        values = resultWords (layerNorm x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3))

theorem layerNorm_exact : ExactSpecFor Project.LayerNorm.module := by
  intro env initial x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3
  unfold arguments
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp Project.LayerNorm.module func6 _ initial
    (func6Def.toLocals [.i64 x0, .i64 x1, .i64 x2, .i64 x3, .i64 g0, .i64 g1,
      .i64 g2, .i64 g3, .i64 b0, .i64 b1, .i64 b2, .i64 b3]) env
  unfold func6
  cases hx : rowBounded x0 x1 x2 x3
  all_goals cases hg : rowBounded g0 g1 g2 g3
  all_goals cases hb : rowBounded b0 b1 b2 b3
  all_goals
    repeat
      first
      | wp_fixed_frame [func6Def, reduceIte, *]
      | (refine wp_call_tw (rowBounded_exact env initial _ _ _ _) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (refine wp_call_tw (compute_exact env initial _ _ _ _ _ _ _ _ _ _ _ _) ?_
         rintro st values ⟨hst, rfl⟩
         subst st)
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [layerNorm, resultWords, *]

#print axioms layerNorm_exact
end Project.LayerNorm.Spec
