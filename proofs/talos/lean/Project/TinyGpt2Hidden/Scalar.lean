import Project.TinyGpt2Hidden.RowLoad
import Project.ProofKit.CallRemainder

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2

theorem addRows_exact (env : HostEnv Unit) (initial : Store Unit) (x y : Row) :
    TerminatesWith env Project.TinyGpt2Hidden.module 4 initial
      (rowResults y ++ rowResults x)
      (fun final values => final = initial ∧ values = rowResults (addRows x y)) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func4 _ initial
    (func4Def.toLocals [.i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3,
      .i64 y.x0, .i64 y.x1, .i64 y.x2, .i64 y.x3]) env
  unfold func4
  wp_fixed_frame [func4Def]
  simp [rowResults, addRows, Wasm.f64Add]

theorem dot2_exact (env : HostEnv Unit) (initial : Store Unit) (x0 x1 w0 w1 : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 23 initial
      [.i64 w1, .i64 w0, .i64 x1, .i64 x0]
      (fun final values => final = initial ∧ values = [.i64 (Affine.dot2 x0 x1 w0 w1)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func23 _ initial
    (func23Def.toLocals [.i64 x0, .i64 x1, .i64 w0, .i64 w1]) env
  unfold func23
  wp_fixed_frame [func23Def]
  simp [Affine.dot2, Wasm.f64Mul, Wasm.f64Add]

theorem dot4_exact (env : HostEnv Unit) (initial : Store Unit)
    (x0 x1 x2 x3 w0 w1 w2 w3 : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 24 initial
      [.i64 w3, .i64 w2, .i64 w1, .i64 w0, .i64 x3, .i64 x2, .i64 x1, .i64 x0]
      (fun final values => final = initial ∧
        values = [.i64 (Affine.dot4 x0 x1 x2 x3 w0 w1 w2 w3)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func24 _ initial
    (func24Def.toLocals [.i64 x0, .i64 x1, .i64 x2, .i64 x3,
      .i64 w0, .i64 w1, .i64 w2, .i64 w3]) env
  unfold func24
  repeat first
    | wp_fixed_frame [func24Def]
    | (refine wp_call_tw (dot2_exact env initial _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
    | (refine wp_call_tw ((dot2_exact env initial _ _ _ _).append_args rfl rfl rfl _) ?_
       rintro st values ⟨out, rfl, hst, rfl⟩
       subst st)
  simp [Affine.dot4, Wasm.f64Add]

theorem dot8_exact (env : HostEnv Unit) (initial : Store Unit)
    (x0 x1 x2 x3 x4 x5 x6 x7 w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 68 initial
      [.i64 w7, .i64 w6, .i64 w5, .i64 w4, .i64 w3, .i64 w2, .i64 w1, .i64 w0,
        .i64 x7, .i64 x6, .i64 x5, .i64 x4, .i64 x3, .i64 x2, .i64 x1, .i64 x0]
      (fun final values => final = initial ∧
        values = [.i64 (Affine.dot8 x0 x1 x2 x3 x4 x5 x6 x7 w0 w1 w2 w3 w4 w5 w6 w7)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func68Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func68 _ initial
    (func68Def.toLocals [.i64 x0, .i64 x1, .i64 x2, .i64 x3, .i64 x4, .i64 x5, .i64 x6, .i64 x7,
      .i64 w0, .i64 w1, .i64 w2, .i64 w3, .i64 w4, .i64 w5, .i64 w6, .i64 w7]) env
  unfold func68
  repeat first
    | wp_fixed_frame [func68Def]
    | (refine wp_call_tw (dot4_exact env initial _ _ _ _ _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
    | (refine wp_call_tw ((dot4_exact env initial _ _ _ _ _ _ _ _).append_args rfl rfl rfl _) ?_
       rintro st values ⟨out, rfl, hst, rfl⟩
       subst st)
  simp [Affine.dot8, Wasm.f64Add]

theorem activate_exact (env : HostEnv Unit) (initial : Store Unit) (x : Row) :
    TerminatesWith env Project.TinyGpt2Hidden.module 65 initial (rowResults x)
      (fun final values => final = initial ∧ values = rowResults (activate x)) := by
  refine TerminatesWith.of_wp_entry_for (f := func65Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func65 _ initial
    (func65Def.toLocals [.i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3]) env
  unfold func65
  repeat first
    | wp_fixed_frame [func65Def]
    | (refine wp_call_tw (gelu_all_exact env initial _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
  simp [activate, rowResults]

theorem attentionScore_exact (env : HostEnv Unit) (initial : Store Unit) (q0 q1 k0 k1 : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 45 initial
      [.i64 k1, .i64 k0, .i64 q1, .i64 q0]
      (fun final values => final = initial ∧ values = [.i64 (attentionScore q0 q1 k0 k1)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func45Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func45 _ initial
    (func45Def.toLocals [.i64 q0, .i64 q1, .i64 k0, .i64 k1]) env
  unfold func45
  wp_fixed_frame [func45Def]
  refine wp_call_tw (dot2_exact env initial _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func45Def]
  simp [attentionScore, Wasm.f64Div]

#print axioms addRows_exact
#print axioms dot8_exact
#print axioms activate_exact
#print axioms attentionScore_exact
end Project.TinyGpt2Hidden.Spec
