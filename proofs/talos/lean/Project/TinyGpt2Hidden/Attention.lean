import Project.TinyGpt2Hidden.Scalar

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def contextResults (x : Context) : List Value :=
  rowResults x.r3 ++ rowResults x.r2 ++ rowResults x.r1 ++ rowResults x.r0

@[simp] theorem contextResults_length (x : Context) : (contextResults x).length = 16 := rfl

private theorem probabilityResults_length (p : Softmax.Result) :
    (Softmax.Spec.resultWords p).length = 5 := rfl

attribute [local simp] probabilityResults_length

theorem headProbabilities_exact (env : HostEnv Unit) (initial : Store Unit)
    (n q0 q1 : UInt64) (k0 k1 : Row) :
    TerminatesWith env Project.TinyGpt2Hidden.module 42 initial
      (rowResults k1 ++ rowResults k0 ++ [.i64 q1, .i64 q0, .i64 n])
      (fun final values => final = initial ∧
        values = Softmax.Spec.resultWords (headProbabilities n q0 q1 k0 k1)) := by
  refine TerminatesWith.of_wp_entry_for (f := func42Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func42 _ initial
    (func42Def.toLocals [.i64 n, .i64 q0, .i64 q1,
      .i64 k0.x0, .i64 k0.x1, .i64 k0.x2, .i64 k0.x3,
      .i64 k1.x0, .i64 k1.x1, .i64 k1.x2, .i64 k1.x3]) env
  unfold func42
  repeat first
    | wp_fixed_frame [func42Def, Softmax.Spec.resultWords]
    | (refine wp_call_tw (attentionScore_exact env initial _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
    | (refine wp_call_tw (softmax_exact env initial _ _ _ _ _) ?_
       rintro st values ⟨hst, rfl⟩
       subst st)
  simp [headProbabilities]

theorem weightedValue_exact (env : HostEnv Unit) (initial : Store Unit)
    (p : Softmax.Result) (v0 v1 v2 v3 : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 47 initial
      ([.i64 v3, .i64 v2, .i64 v1, .i64 v0] ++ Softmax.Spec.resultWords p)
      (fun final values => final = initial ∧ values = [.i64 (weightedValue p v0 v1 v2 v3)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func47Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func47 _ initial
    (func47Def.toLocals [.i64 p.status, .i64 p.p0, .i64 p.p1, .i64 p.p2, .i64 p.p3,
      .i64 v0, .i64 v1, .i64 v2, .i64 v3]) env
  unfold func47
  wp_fixed_frame [func47Def]
  refine wp_call_tw (dot4_exact env initial _ _ _ _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func47Def]
  simp [weightedValue]

theorem attentionRow_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : UInt64) (q : Row) (k v : Context) :
    TerminatesWith env Project.TinyGpt2Hidden.module 48 initial
      (contextResults v ++ contextResults k ++ rowResults q ++ [.i64 n])
      (fun final values => final = initial ∧ values = rowResults (attentionRow n q k v)) := by
  refine TerminatesWith.of_wp_entry_for (f := func48Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func48 _ initial
    (func48Def.toLocals ([.i64 n] ++ (rowResults q).reverse ++
      (contextResults k).reverse ++ (contextResults v).reverse)) env
  simp only [contextResults, rowResults, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append]
  unfold func48
  let p0 := headProbabilities n q.x0 q.x1
    ⟨k.r0.x0, k.r1.x0, k.r2.x0, k.r3.x0⟩ ⟨k.r0.x1, k.r1.x1, k.r2.x1, k.r3.x1⟩
  let p1 := headProbabilities n q.x2 q.x3
    ⟨k.r0.x2, k.r1.x2, k.r2.x2, k.r3.x2⟩ ⟨k.r0.x3, k.r1.x3, k.r2.x3, k.r3.x3⟩
  wp_fixed_frame [func48Def, contextResults, rowResults]
  refine wp_call_tw (headProbabilities_exact env initial n q.x0 q.x1
    ⟨k.r0.x0, k.r1.x0, k.r2.x0, k.r3.x0⟩ ⟨k.r0.x1, k.r1.x1, k.r2.x1, k.r3.x1⟩) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func48Def, Softmax.Spec.resultWords]
  refine wp_call_tw (headProbabilities_exact env initial n q.x2 q.x3
    ⟨k.r0.x2, k.r1.x2, k.r2.x2, k.r3.x2⟩ ⟨k.r0.x3, k.r1.x3, k.r2.x3, k.r3.x3⟩) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func48Def, Softmax.Spec.resultWords]
  refine wp_call_tw (weightedValue_exact env initial p0 _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func48Def]
  refine wp_call_tw (weightedValue_exact env initial p0 _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func48Def]
  refine wp_call_tw (weightedValue_exact env initial p1 _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func48Def]
  refine wp_call_tw (weightedValue_exact env initial p1 _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func48Def]
  simp [attentionRow, p0, p1]

#print axioms attentionRow_exact
end Project.TinyGpt2Hidden.Spec
