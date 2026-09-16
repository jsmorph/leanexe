import Project.TinyGpt2Hidden.Column
import Project.TinyGpt2Hidden.Attention

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem project4_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (offset : Nat) (x : Row)
    (ha : UInt64Array.At initial pointer weights) (hb : offset+15 < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 26 initial
      (rowResults x ++ [.i64 (UInt64.ofNat offset), .i64 pointer, .i64 owner])
      (fun final values => final = initial ∧ values = rowResults (project4 weights offset x)) := by
  refine TerminatesWith.of_wp_entry_for (f := func26Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func26 _ initial
    (func26Def.toLocals [.i64 owner, .i64 pointer, .i64 (UInt64.ofNat offset),
      .i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3]) env
  unfold func26
  wp_fixed_frame [func26Def]
  refine wp_call_tw (dotColumn4_exact env initial owner pointer weights offset 4 0 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func26Def]
  refine wp_call_tw (dotColumn4_exact env initial owner pointer weights offset 4 1 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func26Def]
  refine wp_call_tw (dotColumn4_exact env initial owner pointer weights offset 4 2 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func26Def]
  refine wp_call_tw (dotColumn4_exact env initial owner pointer weights offset 4 3 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func26Def]
  simp [project4, rowResults]

theorem projectContext_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (offset : Nat) (x : Context)
    (ha : UInt64Array.At initial pointer weights) (hb : offset+15 < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 29 initial
      (contextResults x ++ [.i64 (UInt64.ofNat offset), .i64 pointer, .i64 owner])
      (fun final values => final = initial ∧
        values = contextResults (projectContext weights offset x)) := by
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func29 _ initial
    (func29Def.toLocals ([.i64 owner, .i64 pointer, .i64 (UInt64.ofNat offset)] ++
      (contextResults x).reverse)) env
  simp only [contextResults, rowResults, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append]
  unfold func29
  wp_fixed_frame [func29Def, rowResults]
  refine wp_call_tw (project4_exact env initial owner pointer weights offset x.r0 ha hb) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func29Def, rowResults]
  refine wp_call_tw (project4_exact env initial owner pointer weights offset x.r1 ha hb) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func29Def, rowResults]
  refine wp_call_tw (project4_exact env initial owner pointer weights offset x.r2 ha hb) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func29Def, rowResults]
  refine wp_call_tw (project4_exact env initial owner pointer weights offset x.r3 ha hb) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func29Def, rowResults]
  simp [projectContext]

theorem contextRow_exact (env : HostEnv Unit) (initial : Store Unit)
    (x : Context) (position : UInt64) :
    TerminatesWith env Project.TinyGpt2Hidden.module 28 initial
      (.i64 position :: contextResults x)
      (fun final values => final = initial ∧ values = rowResults (contextRow x position)) := by
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func28 _ initial
    (func28Def.toLocals ((contextResults x).reverse ++ [.i64 position])) env
  simp only [contextResults, rowResults, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append]
  unfold func28
  by_cases h0 : position = 0
  all_goals by_cases h1 : position = 1
  all_goals by_cases h2 : position = 2
  all_goals
    repeat first
      | wp_fixed_frame [func28Def, *]
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp [*])
  all_goals simp [contextRow, *]

#print axioms project4_exact
#print axioms projectContext_exact
#print axioms contextRow_exact
end Project.TinyGpt2Hidden.Spec

