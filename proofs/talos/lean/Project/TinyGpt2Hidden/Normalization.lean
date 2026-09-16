import Project.TinyGpt2Hidden.Scalar

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

theorem norm_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (offset : Nat) (x : Row)
    (ha : UInt64Array.At initial pointer weights) (hb : offset+7 < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 17 initial
      (rowResults x ++ [.i64 (UInt64.ofNat offset), .i64 pointer, .i64 owner])
      (fun final values => final = initial ∧ values = rowResults (norm weights offset x)) := by
  refine TerminatesWith.of_wp_entry_for (f := func17Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func17 _ initial
    (func17Def.toLocals [.i64 owner, .i64 pointer, .i64 (UInt64.ofNat offset),
      .i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3]) env
  unfold func17
  wp_fixed_frame [func17Def]
  refine wp_call_tw (loadRow_exact env initial owner pointer weights offset ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func17Def, rowResults]
  try simp only [Wasm.wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have hs : ¬UInt64.ofNat offset+4 < UInt64.ofNat offset := by
    change ¬UInt64.ofNat offset+UInt64.ofNat 4 < UInt64.ofNat offset
    rw [← UInt64.ofNat_add, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' (by have hh := ha.size_lt; omega),
      UInt64.toNat_ofNat_of_lt' (by have hh := ha.size_lt; omega)]
    omega
  simp only [hs, reduceIte, ne_eq, not_true_eq_false]
  wp_fixed_frame [func17Def, rowResults]
  have hadd : UInt64.ofNat offset+4 = UInt64.ofNat (offset+4) := by
    change UInt64.ofNat offset+UInt64.ofNat 4 = UInt64.ofNat (offset+4)
    rw [UInt64.ofNat_add]
  rw [hadd]
  refine wp_call_tw (loadRow_exact env initial owner pointer weights (offset+4) ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func17Def, rowResults]
  refine wp_call_tw (normalization_exact env initial _ _ _ _ _ _ _ _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func17Def, LayerNorm.Spec.resultWords]
  simp [rowResults, Project.TinyGpt2.norm]

#print axioms norm_exact
end Project.TinyGpt2Hidden.Spec
