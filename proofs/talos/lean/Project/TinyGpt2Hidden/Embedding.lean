import Project.TinyGpt2Hidden.Column

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem embedding_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (token position : UInt64)
    (ha : UInt64Array.At initial pointer weights) (hb : 1039 < weights.size)
    (ht : token.toNat < 256) (hp : position.toNat < 4) :
    TerminatesWith env Project.TinyGpt2Hidden.module 8 initial
      [.i64 position, .i64 token, .i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = rowResults (embedding weights token position)) := by
  have hm (word : UInt64) : (4 : UInt64)*word = UInt64.ofNat (4*word.toNat) := by
    calc
      (4 : UInt64)*word = UInt64.ofNat 4 * UInt64.ofNat word.toNat := by simp
      _ = UInt64.ofNat (4*word.toNat) := (UInt64.ofNat_mul 4 word.toNat).symm
  have hpa : (1024 : UInt64)+UInt64.ofNat (4*position.toNat) =
      UInt64.ofNat (1024+4*position.toNat) := by
    exact (UInt64.ofNat_add 1024 (4*position.toNat)).symm
  have hgt : ¬UInt64.ofNat (4*token.toNat) < (0 : UInt64) := by simp
  have hgp : ¬UInt64.ofNat (1024+4*position.toNat) < (1024 : UInt64) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by
      change 1024+4*position.toNat < 18446744073709551616
      omega)]
    change ¬1024+4*position.toNat < 1024
    omega
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func8 _ initial
    (func8Def.toLocals [.i64 owner, .i64 pointer, .i64 token, .i64 position]) env
  unfold func8
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 token [] rfl rfl rfl ?_ _ _ ?_
  · change 4*token.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, UInt64.zero_add]
  wp_column_add hgt
  wp_fixed_frame [func8Def]
  refine wp_call_tw (loadRow_exact env initial owner pointer weights (4*token.toNat) ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 position _ rfl rfl rfl ?_ _ _ ?_
  · change 4*position.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, hpa]
  wp_column_add hgp
  wp_fixed_frame [func8Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights
    (1024+4*position.toNat) ha (by omega)).append_args rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 token [] rfl rfl rfl ?_ _ _ ?_
  · change 4*token.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, UInt64.zero_add]
  wp_column_add hgt
  wp_fixed_frame [func8Def]
  refine wp_call_tw (loadRow_exact env initial owner pointer weights (4*token.toNat) ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 position _ rfl rfl rfl ?_ _ _ ?_
  · change 4*position.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, hpa]
  wp_column_add hgp
  wp_fixed_frame [func8Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights
    (1024+4*position.toNat) ha (by omega)).append_args rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 token [] rfl rfl rfl ?_ _ _ ?_
  · change 4*token.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, UInt64.zero_add]
  wp_column_add hgt
  wp_fixed_frame [func8Def]
  refine wp_call_tw (loadRow_exact env initial owner pointer weights (4*token.toNat) ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 position _ rfl rfl rfl ?_ _ _ ?_
  · change 4*position.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, hpa]
  wp_column_add hgp
  wp_fixed_frame [func8Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights
    (1024+4*position.toNat) ha (by omega)).append_args rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 token [] rfl rfl rfl ?_ _ _ ?_
  · change 4*token.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, UInt64.zero_add]
  wp_column_add hgt
  wp_fixed_frame [func8Def]
  refine wp_call_tw (loadRow_exact env initial owner pointer weights (4*token.toNat) ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.guardProgram 67 68 ++ _) _ initial _ env
  refine CheckedNatMul.guard_spec 67 68 _ _ _ _ 4 position _ rfl rfl rfl ?_ _ _ ?_
  · change 4*position.toNat < 18446744073709551616
    omega
  wp_fixed_frame [func8Def, hm, hpa]
  wp_column_add hgp
  wp_fixed_frame [func8Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights
    (1024+4*position.toNat) ha (by omega)).append_args rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func8Def, rowResults]
  simp [embedding, addRows, rowResults, Layout.token, Layout.position, Wasm.f64Add]

#print axioms embedding_exact
end Project.TinyGpt2Hidden.Spec

