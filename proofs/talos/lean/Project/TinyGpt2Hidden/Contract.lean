import Project.TinyGpt2Hidden.WideColumn
import Project.ProofKit.ConstantFunction

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem contractRow_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (x : WideRow)
    (ha : UInt64Array.At initial pointer weights) (hb : 1183 < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 72 initial
      (wideResults x ++ [.i64 pointer, .i64 owner])
      (fun final values => final = initial ∧ values = rowResults (contractRow weights x)) := by
  refine TerminatesWith.of_wp_entry_for (f := func72Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func72 _ initial
    (func72Def.toLocals [.i64 owner, .i64 pointer,
      .i64 x.low.x0, .i64 x.low.x1, .i64 x.low.x2, .i64 x.low.x3,
      .i64 x.high.x0, .i64 x.high.x1, .i64 x.high.x2, .i64 x.high.x3]) env
  unfold func72
  wp_fixed_frame [func72Def, rowResults]
  refine wp_call_tw (ConstantFunction.exact _ env initial 70 1148 (some 70) rfl rfl) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw (dotColumn8_exact env initial owner pointer weights 1148 4 0 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((ConstantFunction.exact _ env initial 71 1180 (some 71) rfl rfl).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights 1180 ha (by omega)).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def, rowResults]
  refine wp_call_tw (ConstantFunction.exact _ env initial 70 1148 (some 70) rfl rfl) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw (dotColumn8_exact env initial owner pointer weights 1148 4 1 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((ConstantFunction.exact _ env initial 71 1180 (some 71) rfl rfl).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights 1180 ha (by omega)).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def, rowResults]
  refine wp_call_tw (ConstantFunction.exact _ env initial 70 1148 (some 70) rfl rfl) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw (dotColumn8_exact env initial owner pointer weights 1148 4 2 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((ConstantFunction.exact _ env initial 71 1180 (some 71) rfl rfl).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights 1180 ha (by omega)).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def, rowResults]
  refine wp_call_tw (ConstantFunction.exact _ env initial 70 1148 (some 70) rfl rfl) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw (dotColumn8_exact env initial owner pointer weights 1148 4 3 x ha (by omega)) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((ConstantFunction.exact _ env initial 71 1180 (some 71) rfl rfl).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def]
  refine wp_call_tw ((loadRow_exact env initial owner pointer weights 1180 ha (by omega)).append_args
    rfl rfl rfl _) ?_
  rintro st values ⟨out, rfl, hst, rfl⟩
  subst st
  wp_fixed_frame [func72Def, rowResults]
  simp [contractRow, rowResults, addRows, Layout.contract, Layout.contractBias, Wasm.f64Add]

#print axioms contractRow_exact
end Project.TinyGpt2Hidden.Spec
