import Project.TinyGpt2Infer.Region
import Project.TinyGpt2Hidden.Column
import Project.ProofKit.ConstantFunction
import Project.ProofKit.ExactCall

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.ProofKit Project.TinyGpt2Hidden.Spec

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem logit_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (x : Row) (token : UInt64)
    (ha : UInt64Array.At initial pointer weights) (hb : 2488 ≤ weights.size)
    (ht : token.toNat < 256) :
    TerminatesWith env Project.TinyGpt2Infer.module 74 initial
      (.i64 token :: rowResults x ++ [.i64 pointer, .i64 owner])
      (fun final values => final = initial ∧ values = [.i64 (logit weights x token)]) := by
  have hadd : (2208 : UInt64) + token = UInt64.ofNat (2208 + token.toNat) := by
    rw [UInt64.ofNat_add]
    simp
  have hguard : ¬UInt64.ofNat (2208 + token.toNat) < (2208 : UInt64) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by
      change 2208 + token.toNat < 18446744073709551616
      omega)]
    change ¬2208 + token.toNat < 2208
    omega
  refine TerminatesWith.of_wp_entry_for (f := func74Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Infer.module func74 _ initial
    (func74Def.toLocals [.i64 owner, .i64 pointer, .i64 x.x0,
      .i64 x.x1, .i64 x.x2, .i64 x.x3, .i64 token]) env
  unfold func74
  wp_fixed_frame [func74Def]
  refine wp_call_exact_append
    (ConstantFunction.exact Project.TinyGpt2Infer.module env initial 72 1184 (some 72) rfl rfl)
    rfl rfl rfl [] rfl ?_
  wp_fixed_frame [func74Def]
  refine wp_call_exact_append
    (component_exact 25 (by decide)
      (dotColumn4_exact env initial owner pointer weights 1184 256 token.toNat x ha (by omega)))
    rfl rfl rfl [] (by simp [rowResults]) ?_
  wp_fixed_frame [func74Def, hadd]
  wp_column_add hguard
  change wp Project.TinyGpt2Infer.module (CheckedArrayGet.checkedGetCore 18 19 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 18 19 _ _ _ _ pointer weights
    (2208 + token.toNat) _ rfl rfl rfl ha (by omega) _ _ ?_
  wp_fixed_frame [func74Def]
  simp [logit, Layout.head, Layout.headBias, getElem!_pos, show 2208 + token.toNat < weights.size by omega,
    Wasm.f64Add]

#print axioms logit_exact
end Project.TinyGpt2Infer.Spec
