import Project.TinyGpt2Hidden.Scalar
import Project.ProofKit.CheckedNatMul

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

macro "wp_column_add" h:Lean.Parser.Tactic.simpLemma : tactic => `(tactic|
  (try simp only [wp_iff_control_types]
   refine wp_iff_cons rfl ?_
   simp (discharger := omega) only [← UInt64.ofNat_add, $h, reduceIte,
     ne_eq, not_true_eq_false]
   rw [wp_localGet_cons]
   simp only [Locals.get, Locals.set?, List.length, List.getElem?_cons,
     List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.succ_ne_zero, reduceIte,
     wp_localSet_cons, wp_nil, List.take, List.drop, List.append_nil]))

theorem dotColumn4_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (offset width column : Nat) (x : Row)
    (ha : UInt64Array.At initial pointer weights)
    (hb : offset+3*width+column < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 25 initial
      (rowResults x ++ [.i64 (UInt64.ofNat column), .i64 (UInt64.ofNat width),
        .i64 (UInt64.ofNat offset), .i64 pointer, .i64 owner])
      (fun final values => final = initial ∧
        values = [.i64 (dotColumn4 weights offset width column x)]) := by
  have hsize := ha.size_lt
  have hw : width < UInt64.size := by omega
  have hs (a b : Nat) (h : a+b < UInt64.size) :
      ¬UInt64.ofNat (a+b) < UInt64.ofNat a := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h,
      UInt64.toNat_ofNat_of_lt' (by omega)]
    omega
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func25 _ initial
    (func25Def.toLocals [.i64 owner, .i64 pointer, .i64 (UInt64.ofNat offset),
      .i64 (UInt64.ofNat width), .i64 (UInt64.ofNat column),
      .i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3]) env
  unfold func25
  wp_fixed_frame [func25Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 19 20 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 19 20 _ _ _ _ pointer weights
    (offset+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  wp_fixed_frame [func25Def]
  wp_column_add hs
  wp_fixed_frame [func25Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 19 20 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 19 20 _ _ _ _ pointer weights
    (offset+width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 27 28 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 27 28 _ _ _ _ 2 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 2*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func25Def]
  rw [show (2 : UInt64)*UInt64.ofNat width = UInt64.ofNat (2*width) from
    (UInt64.ofNat_mul 2 width).symm]
  wp_column_add hs
  wp_fixed_frame [func25Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 19 20 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 19 20 _ _ _ _ pointer weights
    (offset+2*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 27 28 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 27 28 _ _ _ _ 3 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 3*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func25Def]
  rw [show (3 : UInt64)*UInt64.ofNat width = UInt64.ofNat (3*width) from
    (UInt64.ofNat_mul 3 width).symm]
  wp_column_add hs
  wp_fixed_frame [func25Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 19 20 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 19 20 _ _ _ _ pointer weights
    (offset+3*width+column) [] rfl rfl rfl ha hb _ _ ?_
  wp_fixed_frame [func25Def]
  refine wp_call_tw (dot4_exact env initial _ _ _ _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func25Def]
  simp [dotColumn4, getElem!_pos, show offset+column < weights.size by omega,
    show offset+width+column < weights.size by omega,
    show offset+2*width+column < weights.size by omega, hb]

#print axioms dotColumn4_exact
end Project.TinyGpt2Hidden.Spec
