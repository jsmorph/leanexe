import Project.TinyGpt2Hidden.Column

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def wideResults (x : WideRow) : List Value := rowResults x.high ++ rowResults x.low

@[simp] theorem wideResults_length (x : WideRow) : (wideResults x).length = 8 := rfl

theorem dotColumn8_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (offset width column : Nat) (x : WideRow)
    (ha : UInt64Array.At initial pointer weights)
    (hb : offset+7*width+column < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 66 initial
      (wideResults x ++ [.i64 (UInt64.ofNat column), .i64 (UInt64.ofNat width),
        .i64 (UInt64.ofNat offset), .i64 pointer, .i64 owner])
      (fun final values => final = initial ∧
        values = [.i64 (dotColumn8 weights offset width column x)]) := by
  have hsize := ha.size_lt
  have hw : width < UInt64.size := by omega
  have hs (a b : Nat) (h : a+b < UInt64.size) :
      ¬UInt64.ofNat (a+b) < UInt64.ofNat a := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h,
      UInt64.toNat_ofNat_of_lt' (by omega)]
    omega
  refine TerminatesWith.of_wp_entry_for (f := func66Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func66 _ initial
    (func66Def.toLocals [.i64 owner, .i64 pointer, .i64 (UInt64.ofNat offset),
      .i64 (UInt64.ofNat width), .i64 (UInt64.ofNat column),
      .i64 x.low.x0, .i64 x.low.x1, .i64 x.low.x2, .i64 x.low.x3,
      .i64 x.high.x0, .i64 x.high.x1, .i64 x.high.x2, .i64 x.high.x3]) env
  unfold func66
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  wp_fixed_frame [func66Def]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 39 40 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 39 40 _ _ _ _ 2 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 2*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func66Def]
  rw [show (2 : UInt64)*UInt64.ofNat width = UInt64.ofNat (2*width) from
    (UInt64.ofNat_mul 2 width).symm]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+2*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 39 40 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 39 40 _ _ _ _ 3 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 3*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func66Def]
  rw [show (3 : UInt64)*UInt64.ofNat width = UInt64.ofNat (3*width) from
    (UInt64.ofNat_mul 3 width).symm]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+3*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 39 40 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 39 40 _ _ _ _ 4 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 4*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func66Def]
  rw [show (4 : UInt64)*UInt64.ofNat width = UInt64.ofNat (4*width) from
    (UInt64.ofNat_mul 4 width).symm]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+4*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 39 40 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 39 40 _ _ _ _ 5 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 5*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func66Def]
  rw [show (5 : UInt64)*UInt64.ofNat width = UInt64.ofNat (5*width) from
    (UInt64.ofNat_mul 5 width).symm]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+5*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 39 40 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 39 40 _ _ _ _ 6 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 6*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func66Def]
  rw [show (6 : UInt64)*UInt64.ofNat width = UInt64.ofNat (6*width) from
    (UInt64.ofNat_mul 6 width).symm]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+6*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  iterate 9 wp_fixed_frame_step
  change wp Project.TinyGpt2Hidden.module (CheckedNatMul.program 39 40 ++ _) _ initial _ env
  refine CheckedNatMul.program_spec 39 40 _ _ _ _ 7 (UInt64.ofNat width) []
    rfl rfl rfl ?_ _ _ ?_
  · change 7*(UInt64.ofNat width).toNat < UInt64.size
    rw [UInt64.toNat_ofNat_of_lt' hw]
    omega
  wp_fixed_frame [func66Def]
  rw [show (7 : UInt64)*UInt64.ofNat width = UInt64.ofNat (7*width) from
    (UInt64.ofNat_mul 7 width).symm]
  wp_column_add hs
  wp_fixed_frame [func66Def]
  wp_column_add hs
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 31 32 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 31 32 _ _ _ _ pointer weights
    (offset+7*width+column) [] rfl rfl rfl ha (by omega) _ _ ?_
  wp_fixed_frame [func66Def]
  refine wp_call_tw (dot8_exact env initial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  wp_fixed_frame [func66Def]
  simp [dotColumn8, getElem!_pos, show offset+column < weights.size by omega,
    show offset+width+column < weights.size by omega,
    show offset+2*width+column < weights.size by omega,
    show offset+3*width+column < weights.size by omega,
    show offset+4*width+column < weights.size by omega,
    show offset+5*width+column < weights.size by omega,
    show offset+6*width+column < weights.size by omega,
    hb]

#print axioms dotColumn8_exact
end Project.TinyGpt2Hidden.Spec

