import Project.TinyGpt2Hidden.Components
import Project.ProofKit.CheckedArrayGet

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit

def rowResults (x : Row) : List Value := [.i64 x.x3, .i64 x.x2, .i64 x.x1, .i64 x.x0]

@[simp] theorem rowResults_length (x : Row) : (rowResults x).length = 4 := rfl

theorem loadRow_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (offset : Nat)
    (ha : UInt64Array.At initial pointer weights) (hb : offset+3 < weights.size) :
    TerminatesWith env Project.TinyGpt2Hidden.module 5 initial
      [.i64 (UInt64.ofNat offset), .i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = rowResults (loadRow weights offset)) := by
  refine TerminatesWith.of_wp_entry_for (f := func5Def) rfl ?_ (by decide)
  change wp Project.TinyGpt2Hidden.module func5 _ initial
    (func5Def.toLocals [.i64 owner, .i64 pointer, .i64 (UInt64.ofNat offset)]) env
  unfold func5
  rw [wp_localGet_cons]
  simp only [func5Def, Function.toLocals, Locals.get, Function.numParams, List.length,
    List.getElem?_cons, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.succ_ne_zero, List.map, ValueType.zero,
    reduceIte, wp_localSet_cons, Locals.set?, List.set]
  rw [wp_localGet_cons]
  simp only [Locals.get, List.length, List.getElem?_cons, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceSub, Nat.succ_ne_zero, reduceIte, wp_localSet_cons, Locals.set?, List.set]
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 7 8 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 7 8 _ _ _ _ pointer weights offset []
    rfl rfl rfl ha (by omega) _ _ ?_
  have hs (k : Nat) (hk : k ≤ 3) : ¬UInt64.ofNat offset+UInt64.ofNat k < UInt64.ofNat offset := by
    rw [← UInt64.ofNat_add, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' (by have hh := ha.size_lt; omega),
      UInt64.toNat_ofNat_of_lt' (by have hh := ha.size_lt; omega)]
    omega
  wp_fixed_frame [func5Def]
  try simp only [Wasm.wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have h1 : ¬UInt64.ofNat offset+1 < UInt64.ofNat offset := hs 1 (by decide)
  simp only [h1, reduceIte, ne_eq, not_true_eq_false]
  rw [wp_localGet_cons]
  simp only [Locals.get, List.length, List.getElem?_cons, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceSub, Nat.succ_ne_zero, reduceIte, wp_localSet_cons, Locals.set?, List.set,
    wp_nil, List.take, List.drop, List.append_nil]
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 7 8 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 7 8 _ _ _ _ pointer weights (offset+1) []
    rfl ?_ rfl ha (by omega) _ _ ?_
  · simp only [Locals.get]
    change some (Value.i64 (UInt64.ofNat offset + UInt64.ofNat 1)) =
      some (Value.i64 (UInt64.ofNat (offset+1)))
    rw [UInt64.ofNat_add]
  wp_fixed_frame [func5Def]
  try simp only [Wasm.wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have h2 : ¬UInt64.ofNat offset+2 < UInt64.ofNat offset := hs 2 (by decide)
  simp only [h2, reduceIte, ne_eq, not_true_eq_false]
  rw [wp_localGet_cons]
  simp only [Locals.get, List.length, List.getElem?_cons, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceSub, Nat.succ_ne_zero, reduceIte, wp_localSet_cons, Locals.set?, List.set,
    wp_nil, List.take, List.drop, List.append_nil]
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 7 8 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 7 8 _ _ _ _ pointer weights (offset+2) []
    rfl ?_ rfl ha (by omega) _ _ ?_
  · simp only [Locals.get]
    change some (Value.i64 (UInt64.ofNat offset + UInt64.ofNat 2)) =
      some (Value.i64 (UInt64.ofNat (offset+2)))
    rw [UInt64.ofNat_add]
  wp_fixed_frame [func5Def]
  try simp only [Wasm.wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  have h3 : ¬UInt64.ofNat offset+3 < UInt64.ofNat offset := hs 3 (by decide)
  simp only [h3, reduceIte, ne_eq, not_true_eq_false]
  rw [wp_localGet_cons]
  simp only [Locals.get, List.length, List.getElem?_cons, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceSub, Nat.succ_ne_zero, reduceIte, wp_localSet_cons, Locals.set?, List.set,
    wp_nil, List.take, List.drop, List.append_nil]
  change wp Project.TinyGpt2Hidden.module (CheckedArrayGet.checkedGetCore 7 8 ++ _)
    _ initial _ env
  refine CheckedArrayGet.checkedGetCore_spec 7 8 _ _ _ _ pointer weights (offset+3) []
    rfl ?_ rfl ha (by omega) _ _ ?_
  · simp only [Locals.get]
    change some (Value.i64 (UInt64.ofNat offset + UInt64.ofNat 3)) =
      some (Value.i64 (UInt64.ofNat (offset+3)))
    rw [UInt64.ofNat_add]
  wp_fixed_frame [func5Def]
  simp [rowResults, loadRow, getElem!_pos, show offset < weights.size by omega,
    show offset+1 < weights.size by omega, show offset+2 < weights.size by omega, hb]

#print axioms loadRow_exact

end Project.TinyGpt2Hidden.Spec
