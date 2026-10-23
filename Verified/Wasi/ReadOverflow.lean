import Verified.Wasi.ReadLocals

namespace Verified.Wasi

open Wasm

theorem wp_read_overflow {World : Type} {m : Module} {env : HostEnv World}
    {store : Store World} {Q : Assertion World} {rest : Program}
    {capacity root errno length : UInt64} {values : List Value}
    (hCapacity : 4294967296 ≤ capacity.toNat)
    (hNext : wp m rest Q store
      (readLocals capacity 0 61 0 (.i64 0 :: .i64 0 :: .i64 61 :: values)) env) :
    wp m (readCode 0 1 2 3 ++ rest) Q store
      (readLocals capacity root errno length values) env := by
  have hLarge : (4294967296 : UInt64) ≤ capacity := by
    rw [UInt64.le_iff_toNat_le]
    exact hCapacity
  simp only [readCode, List.cons_append, List.nil_append, wp_localGet_cons,
    readLocals_capacity, wp_constI64_cons, wp_geUI64_cons, ge_iff_le, hLarge,
    ite_true, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
  simp only [wp_constI64_cons]
  refine wp_localSet_local (by change 1 ≤ 2; omega) (by change 2 < 4; omega) ?_
  change wp m _ _ store (readLocals capacity root 61 length values) env
  simp only [wp_constI64_cons]
  refine wp_localSet_local (by change 1 ≤ 1; omega) (by change 1 < 4; omega) ?_
  change wp m _ _ store (readLocals capacity 0 61 length values) env
  simp only [wp_constI64_cons]
  refine wp_localSet_local (by change 1 ≤ 3; omega) (by change 3 < 4; omega) ?_
  change wp m _ _ store (readLocals capacity 0 61 0 values) env
  simpa only [wp_nil, List.take_zero, List.nil_append, List.drop_zero,
    wp_localGet_cons, readLocals_errno, readLocals_root, readLocals_length,
    readLocals_values, readLocals_stack] using hNext

end Verified.Wasi
