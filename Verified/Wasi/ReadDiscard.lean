import Verified.Wasi.ReadCode
import Verified.Wasi.Runtime
import Verified.LocalFrame

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.ProofKit

theorem wp_discard_read {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {s : Locals}
    {root length : UInt64} {bytes : LeanExe.Bytes} {rootSlot : Nat}
    {rest : Program} {Q : Assertion World}
    (hHeap : heap.At (PureTransport.erase store))
    (hBytes : Bytes.Rep heap (PureTransport.erase store) root length bytes)
    (hRoot : s.get rootSlot = some (.i64 root))
    (hLow : s.params.length ≤ rootSlot)
    (hHigh : rootSlot < s.params.length + s.locals.length)
    (hNext : ∀ final : Store World,
      PureTransport.erase final = Bytes.releasedStore heap (PureTransport.erase store) root →
      final.host = store.host →
      wp target rest Q final (setLocal s rootSlot (.i64 0)) targetHost) :
    wp target (discardReadCode rootSlot ++ rest) Q store s targetHost := by
  by_cases hZero : root = 0
  · subst root
    simp only [discardReadCode, List.cons_append, List.nil_append, wp_localGet_cons,
      hRoot, wp_eqzI64_cons, ite_true, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, wp_constI64_cons]
    refine wp_localSet_local hLow hHigh ?_
    simpa only [setLocal] using
      hNext store (by simp only [Bytes.releasedStore, ite_true]) rfl
  · simp only [discardReadCode, List.cons_append, List.nil_append, wp_localGet_cons,
      hRoot, wp_eqzI64_cons, ite_eq_right hZero, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
    simp only [wp_localGet_cons, Locals.get_values, hRoot]
    refine wp_release runtime layout profile hImports sourceHost hHeap hBytes ?_
    intro final hStore hWorld
    simp only [wp_nil, List.take_zero, List.nil_append, List.drop_zero, wp_constI64_cons]
    refine wp_localSet_local hLow hHigh ?_
    simpa only [setLocal] using hNext final hStore hWorld

end Verified.Wasi
