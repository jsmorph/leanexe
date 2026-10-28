import Verified.Bytes.Release
import Verified.Bytes.Code
import Verified.LocalFrame
import LeanExe.TalosCompat

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- `normalizeCode` on an owned buffer: an empty buffer's object is released and its root set
to 0, and a nonempty buffer is left as it is. -/
theorem wp_normalize {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {root length : UInt64} {bytes : LeanExe.Bytes}
    {rootSlot lengthSlot : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hRep : Rep heap store root length bytes)
    (hRootLocal : s.get rootSlot = some (.i64 root))
    (hLengthLocal : s.get lengthSlot = some (.i64 length))
    (hLow : s.params.length ≤ rootSlot) (hHigh : rootSlot < s.params.length + s.locals.length)
    (hEmpty : length = 0 →
      wp m rest Q (releasedStore heap store root)
        { setLocal s rootSlot (.i64 0) with values := s.values } host)
    (hFull : length ≠ 0 → wp m rest Q store s host) :
    wp m (normalizeCode rootSlot lengthSlot ++ rest) Q store s host := by
  simp only [normalizeCode, List.cons_append, List.nil_append, wp_localGet_cons, hLengthLocal,
    wp_eqzI64_cons]
  refine wp_iff_cons rfl ?_
  by_cases hZero : length = 0
  · subst length
    simp (config := { decide := true }) only [ite_true, List.take_zero, List.drop_zero,
      List.nil_append]
    simp only [wp_localGet_cons, hRootLocal]
    refine wp_release hm hHeap hRep ?_
    simp only [wp_constI64_cons]
    refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
    rw [wp_nil]
    exact hEmpty rfl
  · simp (config := { decide := true }) only [hZero, ite_false, List.take_zero, List.drop_zero,
      List.nil_append]
    rw [wp_nil]
    simpa using hFull hZero

#print axioms wp_normalize

end Verified.Bytes
