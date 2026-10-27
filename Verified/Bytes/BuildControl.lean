import Verified.Bytes.BuildCode
import Verified.LocalFrame
import LeanExe.TalosCompat
import LeanExe.Pipeline.Aborts

namespace Verified.Bytes

open Wasm

theorem wp_build_zero {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {count destination index : Nat} {element rest : Program} {Q : Assertion Unit}
    (hCount : s.get count = some (.i64 0))
    (hNext : wp m rest Q store { s with values := .i64 0 :: .i64 0 :: s.values } host) :
    wp m (buildCode count destination index element ++ rest) Q store s host := by
  simp only [buildCode, List.cons_append, List.nil_append, wp_localGet_cons, hCount,
    wp_constI64_cons, wp_geUI64_cons]
  refine wp_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte, wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append, wp_localGet_cons,
    Locals.get_values, hCount, wp_constI64_cons, wp_eqI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp only [Locals.get] at hCount
  simpa [wp_simp, hCount] using hNext

theorem wp_build_overflow {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {length : UInt64} {count destination index : Nat} {element rest : Program}
    {Q : Assertion Unit} (hCount : s.get count = some (.i64 length))
    (hLarge : 4294967296 ≤ length) (hTrap : TrapOK true Q) :
    wp m (buildCode count destination index element ++ rest) Q store s host := by
  simp only [buildCode, List.cons_append, List.nil_append, wp_localGet_cons, hCount,
    wp_constI64_cons, wp_geUI64_cons]
  refine wp_iff_cons rfl ?_
  simp (config := { decide := true }) only [ge_iff_le, hLarge, ↓reduceIte]
  rw [wp_unreachable_cons]
  exact hTrap _

end Verified.Bytes
