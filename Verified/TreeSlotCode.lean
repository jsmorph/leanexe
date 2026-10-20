import Verified.TreeMemory
import Verified.TreeAdvance

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem treeSlotAddress_eq (p : UInt64) (i : Nat) :
    (p + UInt64.ofNat i * 8).toUInt32 = slotAddress p i := by
  unfold slotAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

theorem wp_treeSlotAddress {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hNext : wp m rest Q store { s with values := .i32 (slotAddress p i) :: s.values } host) :
    wp m (treeSlotAddress ptr index ++ rest) Q store s host := by
  simpa only [treeSlotAddress, List.cons_append, List.nil_append, wp_localGet_cons,
    Locals.get_values, hPtr, hIndex, wp_constI64_cons, wp_mulI64_cons, wp_addI64_cons,
    wp_wrapI64_cons, wrap_toUInt32, treeSlotAddress_eq] using hNext

theorem wp_treeSlotLoad {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q store
      { s with values := .i64 (store.mem.read64 (slotAddress p i)) :: s.values } host) :
    wp m (treeSlotAddress ptr index ++ .load64 0 :: rest) Q store s host := by
  apply wp_treeSlotAddress hPtr hIndex
  simpa only [wp_load64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
    ite_eq_right (Nat.not_lt.mpr hRoom)] using hNext

theorem wp_treeSlotStore {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index value i : Nat} {p word : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hValue : s.get value = some (.i64 word))
    (hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q { store with mem := store.mem.write64 (slotAddress p i) word } s host) :
    wp m (treeSlotAddress ptr index ++ [.localGet value, .store64 0] ++ rest) Q store s host := by
  apply wp_treeSlotAddress hPtr hIndex
  simp only [Locals.get] at hValue
  simpa [wp_simp, hValue, hRoom, Nat.not_lt.mpr hRoom] using hNext

theorem wp_treeCopyAdvance {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {ptr index i : Nat} {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) (hIndex : s.get index = some (.i64 (UInt64.ofNat i)))
    (hRoom : (p - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hNext : wp m rest Q (recordHeaderWrite store p 8 (UInt64.ofNat (i + 1))) s host) :
    wp m (treeCopyAdvance ptr index ++ rest) Q store s host := by
  simp only [Locals.get] at hPtr hIndex
  simp only [UInt64.toUInt32_sub] at hRoom
  change (p.toUInt32 - 8).toNat + 8 ≤ store.mem.pages * 65536 at hRoom
  simpa [treeCopyAdvance, headerStore, wp_simp, hPtr, hIndex, wrap_toUInt32_num,
    hRoom, Nat.not_lt.mpr hRoom, recordHeaderWrite, UInt64.ofNat_add] using hNext

#print axioms wp_treeSlotStore
#print axioms wp_treeCopyAdvance

end Verified
