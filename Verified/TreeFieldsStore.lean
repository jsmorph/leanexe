import Verified.TreeFieldsCode
import Verified.TreeFieldsMemory
import Verified.LocalFrame

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

theorem wp_recordStoreCode {m : Module} {host : HostEnv Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) :
    ∀ (i : Nat) (srcs : List Nat) (words : List UInt64) (store : Store Unit),
      List.Forall₂ (fun src word => s.get src = some (.i64 word)) srcs words →
      p.toNat + 8 * (i + words.length) < 4294967296 →
      p.toNat + 8 * (i + words.length) ≤ store.mem.pages * 65536 →
      wp m rest Q (recordWriteValues p i words store) s host →
      wp m (recordStoreCode ptr i srcs ++ rest) Q store s host
  | _, [], [], _, _, _, _, hNext => hNext
  | i, src :: srcs, word :: words, store, hValues, hAddress, hMemory, hNext => by
    obtain ⟨hValue, hValues⟩ := List.forall₂_cons.mp hValues
    have hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      simp only [List.length_cons] at hMemory
      omega
    change (p + UInt64.ofNat (8 * i)).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 at hRoom
    have hRest := wp_recordStoreCode hPtr (i + 1) srcs words
      { store with mem := store.mem.write64 (slotAddress p i) word } hValues
      (by simp only [List.length_cons] at hAddress; omega)
      (by simp only [Mem.write64_pages]; simp only [List.length_cons] at hMemory; omega) hNext
    simpa only [recordStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Locals.get_values, hPtr, hValue, wp_constI64_cons, wp_addI64_cons,
      wp_wrapI64_cons, wrap_toUInt32, slotAddress, wp_store64_cons, UInt32.toNat_zero,
      Nat.add_zero, UInt32.add_zero, ite_eq_right (Nat.not_lt.mpr hRoom)] using hRest

end Verified
