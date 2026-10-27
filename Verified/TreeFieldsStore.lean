import Verified.TreeFieldsCode
import Verified.TreeFieldsMemory
import Verified.LocalFrame
import Verified.WordCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- The locals of the positions `srcs`, of the types `tys`, hold the values whose words are
`words`, and each value's word is the word it was made from. -/
def SourcesHold (s : Locals) (h : Nat) : List Nat → List ValueType → List UInt64 → Prop
  | [], _, [] => True
  | src :: srcs, tys, word :: words =>
    s.get (slotIndex h src (tys.headD .i64)) = some (typedValue (tys.headD .i64) word) ∧
      Value.word (typedValue (tys.headD .i64) word) = word ∧ SourcesHold s h srcs tys.tail words
  | _, _, _ => False

theorem SourcesHold.length {s : Locals} {h : Nat} :
    ∀ {srcs : List Nat} {tys : List ValueType} {words : List UInt64},
      SourcesHold s h srcs tys words → words.length = srcs.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, hold => congrArg (· + 1) (SourcesHold.length hold.2.2)

theorem wp_recordStoreCode {m : Module} {host : HostEnv Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {rest : Program} {Q : Assertion Unit}
    (hPtr : s.get ptr = some (.i64 p)) :
    ∀ (i : Nat) (srcs : List Nat) (tys : List ValueType) (words : List UInt64)
      (store : Store Unit),
      SourcesHold s s.positions srcs tys words →
      p.toNat + 8 * (i + words.length) < 4294967296 →
      p.toNat + 8 * (i + words.length) ≤ store.mem.pages * 65536 →
      wp m rest Q (recordWriteValues p i words store) s host →
      wp m (recordStoreCode s.positions ptr i srcs tys ++ rest) Q store s host
  | _, [], _, [], _, _, _, _, hNext => hNext
  | i, src :: srcs, tys, word :: words, store, hold, hAddress, hMemory, hNext => by
    obtain ⟨hValue, hWord, hold⟩ := hold
    have hRoom : (slotAddress p i).toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      simp only [List.length_cons] at hMemory
      omega
    change (p + UInt64.ofNat (8 * i)).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 at hRoom
    have hRest := wp_recordStoreCode hPtr (i + 1) srcs tys.tail words
      { store with mem := store.mem.write64 (slotAddress p i) word } hold
      (by simp only [List.length_cons] at hAddress; omega)
      (by simp only [Mem.write64_pages]; simp only [List.length_cons] at hMemory; omega) hNext
    have hStore : wp m (.store64 0 :: (recordStoreCode s.positions ptr (i + 1) srcs tys.tail ++
        rest)) Q store
        { s with
          values := .i64 (Value.word (typedValue (tys.headD .i64) word)) ::
            .i32 (p + UInt64.ofNat (8 * i)).toUInt32 :: s.values } host := by
      rw [hWord]
      simpa only [wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero,
        ite_eq_right (Nat.not_lt.mpr hRoom), slotAddress] using hRest
    have hConvert := (wp_toWordCode (m := m) (st := store) (env' := host) (s := s)
      (vs := .i32 (p + UInt64.ofNat (8 * i)).toUInt32 :: s.values)
      (rest := .store64 0 :: (recordStoreCode s.positions ptr (i + 1) srcs tys.tail ++ rest))
      (Q := Q) (tys.headD .i64) word).mpr hStore
    simpa only [recordStoreCode, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Locals.get_values, hPtr, hValue, wp_constI64_cons, wp_addI64_cons,
      wp_wrapI64_cons, wrap_toUInt32] using hConvert

end Verified
