import Project.ClobMatchFuel.TradeAppendCopy

/-!
# Matched-trade append stores

Each successful match appends one trade through four consecutive word stores.
This module states that memory transformation independently of generated local
indices.  Its theorems reconstruct the extended trade array and preserve its
fixed-array header.
-/

namespace Project.ClobMatchFuel.TradeAppendStore

open Wasm Project.Common Project.Clob Project.ClobMatchFuel.Allocation

def appendTradeStore (st : Store Unit) (ptr : UInt64) (n : Nat)
    (trade : TradeL) : Store Unit :=
  { st with
    mem := (((st.mem.write64
      (UInt32.ofNat ((ptr.toNat + (n * 4 + 1) * 8) % 4294967296))
        trade.ttakerId).write64
      (UInt32.ofNat ((ptr.toNat + (n * 4 + 2) * 8) % 4294967296))
        trade.tmakerId).write64
      (UInt32.ofNat ((ptr.toNat + (n * 4 + 3) * 8) % 4294967296))
        trade.tprice).write64
      (UInt32.ofNat ((ptr.toNat + (n * 4 + 4) * 8) % 4294967296))
        trade.tqty }

theorem appendTradeStore_read_before
    (st : Store Unit) (ptr : UInt64) (n : Nat) (trade : TradeL)
    (b : UInt32)
    (hAddr : ptr.toNat + ((n + 1) * 4 + 1) * 8 < 4294967296)
    (hBefore : b.toNat + 8 ≤ ptr.toNat + (n * 4 + 1) * 8) :
    (appendTradeStore st ptr n trade).mem.read64 b = st.mem.read64 b := by
  unfold appendTradeStore
  rw [read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl hBefore)]

theorem appendTradeStore_reads
    (st : Store Unit) (ptr : UInt64) (n : Nat) (trade : TradeL)
    (hAddr : ptr.toNat + ((n + 1) * 4 + 1) * 8 < 4294967296) :
    tradeWord (appendTradeStore st ptr n trade) ptr (n * 4) =
        trade.ttakerId ∧
    tradeWord (appendTradeStore st ptr n trade) ptr (n * 4 + 1) =
        trade.tmakerId ∧
    tradeWord (appendTradeStore st ptr n trade) ptr (n * 4 + 2) =
        trade.tprice ∧
    tradeWord (appendTradeStore st ptr n trade) ptr (n * 4 + 3) =
        trade.tqty := by
  have hAddress (field : Nat) (hfield1 : 1 ≤ field)
      (hfield4 : field ≤ 4) :
      (UInt32.ofNat
        ((ptr.toNat + (n * 4 + field) * 8) % 4294967296)).toNat =
        ptr.toNat + (n * 4 + field) * 8 := by
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
  have hDisjoint (a b : Nat) (ha1 : 1 ≤ a) (ha4 : a ≤ 4)
      (hb1 : 1 ≤ b) (hb4 : b ≤ 4) (hne : a ≠ b) :
      (UInt32.ofNat
          ((ptr.toNat + (n * 4 + a) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((ptr.toNat + (n * 4 + b) * 8) % 4294967296)).toNat ∨
        (UInt32.ofNat
          ((ptr.toNat + (n * 4 + b) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((ptr.toNat + (n * 4 + a) * 8) % 4294967296)).toNat := by
    rw [hAddress a ha1 ha4, hAddress b hb1 hb4]
    omega
  unfold tradeWord appendTradeStore
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [read64_write64_ne _ _ _ _
        (hDisjoint 1 4 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
        (hDisjoint 1 3 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
        (hDisjoint 1 2 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _
        (hDisjoint 2 4 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
        (hDisjoint 2 3 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _
        (hDisjoint 3 4 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      Mem.read64_write64_same]
  · rw [Mem.read64_write64_same]

theorem tradesAt_appendTradeStore
    (st : Store Unit) (ptr : UInt64) (ts : List TradeL) (trade : TradeL)
    (hAddr : ptr.toNat + ((ts.length + 1) * 4 + 1) * 8 < 4294967296)
    (hLength : st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) =
      UInt64.ofNat (ts.length + 1))
    (hLengthBound : ptr.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536)
    (hOldWord : ∀ (j : Nat), j < ts.length → ∀ field : Nat, field < 4 →
      tradeWord st ptr (j * 4 + field) = ts[j]!.word field)
    (hBound : ∀ (j : Nat), j < ts.length + 1 → ∀ field : Nat, field < 4 →
      (ptr.toNat + (j * 4 + field + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) :
    TradesAt (appendTradeStore st ptr ts.length trade) ptr
      (ts ++ [trade]) := by
  apply TradesAt.ofFlatWords
  · calc
      _ = st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) :=
        appendTradeStore_read_before st ptr ts.length trade _ hAddr (by
          rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
          omega)
      _ = UInt64.ofNat (ts.length + 1) := hLength
      _ = UInt64.ofNat (ts ++ [trade]).length := by simp
  · simpa only [appendTradeStore, Mem.write64_pages] using hLengthBound
  · intro j hj field hfield
    by_cases hjOld : j < ts.length
    · have hGet : (ts ++ [trade])[j]! = ts[j]! := by
        rw [getBang_eq hj, getBang_eq hjOld]
        exact List.getElem_append_left hjOld
      rw [hGet]
      calc
        tradeWord (appendTradeStore st ptr ts.length trade) ptr
            (j * 4 + field) = tradeWord st ptr (j * 4 + field) := by
          unfold tradeWord
          apply appendTradeStore_read_before st ptr ts.length trade _ hAddr
          rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
          omega
        _ = ts[j]!.word field := hOldWord j hjOld field hfield
    · have hjEq : j = ts.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      have hGet : (ts ++ [trade])[ts.length]! = trade := by
        simp [getElem!_pos]
      rw [hGet]
      obtain ⟨h1, h2, h3, h4⟩ :=
        appendTradeStore_reads st ptr ts.length trade hAddr
      interval_cases field
      · simpa [TradeL.word] using h1
      · simpa [TradeL.word] using h2
      · simpa [TradeL.word] using h3
      · simpa [TradeL.word] using h4
  · intro j hj field hfield
    simpa only [appendTradeStore, Mem.write64_pages, List.length_append,
      List.length_singleton] using hBound j (by simpa using hj) field hfield

theorem freshTradeArrayAt_appendTradeStore
    (st : Store Unit) (ptr capacity : UInt64) (n : Nat) (trade : TradeL)
    (hPtr48 : 48 ≤ ptr.toNat)
    (hAddr : ptr.toNat + ((n + 1) * 4 + 1) * 8 < 4294967296)
    (hFresh : FreshTradeArrayAt st ptr capacity) :
    FreshTradeArrayAt (appendTradeStore st ptr n trade) ptr capacity := by
  have hData (field : Nat) (hfield1 : 1 ≤ field)
      (hfield4 : field ≤ 4) :
      ptr.toNat ≤
        (UInt32.ofNat
          ((ptr.toNat + (n * 4 + field) * 8) % 4294967296)).toNat := by
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have h1 := FreshFixedArrayAt.write64_data
    (value := trade.ttakerId) hFresh hPtr48
    (hData 1 (by omega) (by omega))
  have h2 := FreshFixedArrayAt.write64_data
    (value := trade.tmakerId) h1 hPtr48
    (hData 2 (by omega) (by omega))
  have h3 := FreshFixedArrayAt.write64_data
    (value := trade.tprice) h2 hPtr48
    (hData 3 (by omega) (by omega))
  have h4 := FreshFixedArrayAt.write64_data
    (value := trade.tqty) h3 hPtr48
    (hData 4 (by omega) (by omega))
  simpa only [appendTradeStore] using h4

end Project.ClobMatchFuel.TradeAppendStore
