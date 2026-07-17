import Project.ClobPostOnly.Allocation

/-!
# Appended order stores

The successful `postOnly` branch appends one order through five consecutive
64-bit writes.  This module states that store transformation independently of
the generated instruction proof and proves its read behavior.  Later phases
use these facts without elaborating the five writes again.
-/

namespace Project.ClobPostOnly.AppendStore

open Wasm Project.Common Project.Clob

def appendOrderStore (st : Store Unit) (g0 : UInt64) (n : Nat)
    (order : OrderL) : Store Unit :=
  { st with
    mem := ((((st.mem.write64
      (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 1) * 8) % 4294967296))
        order.oid).write64
      (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 2) * 8) % 4294967296))
        order.otrader).write64
      (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 3) * 8) % 4294967296))
        order.oside).write64
      (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 4) * 8) % 4294967296))
        order.oprice).write64
      (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 5) * 8) % 4294967296))
        order.oqty }

theorem appendOrderStore_read_before
    (st : Store Unit) (g0 : UInt64) (n : Nat) (order : OrderL)
    (b : UInt32)
    (hAddr : g0.toNat + 48 + (n * 5 + 5) * 8 < 4294967296)
    (hBefore : b.toNat + 8 ≤ g0.toNat + 48 + (n * 5 + 1) * 8) :
    (appendOrderStore st g0 n order).mem.read64 b = st.mem.read64 b := by
  unfold appendOrderStore
  rw [read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl hBefore)]

theorem appendOrderStore_reads
    (st : Store Unit) (g0 : UInt64) (n : Nat) (order : OrderL)
    (hAddr : g0.toNat + 48 + (n * 5 + 5) * 8 < 4294967296) :
    (appendOrderStore st g0 n order).mem.read64
        (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 1) * 8) % 4294967296)) =
          order.oid ∧
    (appendOrderStore st g0 n order).mem.read64
        (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 2) * 8) % 4294967296)) =
          order.otrader ∧
    (appendOrderStore st g0 n order).mem.read64
        (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 3) * 8) % 4294967296)) =
          order.oside ∧
    (appendOrderStore st g0 n order).mem.read64
        (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 4) * 8) % 4294967296)) =
          order.oprice ∧
    (appendOrderStore st g0 n order).mem.read64
        (UInt32.ofNat ((g0.toNat + 48 + (n * 5 + 5) * 8) % 4294967296)) =
          order.oqty := by
  have hAddress (r : Nat) (hr1 : 1 ≤ r) (hr5 : r ≤ 5) :
      (UInt32.ofNat
        ((g0.toNat + 48 + (n * 5 + r) * 8) % 4294967296)).toNat =
        g0.toNat + 48 + (n * 5 + r) * 8 := by
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
  have hDisjoint (r s : Nat) (hr1 : 1 ≤ r) (hr5 : r ≤ 5)
      (hs1 : 1 ≤ s) (hs5 : s ≤ 5) (hne : r ≠ s) :
      (UInt32.ofNat
          ((g0.toNat + 48 + (n * 5 + r) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((g0.toNat + 48 + (n * 5 + s) * 8) % 4294967296)).toNat ∨
        (UInt32.ofNat
          ((g0.toNat + 48 + (n * 5 + s) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((g0.toNat + 48 + (n * 5 + r) * 8) % 4294967296)).toNat := by
    rw [hAddress r hr1 hr5, hAddress s hs1 hs5]
    omega
  unfold appendOrderStore
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [read64_write64_ne _ _ _ _
        (hDisjoint 1 5 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
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
        (hDisjoint 2 5 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
        (hDisjoint 2 4 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
        (hDisjoint 2 3 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _
        (hDisjoint 3 5 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      read64_write64_ne _ _ _ _
        (hDisjoint 3 4 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _
        (hDisjoint 4 5 (by omega) (by omega) (by omega) (by omega)
          (by omega)),
      Mem.read64_write64_same]
  · rw [Mem.read64_write64_same]

end Project.ClobPostOnly.AppendStore
