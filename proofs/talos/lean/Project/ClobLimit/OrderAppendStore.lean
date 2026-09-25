import Project.ClobPostOnly.AppendStore

namespace Project.ClobLimit.OrderAppendStore

open Wasm Project.Common Project.Clob

def appendOrderStore (st : Store Unit) (target : UInt64) (n : Nat)
    (order : OrderL) : Store Unit :=
  { st with
    mem := ((((st.mem.write64
      (UInt32.ofNat ((target.toNat + (n * 5 + 1) * 8) % 4294967296)) order.oid).write64
      (UInt32.ofNat ((target.toNat + (n * 5 + 2) * 8) % 4294967296)) order.otrader).write64
      (UInt32.ofNat ((target.toNat + (n * 5 + 3) * 8) % 4294967296)) order.oside).write64
      (UInt32.ofNat ((target.toNat + (n * 5 + 4) * 8) % 4294967296)) order.oprice).write64
      (UInt32.ofNat ((target.toNat + (n * 5 + 5) * 8) % 4294967296)) order.oqty }

theorem headerBase (target : UInt64) (hTarget : 48 ≤ target.toNat) :
    (target - 48).toNat + 48 = target.toNat := by
  rw [toNat_sub_le target 48 (by simpa using hTarget)]
  change target.toNat - 48 + 48 = target.toNat
  omega

theorem eq_from_header (st : Store Unit) (target : UInt64) (n : Nat)
    (order : OrderL) (hTarget : 48 ≤ target.toNat) :
    appendOrderStore st target n order =
      Project.ClobPostOnly.AppendStore.appendOrderStore st (target - 48) n order := by
  simp only [appendOrderStore, Project.ClobPostOnly.AppendStore.appendOrderStore,
    headerBase target hTarget]

theorem appendOrderStore_read_before (st : Store Unit) (target : UInt64)
    (n : Nat) (order : OrderL) (b : UInt32) (hTarget : 48 ≤ target.toNat)
    (hAddr : target.toNat + (n * 5 + 5) * 8 < 4294967296)
    (hBefore : b.toNat + 8 ≤ target.toNat + (n * 5 + 1) * 8) :
    (appendOrderStore st target n order).mem.read64 b = st.mem.read64 b := by
  rw [eq_from_header st target n order hTarget]
  apply Project.ClobPostOnly.AppendStore.appendOrderStore_read_before
  · simpa only [headerBase target hTarget] using hAddr
  · simpa only [headerBase target hTarget] using hBefore

theorem appendOrderStore_reads (st : Store Unit) (target : UInt64)
    (n : Nat) (order : OrderL) (hTarget : 48 ≤ target.toNat)
    (hAddr : target.toNat + (n * 5 + 5) * 8 < 4294967296) :
    (appendOrderStore st target n order).mem.read64
        (UInt32.ofNat ((target.toNat + (n * 5 + 1) * 8) % 4294967296)) = order.oid ∧
    (appendOrderStore st target n order).mem.read64
        (UInt32.ofNat ((target.toNat + (n * 5 + 2) * 8) % 4294967296)) = order.otrader ∧
    (appendOrderStore st target n order).mem.read64
        (UInt32.ofNat ((target.toNat + (n * 5 + 3) * 8) % 4294967296)) = order.oside ∧
    (appendOrderStore st target n order).mem.read64
        (UInt32.ofNat ((target.toNat + (n * 5 + 4) * 8) % 4294967296)) = order.oprice ∧
    (appendOrderStore st target n order).mem.read64
        (UInt32.ofNat ((target.toNat + (n * 5 + 5) * 8) % 4294967296)) = order.oqty := by
  rw [eq_from_header st target n order hTarget]
  simpa only [headerBase target hTarget] using
    Project.ClobPostOnly.AppendStore.appendOrderStore_reads st (target - 48) n order
      (by simpa only [headerBase target hTarget] using hAddr)

end Project.ClobLimit.OrderAppendStore
