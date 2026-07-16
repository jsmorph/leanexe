import Project.ClobMatchFuel.Model
import Project.ClobMatchFuel.Allocation

/-!
# Partial-fill order stores

The partial-fill branch writes one copied order back through five consecutive
word stores, changing only its quantity.  This module names that memory
transformation and proves its structured order-array result and header frame.
-/

namespace Project.ClobMatchFuel.BookReplaceStore

open Wasm Project.Common Project.Clob Project.ClobMatchFuel.Allocation

def replaceOrderStore (st : Store Unit) (ptr : UInt64) (i : Nat)
    (order : OrderL) (qty : UInt64) : Store Unit :=
  { st with
    mem := ((((st.mem.write64
      (UInt32.ofNat ((ptr.toNat + (i * 5 + 1) * 8) % 4294967296))
        order.oid).write64
      (UInt32.ofNat ((ptr.toNat + (i * 5 + 2) * 8) % 4294967296))
        order.otrader).write64
      (UInt32.ofNat ((ptr.toNat + (i * 5 + 3) * 8) % 4294967296))
        order.oside).write64
      (UInt32.ofNat ((ptr.toNat + (i * 5 + 4) * 8) % 4294967296))
        order.oprice).write64
      (UInt32.ofNat ((ptr.toNat + (i * 5 + 5) * 8) % 4294967296))
        qty }

theorem replaceOrderStore_read_length
    (st : Store Unit) (ptr : UInt64) (os : List OrderL) (i : Nat)
    (order : OrderL) (qty : UInt64)
    (hi : i < os.length)
    (hAddr : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296) :
    (replaceOrderStore st ptr i order qty).mem.read64
        (UInt32.ofNat (ptr.toNat % 4294967296)) =
      st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) := by
  have hDisjoint (field : Nat) (hfield1 : 1 ≤ field)
      (hfield5 : field ≤ 5) :
      (UInt32.ofNat (ptr.toNat % 4294967296)).toNat + 8 ≤
        (UInt32.ofNat
          ((ptr.toNat + (i * 5 + field) * 8) % 4294967296)).toNat := by
    rw [toUInt32_ofNat_mod_toNat, toUInt32_ofNat_mod_toNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold replaceOrderStore
  rw [read64_write64_ne _ _ _ _ (Or.inl (hDisjoint 5 (by omega) (by omega))),
    read64_write64_ne _ _ _ _ (Or.inl (hDisjoint 4 (by omega) (by omega))),
    read64_write64_ne _ _ _ _ (Or.inl (hDisjoint 3 (by omega) (by omega))),
    read64_write64_ne _ _ _ _ (Or.inl (hDisjoint 2 (by omega) (by omega))),
    read64_write64_ne _ _ _ _ (Or.inl (hDisjoint 1 (by omega) (by omega)))]

theorem replaceOrderStore_reads
    (st : Store Unit) (ptr : UInt64) (os : List OrderL) (i : Nat)
    (order : OrderL) (qty : UInt64)
    (hi : i < os.length)
    (hAddr : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296) :
    orderWord (replaceOrderStore st ptr i order qty) ptr (i * 5) =
        order.oid ∧
    orderWord (replaceOrderStore st ptr i order qty) ptr (i * 5 + 1) =
        order.otrader ∧
    orderWord (replaceOrderStore st ptr i order qty) ptr (i * 5 + 2) =
        order.oside ∧
    orderWord (replaceOrderStore st ptr i order qty) ptr (i * 5 + 3) =
        order.oprice ∧
    orderWord (replaceOrderStore st ptr i order qty) ptr (i * 5 + 4) =
        qty := by
  have hAddress (field : Nat) (hfield1 : 1 ≤ field)
      (hfield5 : field ≤ 5) :
      (UInt32.ofNat
        ((ptr.toNat + (i * 5 + field) * 8) % 4294967296)).toNat =
        ptr.toNat + (i * 5 + field) * 8 := by
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
  have hDisjoint (a b : Nat) (ha1 : 1 ≤ a) (ha5 : a ≤ 5)
      (hb1 : 1 ≤ b) (hb5 : b ≤ 5) (hne : a ≠ b) :
      (UInt32.ofNat
          ((ptr.toNat + (i * 5 + a) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((ptr.toNat + (i * 5 + b) * 8) % 4294967296)).toNat ∨
        (UInt32.ofNat
          ((ptr.toNat + (i * 5 + b) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((ptr.toNat + (i * 5 + a) * 8) % 4294967296)).toNat := by
    rw [hAddress a ha1 ha5, hAddress b hb1 hb5]
    omega
  unfold orderWord replaceOrderStore
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

theorem replaceOrderStore_read_other
    (st : Store Unit) (ptr : UInt64) (os : List OrderL) (i j field : Nat)
    (order : OrderL) (qty : UInt64)
    (hi : i < os.length) (hj : j < os.length) (hfield : field < 5)
    (hij : i ≠ j)
    (hAddr : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296) :
    orderWord (replaceOrderStore st ptr i order qty) ptr (j * 5 + field) =
      orderWord st ptr (j * 5 + field) := by
  have hDisjoint (storedField : Nat) (hs1 : 1 ≤ storedField)
      (hs5 : storedField ≤ 5) :
      (UInt32.ofNat
          ((ptr.toNat + (j * 5 + field + 1) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((ptr.toNat + (i * 5 + storedField) * 8) % 4294967296)).toNat ∨
        (UInt32.ofNat
          ((ptr.toNat + (i * 5 + storedField) * 8) % 4294967296)).toNat + 8 ≤
          (UInt32.ofNat
            ((ptr.toNat + (j * 5 + field + 1) * 8) % 4294967296)).toNat := by
    simp only [toUInt32_ofNat_mod_toNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold orderWord replaceOrderStore
  rw [read64_write64_ne _ _ _ _ (hDisjoint 5 (by omega) (by omega)),
    read64_write64_ne _ _ _ _ (hDisjoint 4 (by omega) (by omega)),
    read64_write64_ne _ _ _ _ (hDisjoint 3 (by omega) (by omega)),
    read64_write64_ne _ _ _ _ (hDisjoint 2 (by omega) (by omega)),
    read64_write64_ne _ _ _ _ (hDisjoint 1 (by omega) (by omega))]

theorem ordersAt_replaceOrderStore
    (st : Store Unit) (ptr : UInt64) (os : List OrderL) (i : Nat)
    (qty : UInt64)
    (hi : i < os.length)
    (hAddr : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hOrders : OrdersAt st ptr os) :
    OrdersAt (replaceOrderStore st ptr i os[i]! qty) ptr
      (Model.setQtyL os i qty) := by
  apply OrdersAt.ofFlatWords
  · rw [Model.setQtyL_length]
    exact (replaceOrderStore_read_length st ptr os i os[i]! qty hi hAddr).trans
      hOrders.1.1
  · simpa only [Model.setQtyL_length, replaceOrderStore,
      Mem.write64_pages] using hOrders.1.2
  · intro j hj field hfield
    rw [Model.setQtyL_word os i j field qty hi (by simpa using hj) hfield]
    by_cases hij : i = j
    · subst j
      obtain ⟨h1, h2, h3, h4, h5⟩ :=
        replaceOrderStore_reads st ptr os i os[i]! qty hi hAddr
      interval_cases field
      · simpa [OrderL.word] using h1
      · simpa [OrderL.word] using h2
      · simpa [OrderL.word] using h3
      · simpa [OrderL.word] using h4
      · simpa [OrderL.word] using h5
    · rw [if_neg (by simp [hij])]
      exact (replaceOrderStore_read_other st ptr os i j field os[i]! qty
        hi (by simpa using hj) hfield hij hAddr).trans
          (hOrders.orderWord_eq j field (by simpa using hj) hfield)
  · intro j hj field hfield
    rw [Model.setQtyL_length] at hj
    exact hOrders.orderWord_bound j field hj hfield

theorem freshOrderArrayAt_replaceOrderStore
    (st : Store Unit) (ptr capacity : UInt64) (os : List OrderL) (i : Nat)
    (qty : UInt64)
    (hi : i < os.length)
    (hPtr48 : 48 ≤ ptr.toNat)
    (hAddr : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hFresh : FreshOrderArrayAt st ptr capacity) :
    FreshOrderArrayAt (replaceOrderStore st ptr i os[i]! qty) ptr
      capacity := by
  have hData (field : Nat) (hfield1 : 1 ≤ field)
      (hfield5 : field ≤ 5) :
      ptr.toNat ≤
        (UInt32.ofNat
          ((ptr.toNat + (i * 5 + field) * 8) % 4294967296)).toNat := by
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have h1 := FreshFixedArrayAt.write64_data
    (value := os[i]!.oid) hFresh hPtr48
    (hData 1 (by omega) (by omega))
  have h2 := FreshFixedArrayAt.write64_data
    (value := os[i]!.otrader) h1 hPtr48
    (hData 2 (by omega) (by omega))
  have h3 := FreshFixedArrayAt.write64_data
    (value := os[i]!.oside) h2 hPtr48
    (hData 3 (by omega) (by omega))
  have h4 := FreshFixedArrayAt.write64_data
    (value := os[i]!.oprice) h3 hPtr48
    (hData 4 (by omega) (by omega))
  have h5 := FreshFixedArrayAt.write64_data
    (value := qty) h4 hPtr48
    (hData 5 (by omega) (by omega))
  simpa only [replaceOrderStore] using h5

end Project.ClobMatchFuel.BookReplaceStore
